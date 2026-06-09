/* ###
 * IP: GHIDRA
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package ghidra.feature.vt.api.correlator.program;

import static ghidra.feature.vt.api.correlator.program.VTAbstractReferenceProgramCorrelatorFactory.*;

import java.util.*;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentHashMap;

import org.apache.commons.collections4.map.LazyMap;

import generic.DominantPair;
import generic.concurrent.ConcurrentQ;
import generic.concurrent.ConcurrentQBuilder;
import generic.concurrent.QCallback;
import generic.concurrent.QResult;
import generic.lsh.vector.LSHCosineVectorAccum;
import generic.lsh.vector.VectorCompare;
import ghidra.feature.vt.api.main.*;
import ghidra.feature.vt.api.util.VTAbstractProgramCorrelator;
import ghidra.framework.options.ToolOptions;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.listing.*;
import ghidra.program.model.symbol.*;
import ghidra.util.datastruct.Counter;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Abstract parent class for Version Tracking Reference Program Correlators.
 */
public abstract class VTAbstractReferenceProgramCorrelator extends VTAbstractProgramCorrelator {

	private static final int MAX_DEPTH = 30;
	private static final int TOP_N = 5;
	private static final double DIFFERENTIAL = 0.2;
	private static final double EQUALS_EPSILON = 0.00001;

	private static final Comparator<VTMatchInfo> SCORE_COMPARATOR = (o1, o2) -> {
		return o2.getSimilarityScore().compareTo(o1.getSimilarityScore());
	};

	private String correlatorName;
	private Map<Address, LSHCosineVectorAccum> srcVectorsByAddress;
	private Map<Address, LSHCosineVectorAccum> destVectorsByAddress;

	private Program sourceProgram;
	private Program destinationProgram;
	private Listing sourceListing;
	private Listing destinationListing;

	/**
	 * Correlator class constructor.
	 * @param sourceProgram the source program
	 * @param sourceAddressSet the source addresses to correlate
	 * @param destinationProgram the destination program
	 * @param destinationAddressSet the destination addresses to correlate
	 * @param correlatorName the correlator name
	 * @param options the tool options
	 */
	public VTAbstractReferenceProgramCorrelator(Program sourceProgram,
			AddressSetView sourceAddressSet, Program destinationProgram,
			AddressSetView destinationAddressSet, String correlatorName, ToolOptions options) {
		// Call the constructor for the parent class.
		super(sourceProgram, sourceAddressSet, destinationProgram, destinationAddressSet, options);
		this.correlatorName = correlatorName;

		this.sourceProgram = sourceProgram;
		this.destinationProgram = destinationProgram;

		this.sourceListing = sourceProgram.getListing();
		this.destinationListing = destinationProgram.getListing();
	}

	@Override
	public String getName() {
		return correlatorName;
	}

	/**
	 * First generates the sourceDictionary from the source program and matchSet,
	 * then finds the destinations corresponding to the matchSet and the
	 * sourceDictionary using the preset similarity and confidence thresholds.
	 *
	 * @param matchSet contains all existing matches
	 * @param monitor the task monitor
	 * @throws CancelledException if cancelled
	 */
	@Override
	protected void doCorrelate(VTMatchSet matchSet, TaskMonitor monitor) throws CancelledException {

		monitor.setMessage("Finding reference features");
		extractReferenceFeatures(matchSet, monitor);

		monitor.setMessage("Finding destination functions");
		findDestinations(matchSet, monitor);
	}

	/**
	 * findDestinations updates matchSet with non-null VTMatchInfo members returned from transform.
	 * For each of the entries in the destinationMap = {destMatchAddr:[list of source references]},
	 * we test all pairs [list of source references] x [list of destination references]
	 *
	 * </br>
	 * Note: {@code destinationMap} is a class variable set by {@code extractReferenceFeatures}
	 *
	 * @param matchSet The {@code VTMatchSet} for the current session (non-transitive)
	 * @param monitor task monitor
	 * @throws CancelledException if cancelled
	 */
	private void findDestinations(VTMatchSet matchSet, TaskMonitor monitor)
			throws CancelledException {

		monitor.initialize(destVectorsByAddress.size());

		// Pre-finalize all vectors single-threaded so the parallel compare phase is race-free.
		// LSHCosineVectorAccum.compare() lazily calls doFinalize() on BOTH operands, which mutates
		// the vector exactly once (rebuilds hash[], nulls treehash, sets finalized) and is then
		// idempotent. After finalization, compare() is a pure read of hash[] with only local
		// scratch state. Finalizing every source and destination vector here, before fan-out,
		// means the parallel compares mutate nothing and need no synchronization.
		for (LSHCosineVectorAccum v : srcVectorsByAddress.values()) {
			v.doFinalize();
		}
		for (LSHCosineVectorAccum v : destVectorsByAddress.values()) {
			v.doFinalize();
		}

		// PHASE P (parallel, pure vector math; no Program / matchSet access): for each destination
		// function, compute its positive-similarity source neighbors. Workers read only the two
		// finalized, read-only vector maps and per-pair-local VectorCompare objects, so no
		// synchronization is required. Results are accumulated into a ConcurrentHashMap keyed by
		// destination address (each destination is written by exactly one worker).
		List<Entry<Address, LSHCosineVectorAccum>> destList =
			new ArrayList<>(destVectorsByAddress.entrySet());
		Map<Address, Map<Address, DominantPair<Double, VectorCompare>>> neighborsByDest =
			new ConcurrentHashMap<>();

		QCallback<Entry<Address, LSHCosineVectorAccum>, Object> callback =
			(destEntry, taskMonitor) -> {
				LSHCosineVectorAccum dstVector = destEntry.getValue();

				// Get the set of possible matches, neighbors, in the SourceProgram
				Map<Address, DominantPair<Double, VectorCompare>> srcNeighbors = new HashMap<>();
				for (Entry<Address, LSHCosineVectorAccum> srcEntry : srcVectorsByAddress
						.entrySet()) {
					Address srcAddr = srcEntry.getKey();
					LSHCosineVectorAccum srcVector = srcEntry.getValue();

					VectorCompare vectorCompare = new VectorCompare();
					// Single compare per pair: the prior code compared twice (once for the score,
					// once again to gate on > 0). The stored VectorCompare is identical either way.
					double similarity = dstVector.compare(srcVector, vectorCompare);
					if (similarity > 0) {
						srcNeighbors.put(srcAddr,
							new DominantPair<>(similarity, vectorCompare));
					}
				}

				neighborsByDest.put(destEntry.getKey(), srcNeighbors);
				return null;
			};

		// Build a private thread pool by name (no AutoAnalysisManager in headless AutoVT). The
		// monitor is shared for cancellation only; progress is incremented serially in Phase C so
		// the parallel workers never touch monitor progress state.
		ConcurrentQ<Entry<Address, LSHCosineVectorAccum>, Object> queue =
			new ConcurrentQBuilder<Entry<Address, LSHCosineVectorAccum>, Object>()
					.setThreadPoolName("VT Reference Correlator")
					.setMonitor(monitor)
					.setCollectResults(true)
					.build(callback);
		try {
			queue.add(destList);
			Collection<QResult<Entry<Address, LSHCosineVectorAccum>, Object>> results =
				queue.waitForResults();
			// Surface any worker exception, mirroring DecompilerConcurrentQ's handling: unwrap a
			// CancelledException and rethrow it, otherwise wrap as a RuntimeException.
			for (QResult<Entry<Address, LSHCosineVectorAccum>, Object> result : results) {
				result.getResult();
			}
		}
		catch (InterruptedException e) {
			throw new CancelledException();
		}
		catch (CancelledException e) {
			throw e;
		}
		catch (Exception e) {
			throw new RuntimeException("Unexpected exception scoring reference vectors", e);
		}
		finally {
			queue.dispose();
		}

		// PHASE C (serial, deterministic): commit in sorted destination-address order. All Program
		// and matchSet access happens here on a single thread, preserving the original behavior.
		// matchSet.addMatch writes the session DB under a lock and must stay serial. Sorting by
		// address makes the committed order deterministic (an improvement over HashMap iteration
		// order).
		List<Address> destAddrs = new ArrayList<>(neighborsByDest.keySet());
		Collections.sort(destAddrs);
		for (Address destAddr : destAddrs) {

			monitor.checkCancelled();
			monitor.incrementProgress(1);

			// Get the function containing the ACCEPTED match destination address
			Function destFunc = destinationListing.getFunctionAt(destAddr);
			LSHCosineVectorAccum dstVector = destVectorsByAddress.get(destAddr);
			Map<Address, DominantPair<Double, VectorCompare>> srcNeighbors =
				neighborsByDest.get(destAddr);

			List<VTMatchInfo> members =
				transform(matchSet, destFunc, dstVector, srcNeighbors, monitor);

			for (VTMatchInfo member : members) {
				if (member != null) {
					matchSet.addMatch(member);
				}
			}
		}

	}

	/**
	 * Scoring Mechanism: determines destination similarity and confidence for each of the
	 * sourceNeighbors and if similarity and confidence pass the threshold, then VTMatchInfo will
	 * be created and added to the result.
	 *
	 * @param matchSet match set for this correlator
	 * @param destinationFunction function in the destination program that references an existing accepted match
	 * @param destinationVector the destination function's feature vector
	 * @param neighbors the set data for possible sourceFunction matches for destinationFunction
	 * @param monitor the monitor
	 * @return {@code List<VTMatchInfo>} result
	 * @throws CancelledException if cancelled
	 */
	private List<VTMatchInfo> transform(VTMatchSet matchSet, Function destinationFunction,
			LSHCosineVectorAccum destinationVector,
			Map<Address, DominantPair<Double, VectorCompare>> neighbors, TaskMonitor monitor)
			throws CancelledException {

		boolean refineResult = getOptions().getBoolean(REFINE_RESULTS, REFINE_RESULTS_DEFAULT);
		double confidenceThreshold =
			getOptions().getDouble(CONFIDENCE_THRESHOLD, CONFIDENCE_THRESHOLD_DEFAULT);
		double similarityThreshold =
			getOptions().getDouble(SIMILARITY_THRESHOLD, SIMILARITY_THRESHOLD_DEFAULT);

		Address destinationAddress = destinationFunction.getEntryPoint();
		int destinationLength = (int) destinationFunction.getBody().getNumAddresses();
		List<VTMatchInfo> result = new ArrayList<>();

		for (Entry<Address, DominantPair<Double, VectorCompare>> neighbor : neighbors.entrySet()) {
			monitor.checkCancelled();

			Address sourceAddr = neighbor.getKey();

			/* compare using LSHCosineVector.compare function
			 * --> similarity is the normalized dot product of the two vectors
			 */
			double similarity = neighbor.getValue().first;
			VectorCompare veccompare = neighbor.getValue().second;
			veccompare.fillOut();

			double confidence = veccompare.dotproduct;

			if (similarity < similarityThreshold || Double.isNaN(similarity)) {
				continue;
			}

			if (confidence < confidenceThreshold) {
				continue;
			}

			confidence *= 10.0; // remove when getting rid of log10 stuff

			VTMatchInfo match = new VTMatchInfo(matchSet);

			Function sourceFunction = sourceListing.getFunctionAt(sourceAddr);
			Address sourceAddress = sourceFunction.getEntryPoint();
			int sourceLength = (int) sourceFunction.getBody().getNumAddresses();
			match.setSimilarityScore(new VTScore(similarity));
			match.setConfidenceScore(new VTScore(confidence));
			match.setSourceLength(sourceLength);
			match.setDestinationLength(destinationLength);
			match.setSourceAddress(sourceAddress);
			match.setDestinationAddress(destinationAddress);
			match.setTag(null);
			match.setAssociationType(VTAssociationType.FUNCTION);
			result.add(match);
		}

		if (refineResult) {
			result = refine(result);
		}
		return result;
	}

	private List<VTMatchInfo> refine(List<VTMatchInfo> list) {

		Collections.sort(list, SCORE_COMPARATOR);

		// take the top N + 1 (to catch duplicates across the N boundary)
		int topN = Math.min(TOP_N + 1, list.size());
		list = list.subList(0, topN);

		// remove things that are "very equal"
		if (list.size() > 1) {
			double previousScore = list.get(0).getSimilarityScore().getScore();
			int cutoffIndex = 1;
			for (int i = 1; i < list.size(); ++i) {
				double currentScore = list.get(i).getSimilarityScore().getScore();
				if (currentScore > previousScore - EQUALS_EPSILON) {
					--cutoffIndex;
					break;
				}
				++cutoffIndex;
				previousScore = currentScore;
			}
			list = list.subList(0, cutoffIndex);
		}

		// take the top N
		topN = Math.min(TOP_N, list.size());
		list = list.subList(0, topN);

		// remove things more than differential score from previous
		if (list.size() > 1) {
			double bestScore = list.get(0).getSimilarityScore().getScore();
			int cutoffIndex = list.size();
			for (int i = 1; i < list.size(); ++i) {
				if (list.get(i).getSimilarityScore().getScore() < bestScore - DIFFERENTIAL) {
					cutoffIndex = i;
					break;
				}
			}
			list = list.subList(0, cutoffIndex);
		}
		return list;
	}

	/**
	 * Recursively traces the reference chains from a given address and returns by reference a
	 * list of functions found along the reference chain.
	 *
	 * @param depth the initial recursion depth
	 * @param list a function accumulation list that is updated by this function
	 * @param program the program
	 * @param address an address represents a location in a program
	 */
	private void accumulateFunctionReferences(int depth, Set<Function> list, Program program,
			Address address) {

		if (depth >= MAX_DEPTH) {
			return;
		}

		/*
		 * If address corresponds to a Thunk Function, in addition to following back references,
		 * you should collect back-thunk-addresses (not included in references) by using the
		 * method Function.getFunctionThunkAddresses (Elf programs can have thunks which do
		 * not have a forward reference but thunk another function).  You may also need to dedup
		 * your list of functions returned if this could cause fallout.  In addition, you may
		 * need to watch out for recursion loops which could occur (i.e., a function pointer which
		 * has a secondary reference to itself - contrived example).
		 */

		FunctionManager functionManager = program.getFunctionManager();
		Function addressFunction = functionManager.getFunctionAt(address);
		if (addressFunction != null) {
			Address[] thunkAddresses = addressFunction.getFunctionThunkAddresses();
			if (thunkAddresses != null) {
				for (Address thunkAddress : thunkAddresses) {
					accumulateFunctionReferences(depth + 1, list, program, thunkAddress);
				}
			}
		}

		// Handle References to the address
		if (address.isStackAddress() || address.isRegisterAddress()) {
			return; // can't have references to these types of addresses
		}

		ReferenceManager refManager = program.getReferenceManager();
		Listing listing = program.getListing();
		ReferenceIterator it = refManager.getReferencesTo(address);
		while (it.hasNext()) {
			Reference reference = it.next();
			Address fromAddress = reference.getFromAddress();
			CodeUnit codeUnit = listing.getCodeUnitAt(fromAddress);

			// if the code unit at the location of the reference is an Instruction, then get the
			// function where the reference occurs and determine if it passes the basic VT function
			// match test set above
			if (codeUnit instanceof Instruction) {
				Function function = functionManager.getFunctionContaining(fromAddress);
				if (function == null) {
					continue;
				}

				if (function.isThunk()) {
					// also add references to the thunk function
					Address entryPoint = function.getEntryPoint();
					accumulateFunctionReferences(depth + 1, list, program, entryPoint);
				}
				else {
					list.add(function);
				}
			}
			else if (codeUnit instanceof Data) {
				accumulateFunctionReferences(depth + 1, list, program, fromAddress);
			}
		}
	}

	/**
	 * Used to check that a match association is of the correct type (e.g. DATA or FUNCTION) for
	 * the given correlator.
	 *
	 * @param associationType the type of match
	 * @return true if the correct type
	 */
	protected abstract boolean isExpectedRefType(VTAssociationType associationType);

	/**
	 * Used to check that a match association is of the correct type (e.g. DATA or FUNCTION) for
	 * the given correlator.
	 *
	 * @param ref the reference
	 * @return true if the correct type
	 */
	protected abstract boolean isExpectedRefType(Reference ref);

	/**
	 * extractReferenceFeatures is the core of the reference algorithm.  Each accepted match
	 * becomes a unique feature. At the end, all the source and destination functions will have
	 * "vectors" of these features, which are unique match ids.  Then the LSH dictionary can be
	 * made from the source and we can look for matches in the destination.
	 *
	 * @param matchSet the match set of previously user-accepted matches
	 * @param monitor the monitor
	 */
	private void extractReferenceFeatures(VTMatchSet matchSet, TaskMonitor monitor)
			throws CancelledException {

		srcVectorsByAddress = LazyMap.lazyMap(new HashMap<>(), addr -> new LSHCosineVectorAccum());
		destVectorsByAddress = LazyMap.lazyMap(new HashMap<>(), addr -> new LSHCosineVectorAccum());

		FunctionManager srcFuncManager = sourceProgram.getFunctionManager();
		FunctionManager destFuncManager = destinationProgram.getFunctionManager();
		int srcFunctionCount = srcFuncManager.getFunctionCount();
		int destFunctionCount = destFuncManager.getFunctionCount();

		Counter totalMatches = new Counter();
		Collection<VTMatchSet> matchSets = getMatchSets(matchSet.getSession(), totalMatches);
		monitor.initialize(totalMatches.count());

		// Loop through the matchSets in order to get total source and destination reference
		// counts that pass the filter
		Map<VTMatch, Set<Function>> sourceRefMap = new HashMap<>();
		Map<VTMatch, Set<Function>> destinationRefMap = new HashMap<>();

		for (VTMatchSet ms : matchSets) {
			Collection<VTMatch> matches = ms.getMatches();
			for (VTMatch match : matches) {

				monitor.checkCancelled();
				monitor.incrementProgress(1);

				accumulateMatchFunctionReferences(sourceRefMap, destinationRefMap, match);
			}
		}

		monitor.setMessage("Adding ACCEPTED matches to feature vectors.");
		int featureID = 1;

		// score each match that passed the filter above
		for (VTMatch match : sourceRefMap.keySet()) {

			monitor.checkCancelled();
			monitor.incrementProgress(1);

			if (sourceRefMap.get(match).isEmpty()) {
				continue;
			}

			/**
			 * Compute raw percentages for the sources and destination counts as ratios
			 * (total references to the match):(total number of references of the correct type)
			 */

			// Compute entropy of the system for the given match
			Set<Function> srcRefFuncs = new HashSet<>(sourceRefMap.get(match));
			Set<Function> destRefFuncs = new HashSet<>(destinationRefMap.get(match));

			// take the average probability that the feature appears in any one function (in either
			// source or dest)
			double altPraw = (double) (srcRefFuncs.size() + destRefFuncs.size()) /
				(srcFunctionCount + destFunctionCount);
			double weight = Math.sqrt(-Math.log(altPraw));

			// By the construction above, there may be duplicate functions in the RefMaps
			for (Function function : sourceRefMap.get(match)) {
				LSHCosineVectorAccum vector = srcVectorsByAddress.get(function.getEntryPoint());
				vector.addHash(featureID, weight);
			}

			for (Function function : destinationRefMap.get(match)) {
				LSHCosineVectorAccum vector = destVectorsByAddress.get(function.getEntryPoint());
				vector.addHash(featureID, weight);
			}

			++featureID;
		}

		updateSourceAndDestinationVectors(featureID, srcFuncManager, destFuncManager, monitor);
	}

	private Collection<VTMatchSet> getMatchSets(VTSession session, Counter totalMatches) {

		Map<String, VTMatchSet> dedupedMatchSets = new HashMap<>();
		for (VTMatchSet ms : session.getMatchSets()) {
			String name = ms.getProgramCorrelatorInfo().getName();

			// odd checks here: 1) assuming we do not want to include our own results when checking
			// matches; 2) why keep only the newest match set data?  seems like we should take all
			// matches and dedup the matches, not the match sets
			if (name.equals(correlatorName) || (dedupedMatchSets.containsKey(name) &&
				ms.getID() < dedupedMatchSets.get(name).getID())) {
				continue;
			}

			dedupedMatchSets.put(name, ms);
			totalMatches.add(ms.getMatchCount());
		}

		return dedupedMatchSets.values();

	}

	private void accumulateMatchFunctionReferences(Map<VTMatch, Set<Function>> sourceRefMap,
			Map<VTMatch, Set<Function>> destinationRefMap, VTMatch match) {

		// check match association type and status
		VTAssociation association = match.getAssociation();
		Address sourceAddress = association.getSourceAddress();
		Address destinationAddress = association.getDestinationAddress();

		if (!isExpectedRefType(association.getType())) {
			return;
		}

		if (association.getStatus() != VTAssociationStatus.ACCEPTED) {
			return;
		}

		Set<Function> sourceReferences = new HashSet<>();
		accumulateFunctionReferences(0, sourceReferences, sourceProgram, sourceAddress);

		// If either of the reference lists is empty, skip adding them to the map
		if (sourceReferences.isEmpty()) {
			return;
		}

		Set<Function> destinationReferences = new HashSet<>();
		accumulateFunctionReferences(0, destinationReferences, destinationProgram,
			destinationAddress);

		// If either of the reference lists is empty, skip adding them to the map
		if (destinationReferences.isEmpty()) {
			return;
		}

		// Fill Hashtable for use in next loop
		sourceRefMap.put(match, sourceReferences);
		destinationRefMap.put(match, destinationReferences);
	}

	private void updateSourceAndDestinationVectors(int featureID, FunctionManager srcFuncManager,
			FunctionManager destFuncManager, TaskMonitor monitor) {

		/*
		 * At this point the vectors in the sourceMap and the destinationMap contain log weights for
		 * the probability that ACCEPTED MATCHED features appear in any one function in the system.
		 * Each map has the key:value pair = refFunction:featureVector.
		 * In order to account unmatched/unaccepted matches that appear in the key set that
		 * consists of possibly correlated functions, we can consider the cost of a reference
		 * switching and the cost of a reference being dropped or picked up between versions.
		 *
		 * Theoretically this should be dependent on the probability of the referenced element
		 * occurring, but for the moment we'll consider the model for a generalized switch and
		 * drop/pickup.
		 */
		monitor.setMessage("Adding unmatched references to feature vectors.");

		double pSwitch = 0.5;
		double uniqueWeight = Math.sqrt(-Math.log(pSwitch)); //arbitrary weight used to provide negative correlation

		for (Address addr : srcVectorsByAddress.keySet()) {

			int totalRefs = countFunctionRefs(sourceProgram, addr);
			LSHCosineVectorAccum srcVector = srcVectorsByAddress.get(addr);
			int numEntries = srcVector.numEntries();
			for (int i = 0; i < (totalRefs - numEntries); i++) {
				srcVector.addHash(featureID, uniqueWeight);
				++featureID;
			}
		}

		for (Address addr : destVectorsByAddress.keySet()) {

			int totalRefs = countFunctionRefs(destinationProgram, addr);
			LSHCosineVectorAccum dstVector = destVectorsByAddress.get(addr);
			int numEntries = dstVector.numEntries();
			for (int i = 0; i < (totalRefs - numEntries); i++) {
				dstVector.addHash(featureID, uniqueWeight);
				++featureID;
			}
		}
	}

	private int countFunctionRefs(Program program, Address addr) {
		Function f = program.getFunctionManager().getFunctionAt(addr);
		CodeUnitIterator it = program.getListing().getCodeUnits(f.getBody(), true);
		int totalRefs = 0;
		while (it.hasNext()) {
			CodeUnit cu = it.next();
			Reference[] memRefs = cu.getReferencesFrom();

			for (Reference memRef : memRefs) {
				if (isExpectedRefType(memRef)) {
					++totalRefs;
				}
			}
		}
		return totalRefs;
	}
}
