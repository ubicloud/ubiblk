--------------------------- MODULE MetadataDurability ---------------------------
(*
 * TLA+ specification of ubiblk's metadata durability-before-visibility protocol.
 *
 * Models the 7-stage fetch-to-publish pipeline:
 *   source_read -> target_write -> target_flush -> handoff ->
 *   metadata_write -> metadata_flush -> atomic_publish
 *
 * Actors:
 *   - BgWorker: single-threaded fetch coordinator (drives the pipeline)
 *   - MetadataFlusher: write -> flush -> publish sequence
 *   - SharedMetadataState: atomic state transitions (volatile)
 *   - DurableMetadata: on-disk metadata (survives crash)
 *   - TargetDevice: stripe data storage (durable after flush)
 *   - Frontend: concurrent readers of SharedMetadataState
 *   - Crash: non-deterministic system crash at any point
 *
 * Properties verified:
 *   1. DurabilityBeforeVisibility: Fetched in SharedMetadataState => metadata flushed
 *   2. NoStaleReadsAfterCrash: recovery loads only durable metadata
 *   3. Monotonicity: state only advances forward
 *   4. FailedIsTerminal: no transitions out of Failed state
 *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    NUM_STRIPES,     \* Number of stripes to model (keep small for checking)
    MAX_CRASHES,     \* Bound on crashes for model checking termination
    MAX_RETRIES      \* MAX_FETCH_RETRIES per stripe (3 in code)

Stripes == 0 .. (NUM_STRIPES - 1)

\* Fetch state values (matching shared_state.rs:16-19)
NotFetched == 0
Fetched    == 1
Failed     == 2
NoSource   == 3

\* Write state values (matching shared_state.rs:21-22)
NotWritten == 0
Written    == 1

\* Pipeline stage for each stripe being fetched (stripe_fetcher internal state)
\* These are the 7 stages from the durability-ordering findings
StageIdle          == "idle"
StageSourceRead    == "source_read"
StageTargetWrite   == "target_write"
StageTargetFlush   == "target_flush"
StageHandoff       == "handoff"
StageMetaWrite     == "meta_write"
StageMetaFlush     == "meta_flush"
StagePublish       == "publish"

VARIABLES
    \* === Volatile state (lost on crash) ===
    fetchState,        \* SharedMetadataState: stripe -> {NotFetched, Fetched, Failed, NoSource}
    writeState,        \* SharedMetadataState: stripe -> {NotWritten, Written}
    pipelineStage,     \* StripeFetcher internal: stripe -> pipeline stage
    retryCount,        \* StripeFetcher: stripe -> number of retries so far
    metaFlusherQueue,  \* MetadataFlusher pending requests (set of stripes)
    inMemoryMeta,      \* In-memory copy of metadata (may be ahead of durable)

    \* === Durable state (survives crash) ===
    durableMeta,       \* On-disk metadata: stripe -> {NotFetched, Fetched}
    targetDurable,     \* Target device: stripe -> TRUE if data is durable

    \* === Model checking state ===
    crashCount,        \* Number of crashes so far
    frontendObserved,  \* Set of (stripe, state) pairs the frontend has observed
    prevFetchState     \* For monotonicity checking: previous fetch state per stripe

vars == <<fetchState, writeState, pipelineStage, retryCount,
          metaFlusherQueue, inMemoryMeta,
          durableMeta, targetDurable,
          crashCount, frontendObserved, prevFetchState>>

\* ============================================================================
\* Type invariant
\* ============================================================================

TypeOK ==
    /\ fetchState \in [Stripes -> {NotFetched, Fetched, Failed, NoSource}]
    /\ writeState \in [Stripes -> {NotWritten, Written}]
    /\ pipelineStage \in [Stripes -> {StageIdle, StageSourceRead, StageTargetWrite,
                                       StageTargetFlush, StageHandoff,
                                       StageMetaWrite, StageMetaFlush, StagePublish}]
    /\ retryCount \in [Stripes -> 0..MAX_RETRIES]
    /\ metaFlusherQueue \subseteq Stripes
    /\ inMemoryMeta \in [Stripes -> {NotFetched, Fetched}]
    /\ durableMeta \in [Stripes -> {NotFetched, Fetched}]
    /\ targetDurable \in [Stripes -> BOOLEAN]
    /\ crashCount \in 0..MAX_CRASHES
    /\ frontendObserved \subseteq (Stripes \X {NotFetched, Fetched, Failed, NoSource})
    /\ prevFetchState \in [Stripes -> {NotFetched, Fetched, Failed, NoSource}]

\* ============================================================================
\* Initial state
\* ============================================================================

Init ==
    /\ fetchState     = [s \in Stripes |-> NotFetched]
    /\ writeState     = [s \in Stripes |-> NotWritten]
    /\ pipelineStage  = [s \in Stripes |-> StageIdle]
    /\ retryCount     = [s \in Stripes |-> 0]
    /\ metaFlusherQueue = {}
    /\ inMemoryMeta   = [s \in Stripes |-> NotFetched]
    /\ durableMeta    = [s \in Stripes |-> NotFetched]
    /\ targetDurable  = [s \in Stripes |-> FALSE]
    /\ crashCount     = 0
    /\ frontendObserved = {}
    /\ prevFetchState = [s \in Stripes |-> NotFetched]

\* ============================================================================
\* Pipeline actions (BgWorker thread drives these sequentially)
\* ============================================================================

\* Stage 1: Start fetching a stripe from source
\* Guards: stripe must be idle, not fetched, not in metadata flusher pipeline,
\* and not at max retries. In the real code, stripe_fetcher's internal
\* stripe_states HashMap prevents re-fetching stripes already in the pipeline.
StartSourceRead(s) ==
    /\ fetchState[s] = NotFetched
    /\ pipelineStage[s] = StageIdle
    /\ retryCount[s] < MAX_RETRIES
    /\ s \notin metaFlusherQueue                \* not waiting for metadata flush
    /\ inMemoryMeta[s] = NotFetched             \* not already processed by metadata flusher
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageSourceRead]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, frontendObserved, prevFetchState>>

\* Stage 1 completes: source read succeeds
SourceReadComplete(s) ==
    /\ pipelineStage[s] = StageSourceRead
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageTargetWrite]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, frontendObserved, prevFetchState>>

\* Stage 1 fails: source read error -> retry or fail
SourceReadFail(s) ==
    /\ pipelineStage[s] = StageSourceRead
    /\ IF retryCount[s] + 1 >= MAX_RETRIES
       THEN
            /\ fetchState' = [fetchState EXCEPT ![s] = Failed]
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ prevFetchState' = [prevFetchState EXCEPT ![s] = fetchState[s]]
       ELSE
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ UNCHANGED <<fetchState, prevFetchState>>
    /\ UNCHANGED <<writeState, metaFlusherQueue, inMemoryMeta,
                   durableMeta, targetDurable, crashCount, frontendObserved>>

\* Stage 2 completes: target write succeeded (data in device cache)
TargetWriteComplete(s) ==
    /\ pipelineStage[s] = StageTargetWrite
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageTargetFlush]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, frontendObserved, prevFetchState>>

\* Stage 2 fails: target write error -> retry or fail
TargetWriteFail(s) ==
    /\ pipelineStage[s] = StageTargetWrite
    /\ IF retryCount[s] + 1 >= MAX_RETRIES
       THEN
            /\ fetchState' = [fetchState EXCEPT ![s] = Failed]
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ prevFetchState' = [prevFetchState EXCEPT ![s] = fetchState[s]]
       ELSE
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ UNCHANGED <<fetchState, prevFetchState>>
    /\ UNCHANGED <<writeState, metaFlusherQueue, inMemoryMeta,
                   durableMeta, targetDurable, crashCount, frontendObserved>>

\* Stage 3 completes: target flush -> stripe data DURABLE on target
TargetFlushComplete(s) ==
    /\ pipelineStage[s] = StageTargetFlush
    /\ targetDurable' = [targetDurable EXCEPT ![s] = TRUE]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageHandoff]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta,
                   crashCount, frontendObserved, prevFetchState>>

\* Stage 3 fails: target flush error -> retry or fail
TargetFlushFail(s) ==
    /\ pipelineStage[s] = StageTargetFlush
    /\ IF retryCount[s] + 1 >= MAX_RETRIES
       THEN
            /\ fetchState' = [fetchState EXCEPT ![s] = Failed]
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ prevFetchState' = [prevFetchState EXCEPT ![s] = fetchState[s]]
       ELSE
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ UNCHANGED <<fetchState, prevFetchState>>
    /\ UNCHANGED <<writeState, metaFlusherQueue, inMemoryMeta,
                   durableMeta, targetDurable, crashCount, frontendObserved>>

\* Stage 4: Handoff from StripeFetcher to MetadataFlusher
Handoff(s) ==
    /\ pipelineStage[s] = StageHandoff
    /\ metaFlusherQueue' = metaFlusherQueue \union {s}
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<fetchState, writeState, retryCount,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, frontendObserved, prevFetchState>>

\* Stage 5: Metadata write starts
\* Updates in-memory metadata FIRST (line 168), then writes to device
\* Guard: stripe must not have been Failed (can't happen in real code due to
\* single-threaded BgWorker, but we guard explicitly for model safety)
MetadataWriteStart(s) ==
    /\ s \in metaFlusherQueue
    /\ pipelineStage[s] = StageIdle
    /\ fetchState[s] /= Failed
    /\ inMemoryMeta' = [inMemoryMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageMetaWrite]
    /\ metaFlusherQueue' = metaFlusherQueue \ {s}
    /\ UNCHANGED <<fetchState, writeState, retryCount,
                   durableMeta, targetDurable,
                   crashCount, frontendObserved, prevFetchState>>

\* Stage 5 completes: metadata write succeeded (in device cache)
MetadataWriteComplete(s) ==
    /\ pipelineStage[s] = StageMetaWrite
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageMetaFlush]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, frontendObserved, prevFetchState>>

\* Stage 5 fails: metadata write error
\* BUG: in-memory metadata NOT rolled back (known issue)
MetadataWriteFail(s) ==
    /\ pipelineStage[s] = StageMetaWrite
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, frontendObserved, prevFetchState>>

\* Stage 6 completes: metadata flush -> metadata DURABLE
MetadataFlushComplete(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ durableMeta' = [durableMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StagePublish]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, targetDurable,
                   crashCount, frontendObserved, prevFetchState>>

\* Stage 6 fails: metadata flush error
MetadataFlushFail(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, frontendObserved, prevFetchState>>

\* Stage 7: Atomic publish to SharedMetadataState
\* shared_state.rs:81-91 - swap(Fetched, AcqRel)
AtomicPublish(s) ==
    /\ pipelineStage[s] = StagePublish
    /\ prevFetchState' = [prevFetchState EXCEPT ![s] = fetchState[s]]
    /\ fetchState' = [fetchState EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, frontendObserved>>

\* ============================================================================
\* Frontend action: read SharedMetadataState
\* ============================================================================

FrontendRead(s) ==
    /\ frontendObserved' = frontendObserved \union {<<s, fetchState[s]>>}
    /\ UNCHANGED <<fetchState, writeState, pipelineStage, retryCount,
                   metaFlusherQueue, inMemoryMeta, durableMeta, targetDurable,
                   crashCount, prevFetchState>>

\* ============================================================================
\* Crash and Recovery
\* ============================================================================

Crash ==
    /\ crashCount < MAX_CRASHES
    /\ crashCount' = crashCount + 1
    \* Recovery: re-derive volatile from durable (shared_state.rs:25-53)
    /\ fetchState' = [s \in Stripes |->
                        IF durableMeta[s] = Fetched THEN Fetched
                        ELSE NotFetched]
    /\ writeState' = [s \in Stripes |-> NotWritten]
    /\ pipelineStage' = [s \in Stripes |-> StageIdle]
    /\ retryCount' = [s \in Stripes |-> 0]
    /\ metaFlusherQueue' = {}
    /\ inMemoryMeta' = durableMeta
    /\ UNCHANGED <<durableMeta, targetDurable>>
    /\ frontendObserved' = {}
    /\ prevFetchState' = [s \in Stripes |->
                            IF durableMeta[s] = Fetched THEN Fetched
                            ELSE NotFetched]

\* ============================================================================
\* Next-state relation
\* ============================================================================

Next ==
    \/ Crash
    \/ \E s \in Stripes :
        \/ StartSourceRead(s)
        \/ SourceReadComplete(s)
        \/ SourceReadFail(s)
        \/ TargetWriteComplete(s)
        \/ TargetWriteFail(s)
        \/ TargetFlushComplete(s)
        \/ TargetFlushFail(s)
        \/ Handoff(s)
        \/ MetadataWriteStart(s)
        \/ MetadataWriteComplete(s)
        \/ MetadataWriteFail(s)
        \/ MetadataFlushComplete(s)
        \/ MetadataFlushFail(s)
        \/ AtomicPublish(s)
        \/ FrontendRead(s)

Spec == Init /\ [][Next]_vars

\* ============================================================================
\* Safety Properties
\* ============================================================================

\* PROPERTY 1: Durability-Before-Visibility
\* If SharedMetadataState shows Fetched, then metadata is durable AND target data is durable
DurabilityBeforeVisibility ==
    \A s \in Stripes :
        fetchState[s] = Fetched =>
            /\ durableMeta[s] = Fetched
            /\ targetDurable[s] = TRUE

\* PROPERTY 2: No Stale Reads After Crash
\* If durable metadata says Fetched, then target data must be durable
NoStaleReadsAfterCrash ==
    \A s \in Stripes :
        (durableMeta[s] = Fetched) => targetDurable[s] = TRUE

\* PROPERTY 3: Monotonicity (within a session)
\* prevFetchState tracks the previous value; only forward transitions allowed
Monotonicity ==
    \A s \in Stripes :
        LET prev == prevFetchState[s]
            curr == fetchState[s]
        IN
        \/ prev = curr
        \/ prev = NotFetched /\ curr = Fetched
        \/ prev = NotFetched /\ curr = Failed

\* PROPERTY 4: Failed Is Terminal (within a session)
FailedIsTerminal ==
    \A s \in Stripes :
        prevFetchState[s] = Failed => fetchState[s] = Failed

\* Combined safety invariant
Safety ==
    /\ TypeOK
    /\ DurabilityBeforeVisibility
    /\ NoStaleReadsAfterCrash
    /\ Monotonicity
    /\ FailedIsTerminal

=============================================================================
