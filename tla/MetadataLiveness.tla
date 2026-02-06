--------------------------- MODULE MetadataLiveness ---------------------------
(*
 * TLA+ specification for liveness properties of ubiblk's lazy loading pipeline.
 *
 * Extends the safety model (MetadataDurability) with:
 *   - Frontend request objects with lifecycle states
 *   - Fairness constraints (Weak Fairness on pipeline actions)
 *   - Temporal liveness properties (P7, P8)
 *
 * P7 (Progress under success): If all I/O succeeds and the system is fair,
 *     every queued request eventually completes.
 *
 * P8 (Progress under failure): If retry budget exhausts, dependent requests
 *     eventually fail (no infinite waiting).
 *
 * We model a simplified version where:
 *   - Each request touches exactly one stripe (multi-stripe generalized later)
 *   - Crashes are bounded (MAX_CRASHES) to allow termination
 *   - Fairness is Weak Fairness on each composite pipeline action
 *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    NUM_STRIPES,     \* Number of stripes to model
    MAX_CRASHES,     \* Bound on crashes for model checking termination
    MAX_RETRIES,     \* MAX_FETCH_RETRIES per stripe (3 in code)
    NUM_REQUESTS     \* Number of frontend requests to model

Stripes  == 0 .. (NUM_STRIPES - 1)
Requests == 0 .. (NUM_REQUESTS - 1)

\* Fetch state values (matching shared_state.rs)
NotFetched == 0
Fetched    == 1
Failed     == 2
NoSource   == 3

\* Write state values
NotWritten == 0
Written    == 1

\* Pipeline stages
StageIdle          == "idle"
StageSourceRead    == "source_read"
StageTargetWrite   == "target_write"
StageTargetFlush   == "target_flush"
StageHandoff       == "handoff"
StageMetaWrite     == "meta_write"
StageMetaFlush     == "meta_flush"
StagePublish       == "publish"

\* Request states
ReqQueued    == "queued"
ReqCompleted == "completed"
ReqFailed    == "failed"

VARIABLES
    \* === Volatile state (lost on crash) ===
    fetchState,        \* stripe -> {NotFetched, Fetched, Failed, NoSource}
    writeState,        \* stripe -> {NotWritten, Written}
    pipelineStage,     \* stripe -> pipeline stage
    retryCount,        \* stripe -> retries so far
    metaFlusherQueue,  \* set of stripes pending metadata flush
    inMemoryMeta,      \* in-memory metadata: stripe -> {NotFetched, Fetched}

    \* === Durable state (survives crash) ===
    durableMeta,       \* on-disk metadata: stripe -> {NotFetched, Fetched}
    targetDurable,     \* stripe -> TRUE if data is durable

    \* === Model checking state ===
    crashCount,        \* crashes so far

    \* === Frontend request state ===
    reqState,          \* request -> {ReqQueued, ReqCompleted, ReqFailed}
    reqStripe          \* request -> stripe it depends on (fixed at init)

vars == <<fetchState, writeState, pipelineStage, retryCount,
          metaFlusherQueue, inMemoryMeta,
          durableMeta, targetDurable,
          crashCount, reqState, reqStripe>>

\* Helper: pipeline vars (everything except request state and crashCount)
pipeVars == <<fetchState, writeState, pipelineStage, retryCount,
              metaFlusherQueue, inMemoryMeta, durableMeta, targetDurable>>

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
    /\ reqState \in [Requests -> {ReqQueued, ReqCompleted, ReqFailed}]
    /\ reqStripe \in [Requests -> Stripes]

\* ============================================================================
\* Initial state
\* ============================================================================

\* Each request is assigned a stripe non-deterministically
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
    /\ reqState       = [r \in Requests |-> ReqQueued]
    /\ reqStripe      \in [Requests -> Stripes]

\* ============================================================================
\* Pipeline actions (same as MetadataDurability, plus UNCHANGED for new vars)
\* ============================================================================

StartSourceRead(s) ==
    /\ fetchState[s] = NotFetched
    /\ pipelineStage[s] = StageIdle
    /\ retryCount[s] < MAX_RETRIES
    /\ s \notin metaFlusherQueue
    /\ inMemoryMeta[s] = NotFetched
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageSourceRead]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, reqState, reqStripe>>

SourceReadComplete(s) ==
    /\ pipelineStage[s] = StageSourceRead
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageTargetWrite]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, reqState, reqStripe>>

SourceReadFail(s) ==
    /\ pipelineStage[s] = StageSourceRead
    /\ IF retryCount[s] + 1 >= MAX_RETRIES
       THEN
            /\ fetchState' = [fetchState EXCEPT ![s] = Failed]
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
       ELSE
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ UNCHANGED <<fetchState>>
    /\ UNCHANGED <<writeState, metaFlusherQueue, inMemoryMeta,
                   durableMeta, targetDurable, crashCount, reqState, reqStripe>>

TargetWriteComplete(s) ==
    /\ pipelineStage[s] = StageTargetWrite
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageTargetFlush]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, reqState, reqStripe>>

TargetWriteFail(s) ==
    /\ pipelineStage[s] = StageTargetWrite
    /\ IF retryCount[s] + 1 >= MAX_RETRIES
       THEN
            /\ fetchState' = [fetchState EXCEPT ![s] = Failed]
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
       ELSE
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ UNCHANGED <<fetchState>>
    /\ UNCHANGED <<writeState, metaFlusherQueue, inMemoryMeta,
                   durableMeta, targetDurable, crashCount, reqState, reqStripe>>

TargetFlushComplete(s) ==
    /\ pipelineStage[s] = StageTargetFlush
    /\ targetDurable' = [targetDurable EXCEPT ![s] = TRUE]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageHandoff]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta,
                   crashCount, reqState, reqStripe>>

TargetFlushFail(s) ==
    /\ pipelineStage[s] = StageTargetFlush
    /\ IF retryCount[s] + 1 >= MAX_RETRIES
       THEN
            /\ fetchState' = [fetchState EXCEPT ![s] = Failed]
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
       ELSE
            /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ UNCHANGED <<fetchState>>
    /\ UNCHANGED <<writeState, metaFlusherQueue, inMemoryMeta,
                   durableMeta, targetDurable, crashCount, reqState, reqStripe>>

Handoff(s) ==
    /\ pipelineStage[s] = StageHandoff
    /\ metaFlusherQueue' = metaFlusherQueue \union {s}
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<fetchState, writeState, retryCount,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, reqState, reqStripe>>

MetadataWriteStart(s) ==
    /\ s \in metaFlusherQueue
    /\ pipelineStage[s] = StageIdle
    /\ fetchState[s] /= Failed
    /\ inMemoryMeta' = [inMemoryMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageMetaWrite]
    /\ metaFlusherQueue' = metaFlusherQueue \ {s}
    /\ UNCHANGED <<fetchState, writeState, retryCount,
                   durableMeta, targetDurable,
                   crashCount, reqState, reqStripe>>

MetadataWriteComplete(s) ==
    /\ pipelineStage[s] = StageMetaWrite
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageMetaFlush]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, reqState, reqStripe>>

MetadataWriteFail(s) ==
    /\ pipelineStage[s] = StageMetaWrite
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, reqState, reqStripe>>

MetadataFlushComplete(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ durableMeta' = [durableMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StagePublish]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, targetDurable,
                   crashCount, reqState, reqStripe>>

MetadataFlushFail(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<fetchState, writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, reqState, reqStripe>>

AtomicPublish(s) ==
    /\ pipelineStage[s] = StagePublish
    /\ fetchState' = [fetchState EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<writeState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   crashCount, reqState, reqStripe>>

\* ============================================================================
\* Frontend actions: poll-driven request completion
\* ============================================================================

\* Frontend polls and completes a request whose stripe is now Fetched
FrontendComplete(r) ==
    /\ reqState[r] = ReqQueued
    /\ fetchState[reqStripe[r]] = Fetched
    /\ reqState' = [reqState EXCEPT ![r] = ReqCompleted]
    /\ UNCHANGED <<fetchState, writeState, pipelineStage, retryCount,
                   metaFlusherQueue, inMemoryMeta, durableMeta, targetDurable,
                   crashCount, reqStripe>>

\* Frontend polls and fails a request whose stripe has Failed
FrontendFail(r) ==
    /\ reqState[r] = ReqQueued
    /\ fetchState[reqStripe[r]] = Failed
    /\ reqState' = [reqState EXCEPT ![r] = ReqFailed]
    /\ UNCHANGED <<fetchState, writeState, pipelineStage, retryCount,
                   metaFlusherQueue, inMemoryMeta, durableMeta, targetDurable,
                   crashCount, reqStripe>>

\* ============================================================================
\* Crash and Recovery
\* ============================================================================

Crash ==
    /\ crashCount < MAX_CRASHES
    /\ crashCount' = crashCount + 1
    \* Recovery: re-derive volatile state from durable
    /\ fetchState' = [s \in Stripes |->
                        IF durableMeta[s] = Fetched THEN Fetched
                        ELSE NotFetched]
    /\ writeState' = [s \in Stripes |-> NotWritten]
    /\ pipelineStage' = [s \in Stripes |-> StageIdle]
    /\ retryCount' = [s \in Stripes |-> 0]
    /\ metaFlusherQueue' = {}
    /\ inMemoryMeta' = durableMeta
    /\ UNCHANGED <<durableMeta, targetDurable>>
    \* Requests: re-queue non-terminal requests (queued requests survive crash
    \* conceptually because they are re-submitted by the client)
    /\ reqState' = [r \in Requests |->
                      IF reqState[r] = ReqCompleted THEN ReqCompleted
                      ELSE IF reqState[r] = ReqFailed THEN ReqFailed
                      ELSE ReqQueued]
    /\ UNCHANGED <<reqStripe>>

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
    \/ \E r \in Requests :
        \/ FrontendComplete(r)
        \/ FrontendFail(r)

\* Success-only next: no failures, no crashes (for clean P7 verification)
NextSuccess ==
    \E s \in Stripes :
        \/ StartSourceRead(s)
        \/ SourceReadComplete(s)
        \/ TargetWriteComplete(s)
        \/ TargetFlushComplete(s)
        \/ Handoff(s)
        \/ MetadataWriteStart(s)
        \/ MetadataWriteComplete(s)
        \/ MetadataFlushComplete(s)
        \/ AtomicPublish(s)
    \/ \E r \in Requests :
        \/ FrontendComplete(r)
        \/ FrontendFail(r)

\* ============================================================================
\* Fairness constraints
\* ============================================================================

\* Weak Fairness on each pipeline action per stripe:
\* If an action is continuously enabled, it must eventually be taken.

PipelineFairness ==
    \A s \in Stripes :
        /\ WF_vars(StartSourceRead(s))
        /\ WF_vars(SourceReadComplete(s))
        /\ WF_vars(TargetWriteComplete(s))
        /\ WF_vars(TargetFlushComplete(s))
        /\ WF_vars(Handoff(s))
        /\ WF_vars(MetadataWriteStart(s))
        /\ WF_vars(MetadataWriteComplete(s))
        /\ WF_vars(MetadataFlushComplete(s))
        /\ WF_vars(AtomicPublish(s))

\* Fairness on frontend polling (requests are eventually processed)
FrontendFairness ==
    \A r \in Requests :
        /\ WF_vars(FrontendComplete(r))
        /\ WF_vars(FrontendFail(r))

\* ============================================================================
\* Spec variants
\* ============================================================================

\* Base spec (no fairness, for safety checking)
Spec == Init /\ [][Next]_vars

\* Liveness spec: pipeline fair (with all actions, including failures)
LiveSpec == Spec /\ PipelineFairness /\ FrontendFairness

\* Success-only liveness spec: only success actions, with fairness
SuccessSpec == Init /\ [][NextSuccess]_vars /\ PipelineFairness /\ FrontendFairness

\* ============================================================================
\* Safety Properties (carried over from MetadataDurability)
\* ============================================================================

DurabilityBeforeVisibility ==
    \A s \in Stripes :
        fetchState[s] = Fetched =>
            /\ durableMeta[s] = Fetched
            /\ targetDurable[s] = TRUE

NoStaleReadsAfterCrash ==
    \A s \in Stripes :
        (durableMeta[s] = Fetched) => targetDurable[s] = TRUE

\* ============================================================================
\* Liveness Properties
\* ============================================================================

\* P7: Progress under success
\* Under fair scheduling with no crashes and no I/O failures,
\* every queued request eventually reaches a terminal state (completed or failed).
\*
\* In the LiveSpec (with PipelineFairness), success actions are always enabled
\* once a stripe enters the pipeline. So with WF, the pipeline must progress
\* to completion. The frontend fairness then ensures the request is completed.
\*
\* We state this as: every request eventually leaves the queued state.
EventualCompletion ==
    \A r \in Requests :
        (reqState[r] = ReqQueued) ~> (reqState[r] \in {ReqCompleted, ReqFailed})

\* Stronger version: Under success (no failures enabled by the Spec variant),
\* every request eventually completes (not just terminates).
EventualSuccess ==
    \A r \in Requests :
        (reqState[r] = ReqQueued) ~> (reqState[r] = ReqCompleted)

\* P8: Progress under failure
\* If a stripe's retry count reaches MAX_RETRIES, it eventually becomes Failed,
\* and all requests depending on it eventually fail.
\*
\* The retry budget is enforced in the failure actions (SourceReadFail etc.)
\* which set fetchState[s] = Failed when retryCount[s] + 1 >= MAX_RETRIES.
\* With WF on FrontendFail, those requests then eventually fail.
FailureTerminates ==
    \A s \in Stripes :
        (fetchState[s] = Failed) ~>
            (\A r \in {r2 \in Requests : reqStripe[r2] = s} :
                reqState[r] \in {ReqFailed, ReqCompleted})

\* Combined: every request eventually terminates regardless of failures
AllRequestsTerminate ==
    \A r \in Requests :
        <>(reqState[r] \in {ReqCompleted, ReqFailed})

\* ============================================================================
\* Auxiliary: no-failure constraint for P7 success variant
\* ============================================================================

\* Action constraint: disable all failure actions (for testing P7 pure success path)
\* Used as an ACTION_CONSTRAINT in the config file
NoFailures ==
    /\ \A s \in Stripes :
        /\ pipelineStage'[s] /= StageIdle \/ pipelineStage[s] = StageIdle
              \/ pipelineStage[s] = StageHandoff
              \/ pipelineStage[s] = StagePublish
              \/ (s \in metaFlusherQueue /\ pipelineStage[s] = StageIdle)

\* Simpler: state constraint that failures never happen
NoFailureStates ==
    \A s \in Stripes : fetchState[s] /= Failed

\* No crashes constraint
NoCrashes ==
    crashCount = 0

\* Combined: no failures and no crashes
NoFailureNoCrash ==
    NoFailureStates /\ NoCrashes

\* ============================================================================
\* Deadlock freedom (supplementary)
\* ============================================================================

\* There's always some action enabled (system never gets stuck)
\* This is checked by TLC's built-in deadlock detection
\* But we can also express: if any request is queued, some action is enabled
NoRequestStarvation ==
    (\E r \in Requests : reqState[r] = ReqQueued) =>
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
        \/ \E r \in Requests :
            \/ FrontendComplete(r)
            \/ FrontendFail(r)
        \/ Crash

=============================================================================
