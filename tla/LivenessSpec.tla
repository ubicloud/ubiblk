--------------------------- MODULE LivenessSpec ---------------------------
(*
 * TLA+ specification for liveness properties of ubiblk's fetch pipeline.
 *
 * Extends the MetadataDurability safety model with:
 *   - Frontend request model (queued requests depending on stripe states)
 *   - Fairness constraints on BgWorker/MetadataFlusher actions
 *   - P7: Progress under success (queued requests eventually complete)
 *   - P8: Progress under failure (retry exhaustion -> requests eventually fail)
 *
 * This spec does NOT model crashes (crashes reset everything and are covered
 * by the safety spec). Liveness is about within-session progress.
 *
 * Actors:
 *   - BgWorker: drives the 7-stage fetch pipeline
 *   - MetadataFlusher: write -> flush -> publish
 *   - Frontend: submits requests, polls for completion
 *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    NUM_STRIPES,     \* Number of stripes (keep small: 2)
    MAX_RETRIES,     \* Retry budget per stripe (3 in real code)
    NUM_REQUESTS     \* Number of frontend requests to model

Stripes == 0 .. (NUM_STRIPES - 1)
RequestIds == 0 .. (NUM_REQUESTS - 1)

\* Fetch state values
NotFetched == 0
Fetched    == 1
Failed     == 2

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
    \* === Pipeline state (BgWorker) ===
    fetchState,        \* stripe -> {NotFetched, Fetched, Failed}
    pipelineStage,     \* stripe -> pipeline stage
    retryCount,        \* stripe -> number of retries
    metaFlusherQueue,  \* set of stripes waiting for metadata flush
    inMemoryMeta,      \* stripe -> {NotFetched, Fetched}

    \* === Durable state ===
    durableMeta,       \* stripe -> {NotFetched, Fetched}
    targetDurable,     \* stripe -> BOOLEAN

    \* === Frontend request state ===
    reqState,          \* request -> {ReqQueued, ReqCompleted, ReqFailed}
    reqStripe,         \* request -> stripe it depends on (single-stripe for simplicity)
    reqSubmitted,      \* set of request IDs that have been submitted

    \* === Control: whether I/O operations succeed or fail ===
    ioSucceeds         \* BOOLEAN: when TRUE, all I/O succeeds (for P7 scenario)

pipelineVars == <<fetchState, pipelineStage, retryCount, metaFlusherQueue,
                  inMemoryMeta, durableMeta, targetDurable>>

reqVars == <<reqState, reqStripe, reqSubmitted>>

vars == <<fetchState, pipelineStage, retryCount, metaFlusherQueue,
          inMemoryMeta, durableMeta, targetDurable,
          reqState, reqStripe, reqSubmitted, ioSucceeds>>

\* ============================================================================
\* Type invariant
\* ============================================================================

TypeOK ==
    /\ fetchState \in [Stripes -> {NotFetched, Fetched, Failed}]
    /\ pipelineStage \in [Stripes -> {StageIdle, StageSourceRead, StageTargetWrite,
                                       StageTargetFlush, StageHandoff,
                                       StageMetaWrite, StageMetaFlush, StagePublish}]
    /\ retryCount \in [Stripes -> 0..MAX_RETRIES]
    /\ metaFlusherQueue \subseteq Stripes
    /\ inMemoryMeta \in [Stripes -> {NotFetched, Fetched}]
    /\ durableMeta \in [Stripes -> {NotFetched, Fetched}]
    /\ targetDurable \in [Stripes -> BOOLEAN]
    /\ reqState \in [RequestIds -> {ReqQueued, ReqCompleted, ReqFailed}]
    /\ reqStripe \in [RequestIds -> Stripes]
    /\ reqSubmitted \subseteq RequestIds
    /\ ioSucceeds \in BOOLEAN

\* ============================================================================
\* Initial state
\* ============================================================================

Init ==
    /\ fetchState     = [s \in Stripes |-> NotFetched]
    /\ pipelineStage  = [s \in Stripes |-> StageIdle]
    /\ retryCount     = [s \in Stripes |-> 0]
    /\ metaFlusherQueue = {}
    /\ inMemoryMeta   = [s \in Stripes |-> NotFetched]
    /\ durableMeta    = [s \in Stripes |-> NotFetched]
    /\ targetDurable  = [s \in Stripes |-> FALSE]
    \* All requests start as queued, each assigned to a stripe non-deterministically
    /\ reqState       = [r \in RequestIds |-> ReqQueued]
    /\ reqStripe      \in [RequestIds -> Stripes]
    /\ reqSubmitted   = {}
    /\ ioSucceeds     \in BOOLEAN  \* non-deterministic: fixed for the run

\* ============================================================================
\* Helper: is a stripe in the pipeline (not idle)?
\* ============================================================================

StripeInPipeline(s) ==
    pipelineStage[s] /= StageIdle

\* ============================================================================
\* Pipeline actions (same as MetadataDurability.tla but without crash model)
\* ============================================================================

StartSourceRead(s) ==
    /\ fetchState[s] = NotFetched
    /\ pipelineStage[s] = StageIdle
    /\ retryCount[s] < MAX_RETRIES
    /\ s \notin metaFlusherQueue
    /\ inMemoryMeta[s] = NotFetched
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageSourceRead]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

SourceReadComplete(s) ==
    /\ pipelineStage[s] = StageSourceRead
    /\ ioSucceeds
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageTargetWrite]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

SourceReadFail(s) ==
    /\ pipelineStage[s] = StageSourceRead
    /\ ~ioSucceeds
    /\ IF retryCount[s] + 1 >= MAX_RETRIES
       THEN
            /\ fetchState' = [fetchState EXCEPT ![s] = Failed]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
       ELSE
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ UNCHANGED fetchState
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<metaFlusherQueue, inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

TargetWriteComplete(s) ==
    /\ pipelineStage[s] = StageTargetWrite
    /\ ioSucceeds
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageTargetFlush]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

TargetWriteFail(s) ==
    /\ pipelineStage[s] = StageTargetWrite
    /\ ~ioSucceeds
    /\ IF retryCount[s] + 1 >= MAX_RETRIES
       THEN
            /\ fetchState' = [fetchState EXCEPT ![s] = Failed]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
       ELSE
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ UNCHANGED fetchState
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<metaFlusherQueue, inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

TargetFlushComplete(s) ==
    /\ pipelineStage[s] = StageTargetFlush
    /\ ioSucceeds
    /\ targetDurable' = [targetDurable EXCEPT ![s] = TRUE]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageHandoff]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta,
                   reqVars, ioSucceeds>>

TargetFlushFail(s) ==
    /\ pipelineStage[s] = StageTargetFlush
    /\ ~ioSucceeds
    /\ IF retryCount[s] + 1 >= MAX_RETRIES
       THEN
            /\ fetchState' = [fetchState EXCEPT ![s] = Failed]
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
       ELSE
            /\ retryCount' = [retryCount EXCEPT ![s] = retryCount[s] + 1]
            /\ UNCHANGED fetchState
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<metaFlusherQueue, inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

Handoff(s) ==
    /\ pipelineStage[s] = StageHandoff
    /\ metaFlusherQueue' = metaFlusherQueue \union {s}
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<fetchState, retryCount,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

MetadataWriteStart(s) ==
    /\ s \in metaFlusherQueue
    /\ pipelineStage[s] = StageIdle
    /\ fetchState[s] /= Failed
    /\ inMemoryMeta' = [inMemoryMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageMetaWrite]
    /\ metaFlusherQueue' = metaFlusherQueue \ {s}
    /\ UNCHANGED <<fetchState, retryCount,
                   durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

MetadataWriteComplete(s) ==
    /\ pipelineStage[s] = StageMetaWrite
    /\ ioSucceeds
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageMetaFlush]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

\* Known bug: in-memory metadata NOT rolled back on failure
MetadataWriteFail(s) ==
    /\ pipelineStage[s] = StageMetaWrite
    /\ ~ioSucceeds
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

MetadataFlushComplete(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ ioSucceeds
    /\ durableMeta' = [durableMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StagePublish]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, targetDurable,
                   reqVars, ioSucceeds>>

MetadataFlushFail(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ ~ioSucceeds
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

AtomicPublish(s) ==
    /\ pipelineStage[s] = StagePublish
    /\ fetchState' = [fetchState EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, ioSucceeds>>

\* ============================================================================
\* Frontend actions
\* ============================================================================

\* Submit a request: triggers a fetch for its stripe
SubmitRequest(r) ==
    /\ r \notin reqSubmitted
    /\ reqState[r] = ReqQueued
    /\ reqSubmitted' = reqSubmitted \union {r}
    /\ UNCHANGED <<pipelineVars, reqState, reqStripe, ioSucceeds>>

\* Frontend polls and discovers a completed stripe -> request completes
\* Models process_queued_rw_requests: check fetchState -> Complete -> dispatch
CompleteRequest(r) ==
    /\ r \in reqSubmitted
    /\ reqState[r] = ReqQueued
    /\ fetchState[reqStripe[r]] = Fetched
    /\ reqState' = [reqState EXCEPT ![r] = ReqCompleted]
    /\ UNCHANGED <<pipelineVars, reqStripe, reqSubmitted, ioSucceeds>>

\* Frontend polls and discovers a failed stripe -> request fails
\* Models process_queued_rw_requests: check fetchState -> Failed -> pop & fail
FailRequest(r) ==
    /\ r \in reqSubmitted
    /\ reqState[r] = ReqQueued
    /\ fetchState[reqStripe[r]] = Failed
    /\ reqState' = [reqState EXCEPT ![r] = ReqFailed]
    /\ UNCHANGED <<pipelineVars, reqStripe, reqSubmitted, ioSucceeds>>

\* ============================================================================
\* Combined pipeline step (for fairness constraint grouping)
\* ============================================================================

\* A single BgWorker pipeline step for a stripe
BgWorkerPipelineStep(s) ==
    \/ StartSourceRead(s)
    \/ SourceReadComplete(s)
    \/ SourceReadFail(s)
    \/ TargetWriteComplete(s)
    \/ TargetWriteFail(s)
    \/ TargetFlushComplete(s)
    \/ TargetFlushFail(s)
    \/ Handoff(s)

MetadataFlusherStep(s) ==
    \/ MetadataWriteStart(s)
    \/ MetadataWriteComplete(s)
    \/ MetadataWriteFail(s)
    \/ MetadataFlushComplete(s)
    \/ MetadataFlushFail(s)
    \/ AtomicPublish(s)

FrontendStep(r) ==
    \/ SubmitRequest(r)
    \/ CompleteRequest(r)
    \/ FailRequest(r)

\* ============================================================================
\* Next-state relation
\* ============================================================================

Next ==
    \/ \E s \in Stripes :
        \/ BgWorkerPipelineStep(s)
        \/ MetadataFlusherStep(s)
    \/ \E r \in RequestIds :
        FrontendStep(r)

\* ============================================================================
\* Fairness constraints
\* ============================================================================

\* Weak fairness: if an action is continuously enabled, it eventually happens.
\* This models:
\* - BgWorker's run() loop continuously calling update()
\* - Frontend continuously calling poll()
\* - I/O operations eventually completing (no infinite hang)

Fairness ==
    /\ \A s \in Stripes :
        /\ WF_vars(BgWorkerPipelineStep(s))
        /\ WF_vars(MetadataFlusherStep(s))
    /\ \A r \in RequestIds :
        WF_vars(FrontendStep(r))

\* ============================================================================
\* Specification
\* ============================================================================

Spec == Init /\ [][Next]_vars /\ Fairness

\* ============================================================================
\* Safety Properties (carried forward)
\* ============================================================================

DurabilityBeforeVisibility ==
    \A s \in Stripes :
        fetchState[s] = Fetched =>
            /\ durableMeta[s] = Fetched
            /\ targetDurable[s] = TRUE

\* ============================================================================
\* Liveness Properties
\* ============================================================================

\* P7: Progress under success
\* If I/O always succeeds and a request is queued, it eventually completes.
\* Expressed as: for all requests, if ioSucceeds is true and the request is
\* queued and submitted, then eventually the request is completed.
ProgressUnderSuccess ==
    \A r \in RequestIds :
        (ioSucceeds /\ reqState[r] = ReqQueued /\ r \in reqSubmitted)
            ~> (reqState[r] = ReqCompleted)

\* P8: Progress under failure
\* If I/O always fails (retry budget will be exhausted), then queued requests
\* eventually fail (no infinite waiting).
ProgressUnderFailure ==
    \A r \in RequestIds :
        (~ioSucceeds /\ reqState[r] = ReqQueued /\ r \in reqSubmitted)
            ~> (reqState[r] = ReqFailed)

\* Combined: every submitted request eventually terminates (completes or fails)
EventualTermination ==
    \A r \in RequestIds :
        (r \in reqSubmitted /\ reqState[r] = ReqQueued)
            ~> (reqState[r] \in {ReqCompleted, ReqFailed})

\* All requests are eventually submitted (weak: fairness on SubmitRequest)
EventualSubmission ==
    \A r \in RequestIds :
        <>(r \in reqSubmitted)

\* No starvation: every request eventually reaches a terminal state
NoStarvation ==
    \A r \in RequestIds :
        <>(reqState[r] \in {ReqCompleted, ReqFailed})

=============================================================================
