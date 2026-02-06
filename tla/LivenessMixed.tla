--------------------------- MODULE LivenessMixed ---------------------------
(*
 * TLA+ liveness specification with non-deterministic I/O success/failure.
 *
 * This model allows I/O operations to succeed or fail non-deterministically,
 * which is more realistic than the fixed ioSucceeds model. This enables
 * exploring the metadata no-rollback bug's impact on liveness.
 *
 * Key difference from LivenessSpec.tla:
 * - I/O success/failure is non-deterministic per operation, not fixed
 * - This means a stripe can fail metadata write, leaving inMemoryMeta
 *   stuck at Fetched (no-rollback bug), blocking re-fetch
 * - Tests whether EventualTermination holds despite mixed I/O outcomes
 *
 * Known bug modeled: MetadataWriteFail and MetadataFlushFail do NOT
 * reset inMemoryMeta. This prevents re-fetch of the stripe via
 * StartSourceRead (which guards on inMemoryMeta[s] = NotFetched).
 *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    NUM_STRIPES,
    MAX_RETRIES,
    NUM_REQUESTS,
    MAX_META_FAILURES  \* bound on metadata failures for termination

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
    fetchState,
    pipelineStage,
    retryCount,
    metaFlusherQueue,
    inMemoryMeta,
    durableMeta,
    targetDurable,
    reqState,
    reqStripe,
    reqSubmitted,
    metaFailCount    \* tracks metadata I/O failures for bounding

pipelineVars == <<fetchState, pipelineStage, retryCount, metaFlusherQueue,
                  inMemoryMeta, durableMeta, targetDurable>>

reqVars == <<reqState, reqStripe, reqSubmitted>>

vars == <<fetchState, pipelineStage, retryCount, metaFlusherQueue,
          inMemoryMeta, durableMeta, targetDurable,
          reqState, reqStripe, reqSubmitted, metaFailCount>>

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
    /\ metaFailCount \in 0..MAX_META_FAILURES

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
    /\ reqState       = [r \in RequestIds |-> ReqQueued]
    /\ reqStripe      \in [RequestIds -> Stripes]
    /\ reqSubmitted   = {}
    /\ metaFailCount  = 0

\* ============================================================================
\* Pipeline actions (I/O ops succeed non-deterministically)
\* Fetch pipeline: source_read, target_write, target_flush always succeed
\* (modeling "success" scenario for the data path)
\* Metadata path: may fail (to trigger no-rollback bug)
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
                   reqVars, metaFailCount>>

\* Data path always succeeds in this model
SourceReadComplete(s) ==
    /\ pipelineStage[s] = StageSourceRead
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageTargetWrite]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, metaFailCount>>

TargetWriteComplete(s) ==
    /\ pipelineStage[s] = StageTargetWrite
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageTargetFlush]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, metaFailCount>>

TargetFlushComplete(s) ==
    /\ pipelineStage[s] = StageTargetFlush
    /\ targetDurable' = [targetDurable EXCEPT ![s] = TRUE]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageHandoff]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta,
                   reqVars, metaFailCount>>

Handoff(s) ==
    /\ pipelineStage[s] = StageHandoff
    /\ metaFlusherQueue' = metaFlusherQueue \union {s}
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<fetchState, retryCount,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, metaFailCount>>

MetadataWriteStart(s) ==
    /\ s \in metaFlusherQueue
    /\ pipelineStage[s] = StageIdle
    /\ fetchState[s] /= Failed
    /\ inMemoryMeta' = [inMemoryMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageMetaWrite]
    /\ metaFlusherQueue' = metaFlusherQueue \ {s}
    /\ UNCHANGED <<fetchState, retryCount,
                   durableMeta, targetDurable,
                   reqVars, metaFailCount>>

MetadataWriteComplete(s) ==
    /\ pipelineStage[s] = StageMetaWrite
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageMetaFlush]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, metaFailCount>>

\* Metadata write fails: in-memory NOT rolled back (known bug)
MetadataWriteFail(s) ==
    /\ pipelineStage[s] = StageMetaWrite
    /\ metaFailCount < MAX_META_FAILURES
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ metaFailCount' = metaFailCount + 1
    \* BUG: inMemoryMeta[s] stays Fetched, blocking re-fetch via StartSourceRead
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars>>

MetadataFlushComplete(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ durableMeta' = [durableMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StagePublish]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, targetDurable,
                   reqVars, metaFailCount>>

\* Metadata flush fails: in-memory NOT rolled back (known bug)
MetadataFlushFail(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ metaFailCount < MAX_META_FAILURES
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ metaFailCount' = metaFailCount + 1
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars>>

AtomicPublish(s) ==
    /\ pipelineStage[s] = StagePublish
    /\ fetchState' = [fetchState EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, metaFailCount>>

\* ============================================================================
\* Frontend actions
\* ============================================================================

SubmitRequest(r) ==
    /\ r \notin reqSubmitted
    /\ reqState[r] = ReqQueued
    /\ reqSubmitted' = reqSubmitted \union {r}
    /\ UNCHANGED <<pipelineVars, reqState, reqStripe, metaFailCount>>

CompleteRequest(r) ==
    /\ r \in reqSubmitted
    /\ reqState[r] = ReqQueued
    /\ fetchState[reqStripe[r]] = Fetched
    /\ reqState' = [reqState EXCEPT ![r] = ReqCompleted]
    /\ UNCHANGED <<pipelineVars, reqStripe, reqSubmitted, metaFailCount>>

FailRequest(r) ==
    /\ r \in reqSubmitted
    /\ reqState[r] = ReqQueued
    /\ fetchState[reqStripe[r]] = Failed
    /\ reqState' = [reqState EXCEPT ![r] = ReqFailed]
    /\ UNCHANGED <<pipelineVars, reqStripe, reqSubmitted, metaFailCount>>

\* ============================================================================
\* Action groupings for fairness
\* ============================================================================

BgWorkerPipelineStep(s) ==
    \/ StartSourceRead(s)
    \/ SourceReadComplete(s)
    \/ TargetWriteComplete(s)
    \/ TargetFlushComplete(s)
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
\* Fairness
\* ============================================================================

Fairness ==
    /\ \A s \in Stripes :
        /\ WF_vars(BgWorkerPipelineStep(s))
        /\ WF_vars(MetadataFlusherStep(s))
    /\ \A r \in RequestIds :
        WF_vars(FrontendStep(r))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ============================================================================
\* Properties
\* ============================================================================

\* Safety
DurabilityBeforeVisibility ==
    \A s \in Stripes :
        fetchState[s] = Fetched =>
            /\ durableMeta[s] = Fetched
            /\ targetDurable[s] = TRUE

\* Liveness: every submitted request eventually terminates
\* This should FAIL if a metadata failure causes a stripe to get stuck
\* (the no-rollback bug means the stripe can't be re-fetched)
EventualTermination ==
    \A r \in RequestIds :
        (r \in reqSubmitted /\ reqState[r] = ReqQueued)
            ~> (reqState[r] \in {ReqCompleted, ReqFailed})

NoStarvation ==
    \A r \in RequestIds :
        <>(reqState[r] \in {ReqCompleted, ReqFailed})

\* Detect the stuck state: stripe with inMemoryMeta=Fetched but
\* fetchState=NotFetched and pipeline idle and not in queue
StripeStuck(s) ==
    /\ inMemoryMeta[s] = Fetched
    /\ fetchState[s] = NotFetched
    /\ pipelineStage[s] = StageIdle
    /\ s \notin metaFlusherQueue

\* Any stripe stuck means a liveness issue
NoStuckStripes ==
    \A s \in Stripes : ~StripeStuck(s)

=============================================================================
