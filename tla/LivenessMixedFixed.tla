--------------------------- MODULE LivenessMixedFixed ---------------------------
(*
 * Same as LivenessMixed but with the no-rollback bug FIXED.
 * MetadataWriteFail and MetadataFlushFail now reset inMemoryMeta[s]
 * back to NotFetched, allowing the stripe to be re-fetched.
 *
 * Expected: EventualTermination should now PASS.
 *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    NUM_STRIPES,
    MAX_RETRIES,
    NUM_REQUESTS,
    MAX_META_FAILURES

Stripes == 0 .. (NUM_STRIPES - 1)
RequestIds == 0 .. (NUM_REQUESTS - 1)

NotFetched == 0
Fetched    == 1
Failed     == 2

StageIdle          == "idle"
StageSourceRead    == "source_read"
StageTargetWrite   == "target_write"
StageTargetFlush   == "target_flush"
StageHandoff       == "handoff"
StageMetaWrite     == "meta_write"
StageMetaFlush     == "meta_flush"
StagePublish       == "publish"

ReqQueued    == "queued"
ReqCompleted == "completed"
ReqFailed    == "failed"

VARIABLES
    fetchState, pipelineStage, retryCount, metaFlusherQueue,
    inMemoryMeta, durableMeta, targetDurable,
    reqState, reqStripe, reqSubmitted,
    metaFailCount

pipelineVars == <<fetchState, pipelineStage, retryCount, metaFlusherQueue,
                  inMemoryMeta, durableMeta, targetDurable>>

reqVars == <<reqState, reqStripe, reqSubmitted>>

vars == <<fetchState, pipelineStage, retryCount, metaFlusherQueue,
          inMemoryMeta, durableMeta, targetDurable,
          reqState, reqStripe, reqSubmitted, metaFailCount>>

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

\* FIX: Roll back inMemoryMeta on metadata write failure
MetadataWriteFail(s) ==
    /\ pipelineStage[s] = StageMetaWrite
    /\ metaFailCount < MAX_META_FAILURES
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ inMemoryMeta' = [inMemoryMeta EXCEPT ![s] = NotFetched]  \* FIX: rollback
    /\ metaFailCount' = metaFailCount + 1
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   durableMeta, targetDurable, reqVars>>

MetadataFlushComplete(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ durableMeta' = [durableMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StagePublish]
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   inMemoryMeta, targetDurable,
                   reqVars, metaFailCount>>

\* FIX: Roll back inMemoryMeta on metadata flush failure
MetadataFlushFail(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ metaFailCount < MAX_META_FAILURES
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ inMemoryMeta' = [inMemoryMeta EXCEPT ![s] = NotFetched]  \* FIX: rollback
    /\ metaFailCount' = metaFailCount + 1
    /\ UNCHANGED <<fetchState, retryCount, metaFlusherQueue,
                   durableMeta, targetDurable, reqVars>>

AtomicPublish(s) ==
    /\ pipelineStage[s] = StagePublish
    /\ fetchState' = [fetchState EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<retryCount, metaFlusherQueue,
                   inMemoryMeta, durableMeta, targetDurable,
                   reqVars, metaFailCount>>

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

Next ==
    \/ \E s \in Stripes :
        \/ BgWorkerPipelineStep(s)
        \/ MetadataFlusherStep(s)
    \/ \E r \in RequestIds :
        FrontendStep(r)

Fairness ==
    /\ \A s \in Stripes :
        /\ WF_vars(BgWorkerPipelineStep(s))
        /\ WF_vars(MetadataFlusherStep(s))
    /\ \A r \in RequestIds :
        WF_vars(FrontendStep(r))

Spec == Init /\ [][Next]_vars /\ Fairness

DurabilityBeforeVisibility ==
    \A s \in Stripes :
        fetchState[s] = Fetched =>
            /\ durableMeta[s] = Fetched
            /\ targetDurable[s] = TRUE

EventualTermination ==
    \A r \in RequestIds :
        (r \in reqSubmitted /\ reqState[r] = ReqQueued)
            ~> (reqState[r] \in {ReqCompleted, ReqFailed})

NoStarvation ==
    \A r \in RequestIds :
        <>(reqState[r] \in {ReqCompleted, ReqFailed})

=============================================================================
