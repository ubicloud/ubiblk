--------------------------- MODULE GuestFlushDurability ---------------------------
(*
 * TLA+ specification of ubiblk's guest flush durability guarantee (P5).
 *
 * Goal: Prove that after a guest flush (VIRTIO_BLK_T_FLUSH) completes
 * successfully, all preceding guest writes survive any subsequent crash.
 *
 * This extends the fetch pipeline model from MetadataDurability.tla with:
 *   - Guest writes (gated on Fetched/NoSource per INV-5)
 *   - Guest flush (IORING_OP_FSYNC on target device)
 *   - Per-stripe target device volatile write cache
 *   - NoSource stripes (no source image data, writable immediately)
 *   - Crash model: volatile state lost, durable state survives
 *   - Recovery: volatile state re-derived from durable metadata + hasSource
 *
 * Key insight: Guest writes can ONLY proceed after a stripe is Fetched or
 * NoSource (INV-5). Fetched is published ONLY after metadata is durable
 * (INV-1). NoSource means no source exists to re-fetch from. Therefore:
 *   - Fetched stripes: metadata durable, won't be re-fetched
 *   - NoSource stripes: nothing to re-fetch from, guest data preserved
 * In both cases, guest writes survive crashes after flush.
 *
 * The model tracks individual write "tokens" (write_id, stripe) to verify
 * that every write acknowledged before a completed flush is recoverable.
 *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    NUM_STRIPES,     \* Number of stripes (keep small: 2-3)
    MAX_CRASHES,     \* Bound on crashes for termination
    MAX_WRITES,      \* Max guest writes per session (bounds state space)
    MAX_FLUSHES      \* Max guest flushes per session

Stripes == 0 .. (NUM_STRIPES - 1)

\* Fetch state values (shared_state.rs:16-19)
NotFetched == 0
Fetched    == 1
Failed     == 2
NoSource   == 3

\* Pipeline stages (from MetadataDurability.tla)
StageIdle          == "idle"
StageSourceRead    == "source_read"
StageTargetWrite   == "target_write"
StageTargetFlush   == "target_flush"
StageHandoff       == "handoff"
StageMetaWrite     == "meta_write"
StageMetaFlush     == "meta_flush"
StagePublish       == "publish"

\* Guest flush states
FlushIdle       == "flush_idle"
FlushSubmitted  == "flush_submitted"
FlushComplete   == "flush_complete"

VARIABLES
    \* === Persistent configuration (survives crash) ===
    hasSource,          \* stripe -> BOOLEAN: does this stripe have source data?
                        \* Set at init, derived from source image, immutable.
                        \* In real code: HAS_SOURCE flag in metadata (shared_state.rs:41-42)

    \* === Volatile state (lost on crash) ===
    fetchState,         \* SharedMetadataState: stripe -> fetch state
    pipelineStage,      \* StripeFetcher internal: stripe -> pipeline stage
    metaFlusherQueue,   \* MetadataFlusher pending requests (set of stripes)
    inMemoryMeta,       \* In-memory metadata (may be ahead of durable)

    \* === Target device state ===
    \* Models the target device's volatile write cache and durable storage.
    \* Guest writes land in volatile cache first; flush makes them durable.
    targetVolatile,     \* stripe -> set of write IDs in volatile cache
    targetDurable,      \* stripe -> set of write IDs durable on media
    targetFetchDurable, \* stripe -> BOOLEAN: fetch data durable on target

    \* === Durable metadata ===
    durableMeta,        \* On-disk metadata: stripe -> {NotFetched, Fetched}

    \* === Guest I/O tracking ===
    guestWriteCount,    \* Counter: total guest writes issued this session
    guestFlushCount,    \* Counter: total guest flushes issued this session
    guestFlushState,    \* Current flush state: idle/submitted/complete
    writesBeforeFlush,  \* Set of write IDs issued before current/last flush
    ackedWrites,        \* Set of write IDs acknowledged to guest
    flushAcked,         \* BOOLEAN: most recent flush was acked

    \* === Model checking state ===
    crashCount,         \* Number of crashes so far
    crashed             \* BOOLEAN: crash has occurred (for property checking)

vars == <<hasSource, fetchState, pipelineStage, metaFlusherQueue, inMemoryMeta,
          targetVolatile, targetDurable, targetFetchDurable,
          durableMeta,
          guestWriteCount, guestFlushCount, guestFlushState,
          writesBeforeFlush, ackedWrites, flushAcked,
          crashCount, crashed>>

\* ============================================================================
\* Type invariant
\* ============================================================================

TypeOK ==
    /\ hasSource \in [Stripes -> BOOLEAN]
    /\ fetchState \in [Stripes -> {NotFetched, Fetched, Failed, NoSource}]
    /\ pipelineStage \in [Stripes -> {StageIdle, StageSourceRead, StageTargetWrite,
                                       StageTargetFlush, StageHandoff,
                                       StageMetaWrite, StageMetaFlush, StagePublish}]
    /\ metaFlusherQueue \subseteq Stripes
    /\ inMemoryMeta \in [Stripes -> {NotFetched, Fetched}]
    /\ \A s \in Stripes : targetVolatile[s] \subseteq (1..MAX_WRITES)
    /\ \A s \in Stripes : targetDurable[s] \subseteq (1..MAX_WRITES)
    /\ targetFetchDurable \in [Stripes -> BOOLEAN]
    /\ durableMeta \in [Stripes -> {NotFetched, Fetched}]
    /\ guestWriteCount \in 0..MAX_WRITES
    /\ guestFlushCount \in 0..MAX_FLUSHES
    /\ guestFlushState \in {FlushIdle, FlushSubmitted, FlushComplete}
    /\ writesBeforeFlush \subseteq (1..MAX_WRITES)
    /\ ackedWrites \subseteq (1..MAX_WRITES)
    /\ flushAcked \in BOOLEAN
    /\ crashCount \in 0..MAX_CRASHES
    /\ crashed \in BOOLEAN

\* ============================================================================
\* Initial state
\* ============================================================================

\* Recovery procedure: derive fetchState from durable metadata + hasSource.
\* Matches shared_state.rs:25-53
RecoverFetchState(s) ==
    IF durableMeta[s] = Fetched THEN Fetched
    ELSE IF ~hasSource[s] THEN NoSource
    ELSE NotFetched

Init ==
    \* hasSource is chosen non-deterministically to explore all configurations
    /\ hasSource \in [Stripes -> BOOLEAN]
    /\ fetchState       = [s \in Stripes |-> IF hasSource[s] THEN NotFetched ELSE NoSource]
    /\ pipelineStage    = [s \in Stripes |-> StageIdle]
    /\ metaFlusherQueue = {}
    /\ inMemoryMeta     = [s \in Stripes |-> NotFetched]
    /\ targetVolatile   = [s \in Stripes |-> {}]
    /\ targetDurable    = [s \in Stripes |-> {}]
    /\ targetFetchDurable = [s \in Stripes |-> FALSE]
    /\ durableMeta      = [s \in Stripes |-> NotFetched]
    /\ guestWriteCount  = 0
    /\ guestFlushCount  = 0
    /\ guestFlushState  = FlushIdle
    /\ writesBeforeFlush = {}
    /\ ackedWrites      = {}
    /\ flushAcked       = FALSE
    /\ crashCount       = 0
    /\ crashed          = FALSE

\* ============================================================================
\* Fetch pipeline actions (BgWorker thread)
\* Same 7-stage pipeline as MetadataDurability.tla, simplified
\* (no failure paths for clarity - focus is on P5)
\* ============================================================================

\* Stage 1: Start fetching a stripe from source
StartSourceRead(s) ==
    /\ hasSource[s] = TRUE            \* Only fetch stripes that have a source
    /\ fetchState[s] = NotFetched
    /\ pipelineStage[s] = StageIdle
    /\ s \notin metaFlusherQueue
    /\ inMemoryMeta[s] = NotFetched
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageSourceRead]
    /\ UNCHANGED <<hasSource, fetchState, metaFlusherQueue, inMemoryMeta,
                   targetVolatile, targetDurable, targetFetchDurable, durableMeta,
                   guestWriteCount, guestFlushCount, guestFlushState,
                   writesBeforeFlush, ackedWrites, flushAcked,
                   crashCount, crashed>>

\* Stage 1 completes -> Stage 2
SourceReadComplete(s) ==
    /\ pipelineStage[s] = StageSourceRead
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageTargetWrite]
    /\ UNCHANGED <<hasSource, fetchState, metaFlusherQueue, inMemoryMeta,
                   targetVolatile, targetDurable, targetFetchDurable, durableMeta,
                   guestWriteCount, guestFlushCount, guestFlushState,
                   writesBeforeFlush, ackedWrites, flushAcked,
                   crashCount, crashed>>

\* Stage 2 completes -> Stage 3 (target write done, data in device cache)
TargetWriteComplete(s) ==
    /\ pipelineStage[s] = StageTargetWrite
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageTargetFlush]
    /\ UNCHANGED <<hasSource, fetchState, metaFlusherQueue, inMemoryMeta,
                   targetVolatile, targetDurable, targetFetchDurable, durableMeta,
                   guestWriteCount, guestFlushCount, guestFlushState,
                   writesBeforeFlush, ackedWrites, flushAcked,
                   crashCount, crashed>>

\* Stage 3 completes -> Stage 4 (target flush done, fetch data DURABLE)
TargetFlushComplete(s) ==
    /\ pipelineStage[s] = StageTargetFlush
    /\ targetFetchDurable' = [targetFetchDurable EXCEPT ![s] = TRUE]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageHandoff]
    /\ UNCHANGED <<hasSource, fetchState, metaFlusherQueue, inMemoryMeta,
                   targetVolatile, targetDurable, durableMeta,
                   guestWriteCount, guestFlushCount, guestFlushState,
                   writesBeforeFlush, ackedWrites, flushAcked,
                   crashCount, crashed>>

\* Stage 4: Handoff to MetadataFlusher
Handoff(s) ==
    /\ pipelineStage[s] = StageHandoff
    /\ metaFlusherQueue' = metaFlusherQueue \union {s}
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<hasSource, fetchState, inMemoryMeta,
                   targetVolatile, targetDurable, targetFetchDurable, durableMeta,
                   guestWriteCount, guestFlushCount, guestFlushState,
                   writesBeforeFlush, ackedWrites, flushAcked,
                   crashCount, crashed>>

\* Stage 5: Metadata write start (updates in-memory copy, writes to device)
MetadataWriteStart(s) ==
    /\ s \in metaFlusherQueue
    /\ pipelineStage[s] = StageIdle
    /\ inMemoryMeta' = [inMemoryMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageMetaWrite]
    /\ metaFlusherQueue' = metaFlusherQueue \ {s}
    /\ UNCHANGED <<hasSource, fetchState,
                   targetVolatile, targetDurable, targetFetchDurable, durableMeta,
                   guestWriteCount, guestFlushCount, guestFlushState,
                   writesBeforeFlush, ackedWrites, flushAcked,
                   crashCount, crashed>>

\* Stage 5 completes -> Stage 6
MetadataWriteComplete(s) ==
    /\ pipelineStage[s] = StageMetaWrite
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageMetaFlush]
    /\ UNCHANGED <<hasSource, fetchState, metaFlusherQueue, inMemoryMeta,
                   targetVolatile, targetDurable, targetFetchDurable, durableMeta,
                   guestWriteCount, guestFlushCount, guestFlushState,
                   writesBeforeFlush, ackedWrites, flushAcked,
                   crashCount, crashed>>

\* Stage 6 completes -> Stage 7 (metadata DURABLE)
MetadataFlushComplete(s) ==
    /\ pipelineStage[s] = StageMetaFlush
    /\ durableMeta' = [durableMeta EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StagePublish]
    /\ UNCHANGED <<hasSource, fetchState, metaFlusherQueue, inMemoryMeta,
                   targetVolatile, targetDurable, targetFetchDurable,
                   guestWriteCount, guestFlushCount, guestFlushState,
                   writesBeforeFlush, ackedWrites, flushAcked,
                   crashCount, crashed>>

\* Stage 7: Atomic publish (SharedMetadataState := Fetched)
AtomicPublish(s) ==
    /\ pipelineStage[s] = StagePublish
    /\ fetchState' = [fetchState EXCEPT ![s] = Fetched]
    /\ pipelineStage' = [pipelineStage EXCEPT ![s] = StageIdle]
    /\ UNCHANGED <<hasSource, metaFlusherQueue, inMemoryMeta,
                   targetVolatile, targetDurable, targetFetchDurable, durableMeta,
                   guestWriteCount, guestFlushCount, guestFlushState,
                   writesBeforeFlush, ackedWrites, flushAcked,
                   crashCount, crashed>>

\* ============================================================================
\* Guest write action
\* ============================================================================

\* Guest writes to stripe s. Gated on Fetched or NoSource (INV-5).
\* In the real code: device.rs:259-266 checks request_stripes_fetch_status.
\* The write goes to base.add_write() which writes to target device.
\* The data lands in the target device's volatile write cache.
GuestWrite(s) ==
    /\ fetchState[s] \in {Fetched, NoSource}  \* INV-5: must be Fetched or NoSource
    /\ guestWriteCount < MAX_WRITES           \* Bound state space
    /\ guestFlushState = FlushIdle             \* Simplification: no writes during flush
    /\ LET wid == guestWriteCount + 1
       IN
        /\ guestWriteCount' = wid
        /\ targetVolatile' = [targetVolatile EXCEPT ![s] = targetVolatile[s] \union {wid}]
        /\ ackedWrites' = ackedWrites \union {wid}
        /\ UNCHANGED <<hasSource, fetchState, pipelineStage, metaFlusherQueue, inMemoryMeta,
                       targetDurable, targetFetchDurable, durableMeta,
                       guestFlushCount, guestFlushState,
                       writesBeforeFlush, flushAcked,
                       crashCount, crashed>>

\* ============================================================================
\* Guest flush actions
\* ============================================================================

\* Guest issues a flush. Records all acked writes as "before flush".
\* In the real code: device.rs:299-301 calls self.base.add_flush(id)
GuestFlushStart ==
    /\ guestFlushState = FlushIdle
    /\ guestFlushCount < MAX_FLUSHES
    /\ ackedWrites /= {}             \* Only flush if there are writes to flush
    /\ guestFlushState' = FlushSubmitted
    /\ writesBeforeFlush' = ackedWrites  \* Snapshot of all writes before this flush
    /\ flushAcked' = FALSE
    /\ UNCHANGED <<hasSource, fetchState, pipelineStage, metaFlusherQueue, inMemoryMeta,
                   targetVolatile, targetDurable, targetFetchDurable, durableMeta,
                   guestWriteCount, guestFlushCount,
                   ackedWrites,
                   crashCount, crashed>>

\* Guest flush completes: all volatile writes become durable on target.
\* In the real code: IORING_OP_FSYNC CQE received -> data durable.
\* The fsync applies to the ENTIRE target device fd, making all
\* pending writes durable (not just those for a specific stripe).
GuestFlushComplete ==
    /\ guestFlushState = FlushSubmitted
    /\ guestFlushState' = FlushComplete
    /\ guestFlushCount' = guestFlushCount + 1
    \* FSYNC makes ALL volatile writes durable across ALL stripes
    /\ targetDurable' = [s \in Stripes |-> targetDurable[s] \union targetVolatile[s]]
    /\ targetVolatile' = [s \in Stripes |-> {}]
    /\ flushAcked' = TRUE
    /\ UNCHANGED <<hasSource, fetchState, pipelineStage, metaFlusherQueue, inMemoryMeta,
                   targetFetchDurable, durableMeta,
                   guestWriteCount, writesBeforeFlush, ackedWrites,
                   crashCount, crashed>>

\* Reset flush state to allow more writes and flushes
GuestFlushReset ==
    /\ guestFlushState = FlushComplete
    /\ guestFlushState' = FlushIdle
    /\ UNCHANGED <<hasSource, fetchState, pipelineStage, metaFlusherQueue, inMemoryMeta,
                   targetVolatile, targetDurable, targetFetchDurable, durableMeta,
                   guestWriteCount, guestFlushCount,
                   writesBeforeFlush, ackedWrites, flushAcked,
                   crashCount, crashed>>

\* ============================================================================
\* Crash and Recovery
\* ============================================================================

\* Crash can occur at any time.
\* Volatile state is lost: SharedMetadataState, pipeline state, volatile writes.
\* Durable state survives: durableMeta, targetDurable, targetFetchDurable, hasSource.
\* Recovery: re-derive volatile state from durable metadata + hasSource.
Crash ==
    /\ crashCount < MAX_CRASHES
    /\ crashCount' = crashCount + 1
    /\ crashed' = TRUE
    \* Recovery: re-derive SharedMetadataState from durable metadata + hasSource
    \* (shared_state.rs:25-53)
    /\ fetchState' = [s \in Stripes |-> RecoverFetchState(s)]
    \* All volatile state reset
    /\ pipelineStage' = [s \in Stripes |-> StageIdle]
    /\ metaFlusherQueue' = {}
    /\ inMemoryMeta' = durableMeta
    \* Volatile write cache lost
    /\ targetVolatile' = [s \in Stripes |-> {}]
    \* Guest I/O state reset
    /\ guestWriteCount' = 0
    /\ guestFlushCount' = 0
    /\ guestFlushState' = FlushIdle
    /\ writesBeforeFlush' = writesBeforeFlush  \* Keep for property checking
    /\ ackedWrites' = {}
    /\ flushAcked' = flushAcked                \* Keep for property checking
    \* Durable state preserved
    /\ UNCHANGED <<hasSource, durableMeta, targetDurable, targetFetchDurable>>

\* ============================================================================
\* Next-state relation
\* ============================================================================

Next ==
    \/ Crash
    \/ GuestFlushStart
    \/ GuestFlushComplete
    \/ GuestFlushReset
    \/ \E s \in Stripes :
        \/ StartSourceRead(s)
        \/ SourceReadComplete(s)
        \/ TargetWriteComplete(s)
        \/ TargetFlushComplete(s)
        \/ Handoff(s)
        \/ MetadataWriteStart(s)
        \/ MetadataWriteComplete(s)
        \/ MetadataFlushComplete(s)
        \/ AtomicPublish(s)
        \/ GuestWrite(s)

Spec == Init /\ [][Next]_vars

\* ============================================================================
\* Safety Properties
\* ============================================================================

\* PROPERTY P5: Guest Flush Durability
\* After a guest flush is acked and a crash occurs, ALL writes that were
\* acknowledged before the flush must be recoverable (present in targetDurable).
\*
\* This is the critical durability guarantee for block devices.
\* write(data) -> flush() -> [crash] -> data is recoverable
GuestFlushDurability ==
    (flushAcked /\ crashed) =>
        \A wid \in writesBeforeFlush :
            \E s \in Stripes : wid \in targetDurable[s]

\* PROPERTY: Durability-Before-Visibility (from MetadataDurability.tla)
\* If fetchState shows Fetched, then metadata must be durable AND
\* fetch data must be durable on target.
DurabilityBeforeVisibility ==
    \A s \in Stripes :
        fetchState[s] = Fetched =>
            /\ durableMeta[s] = Fetched
            /\ targetFetchDurable[s] = TRUE

\* PROPERTY: Recovery Consistency
\* If durable metadata says Fetched, target fetch data must be durable.
\* This ensures no stale reads: if recovery says Fetched, the data is there.
RecoveryConsistency ==
    \A s \in Stripes :
        durableMeta[s] = Fetched => targetFetchDurable[s] = TRUE

\* PROPERTY: Write Gating Correctness
\* Guest writes can only happen to fetched or no-source stripes.
\* For Fetched stripes: metadata must already be durable (INV-1).
\*   Therefore on recovery, the stripe stays Fetched and is NOT re-fetched.
\* For NoSource stripes: no source to re-fetch from, so data is preserved.
\*
\* We check: if guest writes exist on a stripe, then either:
\*   (a) metadata says Fetched (so recovery won't re-fetch), or
\*   (b) stripe has no source (so nothing can overwrite it)
WriteGatingCorrectness ==
    \A s \in Stripes :
        (targetVolatile[s] /= {} \/ targetDurable[s] /= {}) =>
            \/ durableMeta[s] = Fetched
            \/ hasSource[s] = FALSE

\* Combined safety invariant
Safety ==
    /\ TypeOK
    /\ GuestFlushDurability
    /\ DurabilityBeforeVisibility
    /\ RecoveryConsistency
    /\ WriteGatingCorrectness

=============================================================================
