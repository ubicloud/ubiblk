--------------------------- MODULE StripeStateTransitions ---------------------------
(*
 * TLA+ model of ubiblk stripe state machine transitions.
 *
 * Models the SharedMetadataState atomic state transitions for fetch_state and
 * write_state, verifying monotonicity, terminal stability, and valid state
 * combinations.
 *
 * Source code modeled:
 *   shared_state.rs:81-95  - set_stripe_header, set_stripe_failed
 *   stripe_fetcher.rs:272-300 - fetch_completed
 *   bgworker.rs:64-65, 101-103 - process_request, take_finished_fetches
 *
 * Two modes:
 *   SINGLE_THREADED = TRUE  -> Only bgworker mutates state (actual code)
 *   SINGLE_THREADED = FALSE -> Multiple actors can mutate concurrently (hypothetical)
 *)
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Stripes,            \* Set of stripe IDs to model
    SINGLE_THREADED     \* TRUE = only bgworker mutates (actual), FALSE = concurrent

\* fetch_state values (matching shared_state.rs:16-19)
NotFetched == 0
Fetched    == 1
Failed     == 2
NoSource   == 3

\* write_state values (matching shared_state.rs:21-22)
NotWritten == 0
Written    == 1

VARIABLES
    fetch_state,        \* Function: stripe -> {NotFetched, Fetched, Failed, NoSource}
    write_state,        \* Function: stripe -> {NotWritten, Written}
    has_source,         \* Function: stripe -> BOOLEAN (immutable after init, models HAS_SOURCE flag)
    fetch_retries,      \* Function: stripe -> 0..MAX_RETRIES (retry count per stripe)
    bgworker_queue,     \* Sequence of pending operations for bgworker
    pc                  \* Process counter for bgworker (for single-threaded model)

vars == <<fetch_state, write_state, has_source, fetch_retries, bgworker_queue, pc>>

MAX_RETRIES == 3

\* Valid fetch states for a stripe
FetchStates == {NotFetched, Fetched, Failed, NoSource}
WriteStates == {NotWritten, Written}

\* ---- Valid successor states (monotonicity encoding) ----

ValidFetchSuccessors(state) ==
    CASE state = NotFetched -> {NotFetched, Fetched, Failed}
      [] state = Fetched    -> {Fetched}
      [] state = Failed     -> {Failed}
      [] state = NoSource   -> {NoSource}

ValidWriteSuccessors(state) ==
    CASE state = NotWritten -> {NotWritten, Written}
      [] state = Written    -> {Written}

\* ---- Initialization ----
\* Models SharedMetadataState::new() at shared_state.rs:25-53
\* Each stripe starts based on its has_source flag

Init ==
    \* has_source is nondeterministic (models different metadata configurations)
    /\ has_source \in [Stripes -> BOOLEAN]
    \* Initial fetch_state depends on has_source and whether already fetched
    \* We model all valid initial states:
    \*   HAS_SOURCE + not FETCHED -> NotFetched
    \*   HAS_SOURCE + FETCHED     -> Fetched (already fetched on load)
    \*   not HAS_SOURCE           -> NoSource
    /\ fetch_state \in [Stripes -> FetchStates]
    /\ \A s \in Stripes:
        \/ (has_source[s] /\ fetch_state[s] \in {NotFetched, Fetched})
        \/ (~has_source[s] /\ fetch_state[s] = NoSource)
    \* Initial write_state: either NotWritten or Written (from durable WRITTEN flag)
    /\ write_state \in [Stripes -> WriteStates]
    /\ fetch_retries = [s \in Stripes |-> 0]
    /\ bgworker_queue = <<>>
    /\ pc = "idle"

\* ---- Actions modeling code paths ----

\* Models stripe_fetcher fetch completing successfully, which eventually
\* leads to metadata_flusher calling set_stripe_header(stripe, FETCHED)
\* Code: stripe_fetcher.rs:281-285 -> bgworker.rs:101-103 ->
\*        metadata_flusher -> shared_state.rs:81-87
SetStripeFetched(s) ==
    /\ has_source[s]                    \* Can only fetch stripes with a source
    /\ fetch_state[s] = NotFetched      \* Only fetch if not already fetched
    \* Models set_stripe_header with FETCHED flag (shared_state.rs:82-87)
    \* Uses swap(Fetched, AcqRel) - unconditional write
    /\ fetch_state' = [fetch_state EXCEPT ![s] = Fetched]
    /\ UNCHANGED <<write_state, has_source, fetch_retries, bgworker_queue, pc>>

\* Models fetch failing after MAX_RETRIES
\* Code: stripe_fetcher.rs:294-299 -> shared_state.rs:93-95
SetStripeFailed(s) ==
    /\ has_source[s]                    \* Can only fail stripes with a source
    /\ fetch_state[s] = NotFetched      \* Only fail from NotFetched
    /\ fetch_retries[s] >= MAX_RETRIES  \* Only after max retries exhausted
    \* Models store(Failed, Release) at shared_state.rs:94
    /\ fetch_state' = [fetch_state EXCEPT ![s] = Failed]
    /\ UNCHANGED <<write_state, has_source, fetch_retries, bgworker_queue, pc>>

\* Models a failed fetch attempt incrementing retries
\* Code: stripe_fetcher.rs:288-293
FetchRetry(s) ==
    /\ has_source[s]
    /\ fetch_state[s] = NotFetched
    /\ fetch_retries[s] < MAX_RETRIES
    /\ fetch_retries' = [fetch_retries EXCEPT ![s] = @ + 1]
    /\ UNCHANGED <<fetch_state, write_state, has_source, bgworker_queue, pc>>

\* Models host write triggering SetWritten through bgworker
\* Code: device.rs:285-293 -> bgworker.rs:64-65 -> metadata_flusher ->
\*        shared_state.rs:88-90
SetStripeWritten(s) ==
    /\ write_state[s] = NotWritten      \* Only write if not already written
    \* Models store(Written, Release) at shared_state.rs:89
    /\ write_state' = [write_state EXCEPT ![s] = Written]
    /\ UNCHANGED <<fetch_state, has_source, fetch_retries, bgworker_queue, pc>>

\* ---- Concurrent model: allows direct mutation from any actor ----
\* This models what would happen WITHOUT the single-threaded bgworker guarantee

\* Unconditional swap to Fetched (what set_stripe_header actually does with swap)
\* This is the "raw" atomic operation without precondition guards
ConcurrentSetFetched(s) ==
    /\ ~SINGLE_THREADED
    /\ has_source[s]
    \* swap(Fetched, AcqRel) - writes Fetched regardless of current state
    /\ fetch_state' = [fetch_state EXCEPT ![s] = Fetched]
    /\ UNCHANGED <<write_state, has_source, fetch_retries, bgworker_queue, pc>>

\* Unconditional store to Failed (what set_stripe_failed actually does)
ConcurrentSetFailed(s) ==
    /\ ~SINGLE_THREADED
    /\ has_source[s]
    \* store(Failed, Release) - writes Failed regardless of current state
    /\ fetch_state' = [fetch_state EXCEPT ![s] = Failed]
    /\ UNCHANGED <<write_state, has_source, fetch_retries, bgworker_queue, pc>>

\* ---- Next state relation ----

Next ==
    \E s \in Stripes:
        \/ SetStripeFetched(s)
        \/ SetStripeFailed(s)
        \/ FetchRetry(s)
        \/ SetStripeWritten(s)
        \* Concurrent actions only enabled when SINGLE_THREADED = FALSE
        \/ ConcurrentSetFetched(s)
        \/ ConcurrentSetFailed(s)

\* Allow stuttering for liveness
Spec == Init /\ [][Next]_vars

\* ============================================================
\* PROPERTIES TO VERIFY
\* ============================================================

\* P-ST1: Monotonicity - states only advance forward, never regress
Monotonicity ==
    [][\A s \in Stripes:
        /\ fetch_state'[s] \in ValidFetchSuccessors(fetch_state[s])
        /\ write_state'[s] \in ValidWriteSuccessors(write_state[s])]_vars

\* P-ST2: Terminal states are stable
TerminalStatesStable ==
    [][\A s \in Stripes:
        (fetch_state[s] \in {Fetched, Failed, NoSource} =>
            fetch_state'[s] = fetch_state[s])]_vars

\* P-ST3: Failed is truly terminal
FailedIsTerminal ==
    [][\A s \in Stripes:
        (fetch_state[s] = Failed => fetch_state'[s] = Failed)]_vars

\* P-ST4: No invalid state combinations (invariant form - no temporal operator)
\* If NoSource, the stripe should not have HAS_SOURCE
ValidStateCombinations ==
    \A s \in Stripes:
        fetch_state[s] = NoSource => ~has_source[s]

\* P-ST5: Written is truly terminal
WrittenIsTerminal ==
    [][\A s \in Stripes:
        (write_state[s] = Written => write_state'[s] = Written)]_vars

\* P-ST6: Only source stripes can be fetched or fail (invariant form)
SourceConsistency ==
    \A s \in Stripes:
        ~has_source[s] => fetch_state[s] = NoSource

\* Type invariant
TypeOK ==
    /\ fetch_state \in [Stripes -> FetchStates]
    /\ write_state \in [Stripes -> WriteStates]
    /\ has_source \in [Stripes -> BOOLEAN]
    /\ \A s \in Stripes: fetch_retries[s] \in 0..MAX_RETRIES

=============================================================================
