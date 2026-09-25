//! Which stripes are in a slot, and who is using them.
//!
//! One lock over everything. Channels take it once to admit a request and once
//! to finish it; the worker takes it to publish a transition. Nothing inside it
//! does I/O, allocates, or sends.

use std::sync::Arc;

use crate::utils::spin_lock::SpinLock;

pub type SlotId = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StripeState {
    Absent,
    Loading { attempt: u64 },
    Resident { slot: SlotId },
    Evicting { slot: SlotId },
    Failed { slot: Option<SlotId> },
}

#[derive(Clone, Debug)]
pub struct Stripe {
    pub state: StripeState,
    /// Requests admitted and not yet finished, including those waiting.
    pub active_requests: u32,
    pub last_accessed: u64,
    /// Written since it was loaded, so evicting it needs an upload.
    pub dirty: bool,
    pub next_attempt: u64,
    pub last_failed_attempt: Option<u64>,
}

pub struct SpillMetadata {
    pub access_sequence: u64,
    pub stripes: Vec<Stripe>,
}

/// What a request does next.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision {
    /// Run against this slot; the request's count keeps the stripe there.
    Ready { slot: SlotId },
    /// Wait. `fetch` is the attempt this request started, if it started one,
    /// and the caller has to ask the worker for it.
    Wait { fetch: Option<u64> },
    /// Fail the request. Its count is already released.
    Fail,
}

#[derive(Clone)]
pub struct SpillSharedMetadata {
    inner: Arc<SpinLock<SpillMetadata>>,
}

impl SpillSharedMetadata {
    pub fn new(stripe_count: usize) -> Self {
        let stripe = Stripe {
            state: StripeState::Absent,
            active_requests: 0,
            last_accessed: 0,
            dirty: false,
            next_attempt: 1,
            last_failed_attempt: None,
        };
        SpillSharedMetadata {
            inner: Arc::new(SpinLock::new(SpillMetadata {
                access_sequence: 0,
                stripes: vec![stripe; stripe_count],
            })),
        }
    }

    pub fn stripe_count(&self) -> usize {
        self.inner.lock().stripes.len()
    }

    pub fn get(&self, stripe: usize) -> Stripe {
        self.inner.lock().stripes[stripe].clone()
    }

    /// Admit a request from the frontend. It counts against the stripe from
    /// here until `finish`, or until a `Fail` decision.
    pub fn admit(&self, stripe: usize, joined: &mut Option<u64>) -> Decision {
        let mut metadata = self.inner.lock();
        metadata.access_sequence = metadata
            .access_sequence
            .checked_add(1)
            .expect("access sequence overflow");
        let accessed = metadata.access_sequence;
        let entry = &mut metadata.stripes[stripe];
        entry.active_requests = entry
            .active_requests
            .checked_add(1)
            .expect("active request count overflow");
        entry.last_accessed = accessed;
        Self::decide(entry, joined)
    }

    /// Look again at a waiting request, which is already counted.
    pub fn retry(&self, stripe: usize, joined: &mut Option<u64>) -> Decision {
        let mut metadata = self.inner.lock();
        Self::decide(&mut metadata.stripes[stripe], joined)
    }

    fn decide(entry: &mut Stripe, joined: &mut Option<u64>) -> Decision {
        // Before anything else: a failed attempt fails everyone who waited for
        // it, even if a newer attempt has since started or finished.
        if joined.is_some() && *joined <= entry.last_failed_attempt {
            entry.active_requests -= 1;
            return Decision::Fail;
        }
        match entry.state {
            StripeState::Resident { slot } => Decision::Ready { slot },
            StripeState::Absent => {
                let attempt = entry.next_attempt;
                entry.next_attempt = attempt.checked_add(1).expect("attempt overflow");
                entry.state = StripeState::Loading { attempt };
                *joined = Some(attempt);
                Decision::Wait {
                    fetch: Some(attempt),
                }
            }
            StripeState::Loading { attempt } => {
                *joined = Some(attempt);
                Decision::Wait { fetch: None }
            }
            StripeState::Evicting { .. } => Decision::Wait { fetch: None },
            StripeState::Failed { .. } => {
                entry.active_requests -= 1;
                Decision::Fail
            }
        }
    }

    /// A request that ran is done. A successful write makes the stripe dirty;
    /// a failed one leaves its contents uncertain for good.
    pub fn finish(&self, stripe: usize, write: bool, ok: bool) {
        let mut metadata = self.inner.lock();
        let entry = &mut metadata.stripes[stripe];
        entry.active_requests -= 1;
        if !write {
            return;
        }
        if let StripeState::Resident { slot } = entry.state {
            if ok {
                entry.dirty = true;
            } else {
                entry.state = StripeState::Failed { slot: Some(slot) };
            }
        }
    }

    /// The attempt could not bring the stripe in; everyone waiting on it fails.
    pub fn fail_attempt(&self, stripe: usize, attempt: u64) {
        let mut metadata = self.inner.lock();
        let entry = &mut metadata.stripes[stripe];
        entry.last_failed_attempt = entry.last_failed_attempt.max(Some(attempt));
        if entry.state == (StripeState::Loading { attempt }) {
            entry.state = StripeState::Absent;
        }
    }

    pub fn is_loading(&self, stripe: usize, attempt: u64) -> bool {
        self.inner.lock().stripes[stripe].state == StripeState::Loading { attempt }
    }

    pub fn publish_resident(&self, stripe: usize, attempt: u64, slot: SlotId) -> bool {
        let mut metadata = self.inner.lock();
        let entry = &mut metadata.stripes[stripe];
        if entry.state != (StripeState::Loading { attempt }) {
            return false;
        }
        entry.state = StripeState::Resident { slot };
        entry.dirty = false;
        true
    }

    pub fn last_accessed(&self, stripe: usize) -> u64 {
        self.inner.lock().stripes[stripe].last_accessed
    }

    /// Take a stripe nobody is using out of its slot. Returns the slot and
    /// whether it has to be uploaded first.
    pub fn reserve_victim(&self, stripe: usize) -> Option<(SlotId, bool)> {
        let mut metadata = self.inner.lock();
        let entry = &mut metadata.stripes[stripe];
        match entry.state {
            StripeState::Resident { slot } if entry.active_requests == 0 => {
                entry.state = StripeState::Evicting { slot };
                Some((slot, entry.dirty))
            }
            _ => None,
        }
    }

    /// The eviction finished: the stripe has no slot, and whatever it held is
    /// in its source now.
    pub fn finish_eviction(&self, stripe: usize) {
        let mut metadata = self.inner.lock();
        let entry = &mut metadata.stripes[stripe];
        if let StripeState::Evicting { .. } = entry.state {
            entry.state = StripeState::Absent;
            entry.dirty = false;
        }
    }

    /// The eviction failed: the stripe keeps its slot and its dirty flag.
    pub fn abort_eviction(&self, stripe: usize) {
        let mut metadata = self.inner.lock();
        let entry = &mut metadata.stripes[stripe];
        if let StripeState::Evicting { slot } = entry.state {
            entry.state = StripeState::Resident { slot };
        }
    }

    /// Take the slot back from a failed stripe once nothing can touch it.
    pub fn reclaim_failed(&self, stripe: usize) -> Option<SlotId> {
        let mut metadata = self.inner.lock();
        let entry = &mut metadata.stripes[stripe];
        match entry.state {
            StripeState::Failed { slot: Some(slot) } if entry.active_requests == 0 => {
                entry.state = StripeState::Failed { slot: None };
                Some(slot)
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn loaded(metadata: &SpillSharedMetadata, stripe: usize, slot: SlotId) {
        let mut joined = None;
        let Decision::Wait {
            fetch: Some(attempt),
        } = metadata.admit(stripe, &mut joined)
        else {
            panic!("an absent stripe did not start a fetch");
        };
        assert!(metadata.publish_resident(stripe, attempt, slot));
        metadata.finish(stripe, false, true);
    }

    #[test]
    fn the_first_request_starts_a_fetch_and_the_rest_join_it() {
        let metadata = SpillSharedMetadata::new(4);
        let (mut first, mut second) = (None, None);

        assert_eq!(
            metadata.admit(2, &mut first),
            Decision::Wait { fetch: Some(1) }
        );
        assert_eq!(
            metadata.admit(2, &mut second),
            Decision::Wait { fetch: None }
        );
        assert_eq!((first, second), (Some(1), Some(1)));
        assert_eq!(metadata.get(2).active_requests, 2);

        assert!(metadata.publish_resident(2, 1, 7));
        assert_eq!(metadata.retry(2, &mut first), Decision::Ready { slot: 7 });
        assert_eq!(metadata.retry(2, &mut second), Decision::Ready { slot: 7 });
    }

    #[test]
    fn a_stripe_with_requests_cannot_be_evicted() {
        let metadata = SpillSharedMetadata::new(1);
        loaded(&metadata, 0, 3);

        let mut joined = None;
        assert_eq!(metadata.admit(0, &mut joined), Decision::Ready { slot: 3 });
        assert_eq!(metadata.reserve_victim(0), None);

        metadata.finish(0, false, true);
        assert_eq!(metadata.reserve_victim(0), Some((3, false)));
    }

    /// Everyone waiting on a failed attempt fails, rather than waking to an
    /// absent stripe and starting another attempt against the same failure.
    #[test]
    fn a_failed_attempt_fails_its_waiters_instead_of_retrying() {
        let metadata = SpillSharedMetadata::new(1);
        let (mut first, mut second) = (None, None);
        metadata.admit(0, &mut first);
        metadata.admit(0, &mut second);

        metadata.fail_attempt(0, 1);

        assert_eq!(metadata.get(0).state, StripeState::Absent);
        assert_eq!(metadata.retry(0, &mut first), Decision::Fail);
        assert_eq!(metadata.retry(0, &mut second), Decision::Fail);
        assert_eq!(metadata.get(0).active_requests, 0);

        // A new request starts afresh.
        let mut third = None;
        assert_eq!(
            metadata.admit(0, &mut third),
            Decision::Wait { fetch: Some(2) }
        );
    }

    #[test]
    fn a_waiter_on_a_failed_attempt_fails_even_if_a_newer_one_succeeded() {
        let metadata = SpillSharedMetadata::new(1);
        let mut old = None;
        metadata.admit(0, &mut old);
        metadata.fail_attempt(0, 1);

        let mut new = None;
        metadata.admit(0, &mut new);
        assert!(metadata.publish_resident(0, 2, 5));

        assert_eq!(metadata.retry(0, &mut old), Decision::Fail);
        assert_eq!(metadata.retry(0, &mut new), Decision::Ready { slot: 5 });
    }

    /// Waiting through an eviction is not waiting on an attempt: once the
    /// stripe is gone, the waiter brings it back.
    #[test]
    fn a_request_that_waited_through_an_eviction_fetches_again() {
        let metadata = SpillSharedMetadata::new(1);
        loaded(&metadata, 0, 1);
        assert!(metadata.reserve_victim(0).is_some());

        let mut joined = None;
        assert_eq!(
            metadata.admit(0, &mut joined),
            Decision::Wait { fetch: None }
        );
        assert_eq!(joined, None);

        metadata.finish_eviction(0);
        assert_eq!(
            metadata.retry(0, &mut joined),
            Decision::Wait { fetch: Some(2) }
        );
    }

    #[test]
    fn a_write_marks_the_stripe_dirty_and_a_failed_one_fails_it() {
        let metadata = SpillSharedMetadata::new(2);
        loaded(&metadata, 0, 1);
        loaded(&metadata, 1, 2);

        let mut joined = None;
        metadata.admit(0, &mut joined);
        metadata.finish(0, true, true);
        assert!(metadata.get(0).dirty);
        assert_eq!(metadata.reserve_victim(0), Some((1, true)));

        let mut joined = None;
        metadata.admit(1, &mut joined);
        metadata.admit(1, &mut joined);
        metadata.finish(1, true, false);
        assert_eq!(metadata.get(1).state, StripeState::Failed { slot: Some(2) });

        // A later success does not bring it back, and the slot stays until the
        // last request is done.
        assert_eq!(metadata.reclaim_failed(1), None);
        metadata.finish(1, true, true);
        assert_eq!(metadata.get(1).state, StripeState::Failed { slot: Some(2) });
        assert_eq!(metadata.reclaim_failed(1), Some(2));
        assert_eq!(metadata.get(1).state, StripeState::Failed { slot: None });

        let mut joined = None;
        assert_eq!(metadata.admit(1, &mut joined), Decision::Fail);
        assert_eq!(metadata.get(1).active_requests, 0);
    }

    #[test]
    fn a_failed_eviction_keeps_the_slot_and_the_dirty_flag() {
        let metadata = SpillSharedMetadata::new(1);
        loaded(&metadata, 0, 4);
        let mut joined = None;
        metadata.admit(0, &mut joined);
        metadata.finish(0, true, true);

        assert_eq!(metadata.reserve_victim(0), Some((4, true)));
        metadata.abort_eviction(0);

        let stripe = metadata.get(0);
        assert_eq!(stripe.state, StripeState::Resident { slot: 4 });
        assert!(stripe.dirty);
    }

    #[test]
    fn a_later_publish_for_a_stale_attempt_is_refused() {
        let metadata = SpillSharedMetadata::new(1);
        let mut joined = None;
        metadata.admit(0, &mut joined);
        metadata.fail_attempt(0, 1);
        assert!(!metadata.publish_resident(0, 1, 9));
        assert_eq!(metadata.get(0).state, StripeState::Absent);
    }

    #[test]
    fn admission_orders_access() {
        let metadata = SpillSharedMetadata::new(2);
        let mut joined = None;
        metadata.admit(1, &mut joined);
        let mut joined = None;
        metadata.admit(0, &mut joined);
        assert!(metadata.last_accessed(0) > metadata.last_accessed(1));

        // Retrying does not count as an access.
        let before = metadata.last_accessed(1);
        let mut joined = Some(1);
        metadata.retry(1, &mut joined);
        assert_eq!(metadata.last_accessed(1), before);
    }
}
