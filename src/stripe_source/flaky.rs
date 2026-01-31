use std::collections::HashMap;

use super::StripeSource;
use crate::{block_device::SharedBuffer, Result};

/// A stripe source wrapper that fails specified stripes a fixed number of times.
pub struct FlakyStripeSource {
    inner: Box<dyn StripeSource>,
    remaining_failures: HashMap<usize, usize>,
}

impl FlakyStripeSource {
    pub fn new(inner: Box<dyn StripeSource>, failures: Vec<(usize, usize)>) -> Self {
        let mut remaining_failures = HashMap::new();
        for (stripe_id, count) in failures {
            *remaining_failures.entry(stripe_id).or_insert(0) += count;
        }
        Self {
            inner,
            remaining_failures,
        }
    }
}

impl StripeSource for FlakyStripeSource {
    fn request(&mut self, stripe_id: usize, buffer: SharedBuffer) -> Result<()> {
        self.inner.request(stripe_id, buffer)
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        self.inner
            .poll()
            .into_iter()
            .map(|(stripe_id, success)| {
                if let Some(remaining) = self.remaining_failures.get_mut(&stripe_id) {
                    if *remaining > 0 {
                        *remaining -= 1;
                        if *remaining == 0 {
                            self.remaining_failures.remove(&stripe_id);
                        }
                        return (stripe_id, false);
                    }
                }
                (stripe_id, success)
            })
            .collect()
    }

    fn busy(&self) -> bool {
        self.inner.busy()
    }

    fn sector_count(&self) -> u64 {
        self.inner.sector_count()
    }

    fn has_stripe(&self, stripe_id: usize) -> bool {
        self.inner.has_stripe(stripe_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::shared_buffer;

    struct ImmediateStripeSource {
        completions: Vec<(usize, bool)>,
        sector_count: u64,
    }

    impl ImmediateStripeSource {
        fn new(sector_count: u64) -> Self {
            Self {
                completions: Vec::new(),
                sector_count,
            }
        }
    }

    impl StripeSource for ImmediateStripeSource {
        fn request(&mut self, stripe_id: usize, _buffer: SharedBuffer) -> Result<()> {
            self.completions.push((stripe_id, true));
            Ok(())
        }

        fn poll(&mut self) -> Vec<(usize, bool)> {
            std::mem::take(&mut self.completions)
        }

        fn busy(&self) -> bool {
            !self.completions.is_empty()
        }

        fn sector_count(&self) -> u64 {
            self.sector_count
        }

        fn has_stripe(&self, _stripe_id: usize) -> bool {
            true
        }
    }

    #[test]
    fn flaky_source_fails_then_succeeds() {
        let inner: Box<dyn StripeSource> = Box::new(ImmediateStripeSource::new(8));
        let mut source = FlakyStripeSource::new(inner, vec![(1, 2)]);

        source.request(1, shared_buffer(512)).unwrap();
        assert_eq!(source.poll(), vec![(1, false)]);

        source.request(1, shared_buffer(512)).unwrap();
        assert_eq!(source.poll(), vec![(1, false)]);

        source.request(1, shared_buffer(512)).unwrap();
        assert_eq!(source.poll(), vec![(1, true)]);

        assert!(source.has_stripe(0));
        assert_eq!(source.sector_count(), 8);
        assert!(!source.busy());
    }
}
