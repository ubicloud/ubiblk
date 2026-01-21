use std::time::Duration;

use super::*;

impl dyn StripeSource {
    pub fn wait_for_stripe(&mut self, stripe_id: usize, timeout: Duration) -> Result<()> {
        let start = std::time::Instant::now();
        loop {
            let completed = self.poll();
            for (completed_stripe_id, success) in completed {
                if completed_stripe_id == stripe_id {
                    if success {
                        return Ok(());
                    } else {
                        return Err(crate::ubiblk_error!(StripeFetchFailed {
                            stripe: stripe_id
                        }));
                    }
                }
            }
            if start.elapsed() >= timeout {
                return Err(crate::ubiblk_error!(StripeFetchTimeout {
                    stripe: stripe_id
                }));
            }
            if !self.busy() {
                std::thread::sleep(std::time::Duration::from_millis(1));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::UbiblkError;

    struct MockStripeSource {
        busy: bool,
        completed_stripes: Vec<(usize, bool)>,
    }

    impl StripeSource for MockStripeSource {
        fn request(&mut self, _stripe_id: usize, _buffer: SharedBuffer) -> Result<()> {
            self.busy = true;
            Ok(())
        }

        fn poll(&mut self) -> Vec<(usize, bool)> {
            let completed = self.completed_stripes.clone();
            self.completed_stripes.clear();
            self.busy = false;
            completed
        }

        fn busy(&self) -> bool {
            self.busy
        }

        fn sector_count(&self) -> u64 {
            0
        }

        fn has_stripe(&self, _stripe_id: usize) -> bool {
            true
        }
    }

    #[test]
    fn test_wait_for_stripe_success() {
        let mut source: Box<dyn StripeSource> = Box::new(MockStripeSource {
            busy: true,
            completed_stripes: vec![(1, true)],
        });
        let result = source.wait_for_stripe(1, Duration::from_millis(1000));
        assert!(result.is_ok());
    }

    #[test]
    fn test_wait_for_stripe_failure() {
        let mut source: Box<dyn StripeSource> = Box::new(MockStripeSource {
            busy: true,
            completed_stripes: vec![(1, false)],
        });
        let result = source.wait_for_stripe(1, Duration::from_millis(1000));
        assert!(matches!(
            result,
            Err(UbiblkError::StripeFetchFailed { stripe: 1, .. })
        ));
    }

    #[test]
    fn test_wait_for_stripe_timeout() {
        let mut source: Box<dyn StripeSource> = Box::new(MockStripeSource {
            busy: true,
            completed_stripes: vec![],
        });
        let result = source.wait_for_stripe(1, Duration::from_millis(100));
        assert!(matches!(
            result,
            Err(UbiblkError::StripeFetchTimeout { stripe: 1, .. })
        ));
    }

    #[test]
    fn test_wait_for_stripe_timeout_with_other_completion() {
        let mut source: Box<dyn StripeSource> = Box::new(MockStripeSource {
            busy: true,
            completed_stripes: vec![(2, true)],
        });
        let result = source.wait_for_stripe(1, Duration::from_millis(50));
        assert!(matches!(
            result,
            Err(UbiblkError::StripeFetchTimeout { stripe: 1, .. })
        ));
    }
}
