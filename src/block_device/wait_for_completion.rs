use super::*;

pub fn wait_for_completion(
    channel: &mut dyn IoChannel,
    request_id: usize,
    timeout: std::time::Duration,
) -> Result<()> {
    let start = std::time::Instant::now();
    while start.elapsed() < timeout {
        let completions = channel.poll();
        for (id, success) in completions.into_iter() {
            if id != request_id {
                continue;
            }
            if !success {
                return Err(crate::ubiblk_error!(IoError {
                    source: std::io::Error::other(format!("Failed request ID: {request_id}")),
                }));
            }
            return Ok(());
        }
        if !channel.busy() {
            std::thread::sleep(std::time::Duration::from_millis(1));
        }
    }
    Err(crate::ubiblk_error!(IoError {
        source: std::io::Error::new(
            std::io::ErrorKind::TimedOut,
            format!("Timeout while waiting for request ID {request_id}"),
        ),
    }))
}

#[cfg(test)]
mod tests {
    use crate::UbiblkError;
    use crate::{block_device::bdev_test::TestBlockDevice, vhost_backend::SECTOR_SIZE};

    use super::*;

    #[test]
    fn test_wait_for_completion_success() {
        let mut channel = TestBlockDevice::new(1024).create_channel().unwrap();
        channel.add_read(0, 1, shared_buffer(SECTOR_SIZE), 1);
        channel.add_read(0, 1, shared_buffer(SECTOR_SIZE), 4);
        channel.submit().unwrap();
        wait_for_completion(channel.as_mut(), 4, std::time::Duration::from_millis(10)).unwrap();
    }

    #[test]
    fn test_wait_for_completion_failure() {
        let bdev = TestBlockDevice::new(1024);
        let mut channel = bdev.create_channel().unwrap();
        bdev.fail_next
            .store(true, std::sync::atomic::Ordering::SeqCst);
        channel.add_read(0, 1, shared_buffer(SECTOR_SIZE), 7);
        channel.submit().unwrap();
        let err = wait_for_completion(channel.as_mut(), 7, std::time::Duration::from_millis(10))
            .unwrap_err();
        assert!(matches!(&err, UbiblkError::IoError {
            source,
            ..
        } if source.kind() == std::io::ErrorKind::Other && source.to_string().contains("Failed request ID: 7")));
    }

    #[test]
    fn test_wait_for_completion_timeout() {
        let mut channel = TestBlockDevice::new(1024).create_channel().unwrap();
        let err = wait_for_completion(channel.as_mut(), 1, std::time::Duration::from_millis(10))
            .unwrap_err();
        assert!(matches!(&err, UbiblkError::IoError {
            source,
            ..
        } if source.kind() == std::io::ErrorKind::TimedOut && source.to_string().contains("Timeout while waiting for request ID 1")));
    }
}
