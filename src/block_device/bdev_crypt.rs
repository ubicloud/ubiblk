use super::*;

use crate::{crypt::XtsBlockCipher, Result};

struct Request {
    sector_offset: u64,
    sector_count: u32,
    buf: SharedBuffer,
}

struct CryptIoChannel {
    base: Box<dyn IoChannel>,
    xts_cipher: XtsBlockCipher,
    read_requests: Vec<Option<Request>>,
}

impl CryptIoChannel {
    pub fn new(base: Box<dyn IoChannel>, xts_cipher: XtsBlockCipher) -> Self {
        CryptIoChannel {
            base,
            xts_cipher,
            read_requests: Vec::new(),
        }
    }
}

impl IoChannel for CryptIoChannel {
    fn add_read(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        if id >= self.read_requests.len() {
            self.read_requests.resize_with(id + 1, || None);
        }
        self.read_requests[id] = Some(Request {
            sector_offset,
            buf: buf.clone(),
            sector_count,
        });
        self.base
            .add_read(sector_offset, sector_count, buf.clone(), id);
    }

    fn add_write(&mut self, sector_offset: u64, sector_count: u32, buf: SharedBuffer, id: usize) {
        self.xts_cipher.encrypt(
            buf.borrow_mut().as_mut_slice(),
            sector_offset,
            sector_count as u64,
        );
        self.base
            .add_write(sector_offset, sector_count, buf.clone(), id);
    }

    fn add_flush(&mut self, id: usize) {
        self.base.add_flush(id);
    }

    fn submit(&mut self) -> Result<()> {
        self.base.submit()
    }

    fn poll(&mut self) -> Vec<(usize, bool)> {
        let mut results = vec![];
        for (id, result) in self.base.poll() {
            if id < self.read_requests.len() {
                if let Some(req) = self.read_requests[id].take() {
                    if result {
                        self.xts_cipher.decrypt(
                            req.buf.borrow_mut().as_mut_slice(),
                            req.sector_offset,
                            req.sector_count as u64,
                        );
                    }
                    results.push((id, result));
                    continue;
                }
            }
            results.push((id, result));
        }
        results
    }

    fn busy(&self) -> bool {
        self.base.busy()
    }
}

pub struct CryptBlockDevice {
    base: Box<dyn BlockDevice>,
    xts_cipher: XtsBlockCipher,
}

impl BlockDevice for CryptBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let base_channel = self.base.create_channel()?;
        let crypt_channel = CryptIoChannel::new(base_channel, self.xts_cipher.clone());
        Ok(Box::new(crypt_channel))
    }

    fn sector_count(&self) -> u64 {
        self.base.sector_count()
    }

    fn clone(&self) -> Box<dyn BlockDevice> {
        Box::new(CryptBlockDevice {
            base: self.base.clone(),
            xts_cipher: self.xts_cipher.clone(),
        })
    }
}

impl CryptBlockDevice {
    pub fn new(base: Box<dyn BlockDevice>, key1: Vec<u8>, key2: Vec<u8>) -> Result<Box<Self>> {
        let xts_cipher = XtsBlockCipher::new(key1, key2)?;
        Ok(Box::new(CryptBlockDevice { base, xts_cipher }))
    }
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::*;

    use crate::{block_device::bdev_test::TestBlockDevice, vhost_backend::SECTOR_SIZE};

    #[test]
    fn test_crypt_block_device() {
        let base = TestBlockDevice::new(1024 * 1024);
        let metrics = base.metrics.clone();
        let mem = base.mem.clone();
        let key1 = [
            1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103,
            137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239,
        ];
        let key2 = [
            254, 220, 186, 152, 118, 84, 50, 16, 254, 220, 186, 152, 118, 84, 50, 16, 254, 220,
            186, 152, 118, 84, 50, 16, 254, 220, 186, 152, 118, 84, 50, 16,
        ];
        let crypt_bdev = CryptBlockDevice::new(Box::new(base), key1.to_vec(), key2.to_vec())
            .expect("Failed to create CryptBlockDevice");
        let mut channel = crypt_bdev
            .create_channel()
            .expect("Failed to create channel");

        // initially, first 2 sectors of mem should be the same
        assert_eq!(
            &mem.read().unwrap()[0..SECTOR_SIZE],
            &mem.read().unwrap()[SECTOR_SIZE..SECTOR_SIZE * 2]
        );

        let sample_data = "Hello, world!".as_bytes();
        let buf = shared_buffer(SECTOR_SIZE);

        for i in 0..2 {
            buf.borrow_mut().as_mut_slice()[0..sample_data.len()].copy_from_slice(sample_data);
            channel.add_write(i, 1, buf.clone(), 12);
            channel.submit().expect("Failed to submit write request");
            wait_for_completion(channel.as_mut(), 12, Duration::from_secs(5)).unwrap();
        }

        assert_eq!(metrics.read().unwrap().reads, 0);
        assert_eq!(metrics.read().unwrap().writes, 2);
        assert_eq!(metrics.read().unwrap().flushes, 0);

        for i in 0..2 {
            let read_id = 34;
            buf.borrow_mut().as_mut_slice().fill(0);
            channel.add_read(i, 1, buf.clone(), read_id);
            channel.submit().expect("Failed to submit read request");
            wait_for_completion(channel.as_mut(), read_id, Duration::from_secs(5)).unwrap();

            assert_eq!(&buf.borrow().as_slice()[0..sample_data.len()], sample_data);
        }

        assert_eq!(metrics.read().unwrap().reads, 2);
        assert_eq!(metrics.read().unwrap().writes, 2);
        assert_eq!(metrics.read().unwrap().flushes, 0);

        let flush_id = 56;
        channel.add_flush(flush_id);
        channel.submit().expect("Failed to submit flush request");
        assert!(channel.busy());
        wait_for_completion(channel.as_mut(), flush_id, Duration::from_secs(5)).unwrap();
        assert!(!channel.busy());

        assert_eq!(metrics.read().unwrap().reads, 2);
        assert_eq!(metrics.read().unwrap().writes, 2);
        assert_eq!(metrics.read().unwrap().flushes, 1);

        // Although we wrote the same data to both sectors, the encrypted data
        // should be different due to the different tweaks.
        assert_ne!(
            &mem.read().unwrap()[0..SECTOR_SIZE],
            &mem.read().unwrap()[SECTOR_SIZE..SECTOR_SIZE * 2]
        );
    }

    #[test]
    fn test_invalid_key_length() {
        let base = TestBlockDevice::new(1024 * 1024);
        let key1 = [
            1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103,
            137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205, 239, 1, 35, 69, 103, 137, 171, 205,
            239,
        ];
        let key2 = [
            254, 220, 186, 152, 118, 84, 50, 16, 254, 220, 186, 152, 118, 84, 50, 16, 254, 220,
            186, 152, 118, 84, 50, 16, 254, 220, 186, 152, 118, 84, 50, 16, 254, 220, 186, 152,
            118, 84, 50, 16,
        ];
        let result = CryptBlockDevice::new(Box::new(base), key1.to_vec(), key2.to_vec());
        assert!(result.is_err());
    }

    #[test]
    fn test_sector_count() {
        let base = TestBlockDevice::new(1024 * 1024);
        let bdev = CryptBlockDevice::new(Box::new(base), vec![0u8; 32], vec![0u8; 32]).unwrap();

        assert_eq!(bdev.sector_count(), 2048);
    }

    #[test]
    fn test_clone() {
        let base = TestBlockDevice::new(1024 * 1024);
        let key1 = vec![1u8; 32];
        let key2 = vec![3u8; 32];
        let bdev = CryptBlockDevice::new(Box::new(base), key1, key2).unwrap();
        let bdev_clone = bdev.clone();
        assert_eq!(bdev.sector_count(), bdev_clone.sector_count());

        // write some data using the original device
        let mut channel = bdev.create_channel().unwrap();
        let buf = shared_buffer(SECTOR_SIZE);
        buf.borrow_mut().as_mut_slice()[0..5].copy_from_slice(b"Hello");
        channel.add_write(0, 1, buf.clone(), 1);
        channel.submit().unwrap();
        assert_eq!(channel.poll(), vec![(1, true)]);

        // read the data back using the cloned device
        let mut clone_channel = bdev_clone.create_channel().unwrap();
        let read_buf = shared_buffer(SECTOR_SIZE);
        clone_channel.add_read(0, 1, read_buf.clone(), 2);
        clone_channel.submit().unwrap();
        assert_eq!(clone_channel.poll(), vec![(2, true)]);
        assert_eq!(&read_buf.borrow().as_slice()[0..5], b"Hello");
    }
}
