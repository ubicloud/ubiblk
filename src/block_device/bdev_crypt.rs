use super::*;
use crate::{Error, Result};
use crate::{XTS_AES_256_dec, XTS_AES_256_enc};
use log::error;

struct Request {
    sector: u64,
    buf: SharedBuffer,
    len: usize,
}

struct CryptIoChannel {
    base: Box<dyn IoChannel>,
    key1: [u8; 32],
    key2: [u8; 32],
    read_requests: [Option<Request>; 256],
}

impl CryptIoChannel {
    pub fn new(base: Box<dyn IoChannel>, key1: [u8; 32], key2: [u8; 32]) -> Self {
        CryptIoChannel {
            base,
            key1,
            key2,
            read_requests: [const { None }; 256],
        }
    }
}

impl CryptIoChannel {
    fn get_initial_tweak(&self, sector: u64) -> [u8; 16] {
        /*
         * Based on SPDK's _sw_accel_crypto_operation() in spdk/lib/accel/accel_sw.c:
         *   uint64_t iv[2];
         *   iv[0] = 0;
         *   iv[1] = accel_task->iv;
         */
        let mut tweak = [0u8; 16];
        // First 8 bytes are already zero.
        // Encode the sector number as little-endian into the second 8 bytes.
        tweak[8..].copy_from_slice(&sector.to_le_bytes());
        tweak
    }

    /*
     * From isa-l_crypto/include/aes_xts.h:
     *
     * The input and output buffers can be overlapping as long as the output buffer
     * pointer is not less than the input buffer pointer. If the two pointers are the
     * same, then encryption/decryption will occur in-place.
     *
     * The input and output buffers, keys, pre-expanded keys and initial tweak value
     * are not required to be aligned to 16 bytes, any alignment works.
     */

    fn decrypt(&mut self, buf: &mut [u8], sector_start: u64, sector_count: u64) {
        for i in 0..sector_count {
            let sector = sector_start + i;
            let mut tweak = self.get_initial_tweak(sector);
            let sector_data = &mut buf[(i * 512) as usize..((i + 1) * 512) as usize];
            unsafe {
                XTS_AES_256_dec(
                    self.key2.as_mut_ptr(),
                    self.key1.as_mut_ptr(),
                    tweak.as_mut_ptr(),
                    512,
                    sector_data.as_ptr(),
                    sector_data.as_mut_ptr(),
                );
            }
        }
    }

    fn encrypt(&mut self, buf: &mut [u8], sector_start: u64, sector_count: u64) {
        for i in 0..sector_count {
            let sector = sector_start + i;
            let mut tweak = self.get_initial_tweak(sector);
            let sector_data = &mut buf[((i * 512) as usize)..((i + 1) * 512) as usize];
            unsafe {
                XTS_AES_256_enc(
                    self.key2.as_mut_ptr(),
                    self.key1.as_mut_ptr(),
                    tweak.as_mut_ptr(),
                    512,
                    sector_data.as_ptr(),
                    sector_data.as_mut_ptr(),
                );
            }
        }
    }
}

impl IoChannel for CryptIoChannel {
    fn add_read(&mut self, sector: u64, buf: SharedBuffer, len: usize, id: usize) {
        if len % 512 != 0 {
            // programming error, so panic
            panic!("Read length must be a multiple of 512");
        }
        self.read_requests[id] = Some(Request {
            sector,
            buf: buf.clone(),
            len,
        });
        self.base.add_read(sector, buf.clone(), len, id);
    }

    fn add_write(&mut self, sector: u64, buf: SharedBuffer, len: usize, id: usize) {
        if len % 512 != 0 {
            // programming error, so panic
            panic!("Write length must be a multiple of 512");
        }
        self.encrypt(buf.borrow_mut().as_mut_slice(), sector, (len / 512) as u64);
        self.base.add_write(sector, buf.clone(), len, id);
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
            if let Some(req) = self.read_requests[id].take() {
                self.decrypt(
                    req.buf.borrow_mut().as_mut_slice(),
                    req.sector,
                    (req.len / 512) as u64,
                );
                results.push((id, result));
            } else {
                results.push((id, result));
            }
        }
        results
    }

    fn busy(&mut self) -> bool {
        self.base.busy()
    }
}

pub struct CryptBlockDevice {
    base: Box<dyn BlockDevice>,
    key1: String,
    key2: String,
}

impl BlockDevice for CryptBlockDevice {
    fn create_channel(&self) -> Result<Box<dyn IoChannel>> {
        let base_channel = self.base.create_channel()?;
        let (key1, key2) = prepare_keys(&self.key1, &self.key2)?;
        let crypt_channel = CryptIoChannel::new(base_channel, key1, key2);
        Ok(Box::new(crypt_channel))
    }

    fn size(&self) -> u64 {
        self.base.size()
    }
}

impl CryptBlockDevice {
    pub fn new(base: Box<dyn BlockDevice>, key1: &str, key2: &str) -> Box<Self> {
        Box::new(CryptBlockDevice {
            base,
            key1: key1.to_string(),
            key2: key2.to_string(),
        })
    }
}

fn prepare_keys(hex_key1: &str, hex_key2: &str) -> Result<([u8; 32], [u8; 32])> {
    fn decode_key(hex: &str) -> Result<[u8; 32]> {
        let bytes = hex::decode(hex).map_err(|e| {
            error!("Failed to decode hex string: {}", e);
            Error::InvalidParameter
        })?;
        let mut key = [0u8; 32];
        let copy_len = std::cmp::min(bytes.len(), 32);
        key[..copy_len].copy_from_slice(&bytes[..copy_len]);
        Ok(key)
    }

    let key1 = decode_key(hex_key1)?;
    let key2 = decode_key(hex_key2)?;

    Ok((key1, key2))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::bdev_test::TestBlockDevice;

    #[test]
    fn test_crypt_block_device() {
        let base = TestBlockDevice::new(1024 * 1024);
        let metrics = base.metrics.clone();
        let mem = base.mem.clone();
        let key1 = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
        let key2 = "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210";
        let crypt_bdev = CryptBlockDevice::new(Box::new(base), key1, key2);
        let mut channel = crypt_bdev
            .create_channel()
            .expect("Failed to create channel");

        // initially, first 2 sectors of mem should be the same
        assert_eq!(
            &mem.read().unwrap()[0..512],
            &mem.read().unwrap()[512..1024]
        );

        let sample_data = "Hello, world!".as_bytes();
        let buf = Rc::new(RefCell::new(vec![0u8; 512]));

        for i in 0..2 {
            buf.borrow_mut()[0..sample_data.len()].copy_from_slice(sample_data);
            channel.add_write(i, buf.clone(), 512, 12);
            channel.submit().expect("Failed to submit write request");
            while channel.busy() {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            let poll_results = channel.poll();
            assert_eq!(poll_results, vec![(12, true)]);
        }

        assert_eq!(metrics.read().unwrap().reads, 0);
        assert_eq!(metrics.read().unwrap().writes, 2);
        assert_eq!(metrics.read().unwrap().flushes, 0);

        for i in 0..2 {
            let read_id = 34;
            buf.borrow_mut().fill(0);
            channel.add_read(i, buf.clone(), 512, read_id);
            channel.submit().expect("Failed to submit read request");

            while channel.busy() {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }

            let poll_results = channel.poll();
            assert_eq!(poll_results, vec![(read_id, true)]);
            assert_eq!(&buf.borrow()[0..sample_data.len()], sample_data);
        }

        assert_eq!(metrics.read().unwrap().reads, 2);
        assert_eq!(metrics.read().unwrap().writes, 2);
        assert_eq!(metrics.read().unwrap().flushes, 0);

        let flush_id = 56;
        channel.add_flush(flush_id);
        channel.submit().expect("Failed to submit flush request");
        while channel.busy() {
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        let poll_results = channel.poll();
        assert_eq!(poll_results, vec![(flush_id, true)]);

        assert_eq!(metrics.read().unwrap().reads, 2);
        assert_eq!(metrics.read().unwrap().writes, 2);
        assert_eq!(metrics.read().unwrap().flushes, 1);

        // Although we wrote the same data to both sectors, the encrypted data
        // should be different due to the different tweaks.
        assert_ne!(
            &mem.read().unwrap()[0..512],
            &mem.read().unwrap()[512..1024]
        );
    }
}
