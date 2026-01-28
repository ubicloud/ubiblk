use std::{cell::RefCell, collections::VecDeque, rc::Rc};

use libublk::{
    helpers::IoBuf,
    io::{UblkIOCtx, UblkQueue},
    BufDesc, UblkError, UblkIORes,
};
use log::error;

use crate::backends::ublk::{UblkIoRequest, UblkOp};
use crate::block_device::{IoChannel, SharedBuffer};
use crate::{backends::common::SECTOR_SIZE, utils::AlignedBuf};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UblkIoError {
    Invalid,
    Io,
}

type UblkIoResult<T> = std::result::Result<T, UblkIoError>;

pub struct UblkIoHandler {
    pub max_io_bytes: usize,
    pub pending_requests: VecDeque<UblkIoRequest>,
    pub inflight_requests: Vec<Option<UblkIoRequest>>,
    pub io_channel: Box<dyn IoChannel>,
    pub backend_bufs: Vec<SharedBuffer>,
    pub bufs: Vec<IoBuf<u8>>,
}

impl UblkIoHandler {
    pub fn new(
        alignment: usize,
        max_io_bytes: usize,
        io_channel: Box<dyn IoChannel>,
        ublk_io_bufs: Vec<IoBuf<u8>>,
        queue_size: usize,
    ) -> Self {
        let backend_bufs = (0..queue_size)
            .map(|_| {
                Rc::new(RefCell::new(AlignedBuf::new_with_alignment(
                    max_io_bytes,
                    alignment,
                )))
            })
            .collect::<Vec<_>>();

        Self {
            max_io_bytes,
            pending_requests: VecDeque::new(),
            inflight_requests: vec![None; queue_size],
            io_channel,
            backend_bufs,
            bufs: ublk_io_bufs,
        }
    }

    pub fn handle(&mut self, q: &UblkQueue, tag: u16, io: &UblkIOCtx) {
        if io.is_tgt_io() {
            return;
        }

        let iod = q.get_iod(tag);
        let op = UblkOp::from_raw(iod.op_flags & 0xff);
        let sector_offset = iod.start_sector;
        let sector_count = iod.nr_sectors;
        let bytes = sector_count as usize * SECTOR_SIZE;

        if bytes > self.max_io_bytes {
            error!(
                "UBLK request exceeds max IO bytes: {bytes} > {}",
                self.max_io_bytes
            );
            let completion_slice = BufDesc::Slice(self.bufs[tag as usize].as_slice());
            let _ = q.complete_io_cmd_unified(tag, completion_slice, Err(UblkError::InvalidVal));
            return;
        }

        self.pending_requests.push_back(UblkIoRequest {
            op,
            sector_offset,
            sector_count,
            request_id: tag as usize,
            bytes,
        });

        if io.is_last_cqe() {
            self.process_pending_requests(q);
        }
    }

    fn enqueue_request(&mut self, request: &UblkIoRequest) -> UblkIoResult<()> {
        let tag = request.request_id;
        let backend_buf = &self.backend_bufs[tag];
        let ublk_buf = &self.bufs[tag];
        let bytes = request.bytes;
        let backend_len = backend_buf.borrow().len();

        if bytes > backend_len || bytes > ublk_buf.len() {
            return Err(UblkIoError::Invalid);
        }

        match request.op {
            UblkOp::Read => self.io_channel.add_read(
                request.sector_offset,
                request.sector_count,
                backend_buf.clone(),
                request.request_id,
            ),
            UblkOp::Write => {
                let ublk_slice = ublk_buf.subslice(..bytes);
                backend_buf.borrow_mut().as_mut_slice()[..bytes].copy_from_slice(ublk_slice);
                self.io_channel.add_write(
                    request.sector_offset,
                    request.sector_count,
                    backend_buf.clone(),
                    request.request_id,
                );
            }
            UblkOp::Flush => self.io_channel.add_flush(request.request_id),
            UblkOp::Unsupported => return Err(UblkIoError::Invalid),
        }

        Ok(())
    }

    fn complete_request(&mut self, request: &UblkIoRequest, success: bool) -> UblkIoResult<i32> {
        if !success {
            return Err(UblkIoError::Io);
        }

        let request_id = request.request_id;
        let backend_buf = &self.backend_bufs[request_id];
        let ublk_buf = &mut self.bufs[request_id];
        match request.op {
            UblkOp::Read => {
                let bytes = request.bytes;
                let backend_data = backend_buf.borrow();
                let backend_slice = &backend_data.as_slice()[..bytes];
                let ublk_slice = ublk_buf.subslice_mut(..bytes);
                ublk_slice.copy_from_slice(backend_slice);
                Ok(bytes as i32)
            }
            UblkOp::Write => Ok(request.bytes as i32),
            UblkOp::Flush => Ok(0),
            UblkOp::Unsupported => Err(UblkIoError::Invalid),
        }
    }

    fn process_pending_requests(&mut self, q: &UblkQueue) {
        while !self.pending_requests.is_empty() || self.io_channel.busy() {
            let mut queued = false;

            while let Some(request) = self.pending_requests.pop_front() {
                let tag = request.request_id;
                if let Err(err) = self.enqueue_request(&request) {
                    error!(
                        "UBLK IO error (op={:?}, sector_offset={}, sector_count={}): {:?}",
                        request.op, request.sector_offset, request.sector_count, err
                    );
                    let ublk_buf = &self.bufs[tag];
                    let completion_slice = BufDesc::Slice(ublk_buf.as_slice());
                    let _ = q.complete_io_cmd_unified(
                        tag as u16,
                        completion_slice,
                        Err(UblkError::InvalidVal),
                    );
                    continue;
                }
                self.inflight_requests[tag] = Some(request);
                queued = true;
            }

            if queued {
                if let Err(err) = self.io_channel.submit() {
                    error!("Failed to submit IO requests: {err}");
                    for (tag, slot) in self.inflight_requests.iter_mut().enumerate() {
                        if slot.take().is_some() {
                            let completion_slice = BufDesc::Slice(self.bufs[tag].as_slice());
                            let _ = q.complete_io_cmd_unified(
                                tag as u16,
                                completion_slice,
                                Err(UblkError::InvalidVal),
                            );
                        }
                    }
                    return;
                }
            }

            for (request_id, success) in self.io_channel.poll() {
                let Some(request) = self
                    .inflight_requests
                    .get_mut(request_id)
                    .and_then(|slot| slot.take())
                else {
                    error!("UBLK IO completion for unknown request_id: {request_id}");
                    continue;
                };

                let io_result = self.complete_request(&request, success);

                let completion = match io_result {
                    Ok(bytes) => Ok(UblkIORes::Result(bytes)),
                    Err(err) => {
                        error!(
                            "UBLK IO error (op={:?}, sector_offset={}, sector_count={}): {:?}",
                            request.op, request.sector_offset, request.sector_count, err
                        );
                        Err(UblkError::InvalidVal)
                    }
                };

                let completion_slice = BufDesc::Slice(self.bufs[request_id].as_slice());
                if let Err(err) =
                    q.complete_io_cmd_unified(request_id as u16, completion_slice, completion)
                {
                    error!("Failed to complete IO command: {err}");
                }
            }

            if self.pending_requests.is_empty() && self.io_channel.busy() {
                std::thread::yield_now();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::block_device::bdev_test::TestBlockDevice;
    use crate::block_device::BlockDevice;

    fn setup_handler(max_io_bytes: usize, queue_size: usize) -> (UblkIoHandler, TestBlockDevice) {
        let device = TestBlockDevice::new(4 * SECTOR_SIZE as u64);
        let io_channel = device.create_channel().unwrap();
        let bufs = (0..queue_size)
            .map(|_| IoBuf::<u8>::new(max_io_bytes))
            .collect();
        let handler = UblkIoHandler::new(1, max_io_bytes, io_channel, bufs, queue_size);
        (handler, device)
    }

    #[test]
    fn enqueue_read_and_write_requests() {
        let (mut handler, device) = setup_handler(SECTOR_SIZE, 1);
        let pattern = vec![0x5a; SECTOR_SIZE];

        device.write(0, &pattern, SECTOR_SIZE);
        let read_request = UblkIoRequest {
            op: UblkOp::Read,
            sector_offset: 0,
            sector_count: 1,
            request_id: 0,
            bytes: SECTOR_SIZE,
        };
        handler.enqueue_request(&read_request).unwrap();
        assert_eq!(
            &handler.backend_bufs[0].borrow().as_slice()[..SECTOR_SIZE],
            pattern.as_slice()
        );

        handler.bufs[0].as_mut_slice()[..SECTOR_SIZE].copy_from_slice(&pattern);
        let write_request = UblkIoRequest {
            op: UblkOp::Write,
            sector_offset: 0,
            sector_count: 1,
            request_id: 0,
            bytes: SECTOR_SIZE,
        };
        handler.enqueue_request(&write_request).unwrap();
        let mut out = vec![0u8; SECTOR_SIZE];
        device.read(0, &mut out, SECTOR_SIZE);
        assert_eq!(out, pattern);

        let metrics = device.metrics.read().unwrap();
        assert_eq!(metrics.reads, 1);
        assert_eq!(metrics.writes, 1);
    }

    #[test]
    fn complete_request_transfers_data() {
        let (mut handler, _device) = setup_handler(SECTOR_SIZE, 1);
        let pattern = vec![0xab; SECTOR_SIZE];

        handler.backend_bufs[0].borrow_mut().as_mut_slice()[..SECTOR_SIZE]
            .copy_from_slice(&pattern);
        let read_request = UblkIoRequest {
            op: UblkOp::Read,
            sector_offset: 0,
            sector_count: 1,
            request_id: 0,
            bytes: SECTOR_SIZE,
        };
        let bytes = handler.complete_request(&read_request, true).unwrap();
        assert_eq!(bytes, SECTOR_SIZE as i32);
        assert_eq!(
            &handler.bufs[0].as_slice()[..SECTOR_SIZE],
            pattern.as_slice()
        );

        let write_request = UblkIoRequest {
            op: UblkOp::Write,
            sector_offset: 0,
            sector_count: 1,
            request_id: 0,
            bytes: SECTOR_SIZE,
        };
        assert_eq!(
            handler.complete_request(&write_request, true).unwrap(),
            SECTOR_SIZE as i32
        );

        let flush_request = UblkIoRequest {
            op: UblkOp::Flush,
            sector_offset: 0,
            sector_count: 0,
            request_id: 0,
            bytes: 0,
        };
        assert_eq!(handler.complete_request(&flush_request, true).unwrap(), 0);
        assert!(matches!(
            handler.complete_request(&flush_request, false),
            Err(UblkIoError::Io)
        ));
    }

    #[test]
    fn enqueue_rejects_invalid_requests() {
        let (mut handler, _device) = setup_handler(SECTOR_SIZE, 1);
        let oversized_request = UblkIoRequest {
            op: UblkOp::Read,
            sector_offset: 0,
            sector_count: 1,
            request_id: 0,
            bytes: SECTOR_SIZE + 1,
        };
        assert!(matches!(
            handler.enqueue_request(&oversized_request),
            Err(UblkIoError::Invalid)
        ));

        let unsupported_request = UblkIoRequest {
            op: UblkOp::Unsupported,
            sector_offset: 0,
            sector_count: 1,
            request_id: 0,
            bytes: SECTOR_SIZE,
        };
        assert!(matches!(
            handler.enqueue_request(&unsupported_request),
            Err(UblkIoError::Invalid)
        ));
    }
}
