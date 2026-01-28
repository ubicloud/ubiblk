use std::cell::RefCell;
use std::rc::Rc;
use std::{ops::Deref, sync::RwLockWriteGuard};

use super::request::*;
#[cfg(test)]
use crate::backends::common::io_tracking::IoKind;
use crate::backends::common::io_tracking::IoTracker;
use crate::backends::SECTOR_SIZE;
use crate::block_device::IoChannel;
use crate::block_device::SharedBuffer;
use crate::config::DeviceConfig;
use crate::utils::aligned_buffer::AlignedBuf;
use crate::Result;

use libc::EFD_NONBLOCK;
use log::{error, info};
use nix::{
    sched::{sched_setaffinity, CpuSet},
    unistd::Pid,
};
use vhost_user_backend::{bitmap::BitmapMmapRegion, VringState};
use virtio_bindings::virtio_blk::*;
use virtio_queue::{DescriptorChain, QueueT};
use vm_memory::{
    Bytes, GuestAddress, GuestAddressSpace, GuestMemory, GuestMemoryAtomic, GuestMemoryLoadGuard,
};
use vmm_sys_util::eventfd::EventFd;

type GuestMemoryMmap = vm_memory::GuestMemoryMmap<BitmapMmapRegion>;
type Vring<'a> = RwLockWriteGuard<'a, VringState<GuestMemoryAtomic<GuestMemoryMmap>>>;
type DescChain = DescriptorChain<GuestMemoryLoadGuard<GuestMemoryMmap>>;

#[derive(Debug, Clone)]
struct RequestSlot {
    used: bool,
    request_type: RequestType,
    request_sector: u64,
    request_len: usize,
    buffer: SharedBuffer,
    len: usize,
    status_addr: GuestAddress,
    desc_chain: Option<DescChain>,
    data_descriptors: Vec<(GuestAddress, u32)>,
}

pub struct UbiBlkBackendThread {
    pub event_idx: bool,
    pub kill_evt: EventFd,
    mem: GuestMemoryAtomic<GuestMemoryMmap>,
    io_channel: Box<dyn IoChannel>,
    request_slots: Vec<RequestSlot>,
    device_id: String,
    alignment: usize,
    pin_attempted: bool,
    ios_pending_signal: bool,
    io_tracker: IoTracker,
}

impl UbiBlkBackendThread {
    /// Complete a descriptor chain that could not be parsed, without a status byte.
    fn complete_bad_chain(&mut self, vring: &mut Vring<'_>, desc_chain: &DescChain) {
        let mem = desc_chain.memory();
        if let Err(e) = vring
            .get_queue_mut()
            .add_used(mem, desc_chain.head_index(), 0)
        {
            error!("failed to add used descriptor: {e:?}");
        }
    }
    pub fn new(
        mem: GuestMemoryAtomic<GuestMemoryMmap>,
        io_channel: Box<dyn IoChannel>,
        config: &DeviceConfig,
        alignment: usize,
        io_tracker: IoTracker,
    ) -> Result<Self> {
        let buf_size = config.seg_count_max * config.seg_size_max;
        let request_slots: Vec<RequestSlot> = (0..config.queue_size)
            .map(|_| RequestSlot {
                used: false,
                request_type: RequestType::None,
                buffer: Rc::new(RefCell::new(AlignedBuf::new_with_alignment(
                    buf_size as usize,
                    alignment,
                ))),
                len: buf_size as usize,
                status_addr: GuestAddress(0),
                request_sector: 0,
                request_len: 0,
                desc_chain: None,
                data_descriptors: vec![],
            })
            .collect();

        let kill_evt = EventFd::new(EFD_NONBLOCK).map_err(|e| {
            error!("failed to create kill eventfd: {e:?}");
            crate::ubiblk_error!(ThreadCreation { source: e })
        })?;

        Ok(UbiBlkBackendThread {
            event_idx: false,
            kill_evt,
            mem,
            io_channel,
            request_slots,
            device_id: config.device_id.clone(),
            alignment,
            pin_attempted: false,
            ios_pending_signal: false,
            io_tracker,
        })
    }

    pub(crate) fn get_request_slot(
        &mut self,
        len: usize,
        request: &Request,
        desc_chain: &DescChain,
    ) -> usize {
        for i in 0..self.request_slots.len() {
            if self.request_slots[i].len >= len && !self.request_slots[i].used {
                let slot = &mut self.request_slots[i];
                slot.used = true;
                slot.request_type = request.request_type;
                slot.status_addr = request.status_addr;
                slot.desc_chain = Some(desc_chain.clone());
                slot.data_descriptors = request.data_descriptors.to_vec();
                slot.request_sector = request.sector;
                slot.request_len = len;
                return i;
            }
        }
        self.request_slots.push(RequestSlot {
            used: true,
            request_type: request.request_type,
            buffer: Rc::new(RefCell::new(AlignedBuf::new_with_alignment(
                len,
                self.alignment,
            ))),
            len,
            request_sector: request.sector,
            request_len: len,
            status_addr: request.status_addr,
            desc_chain: Some(desc_chain.clone()),
            data_descriptors: request.data_descriptors.to_vec(),
        });
        self.request_slots.len() - 1
    }

    pub(crate) fn put_request_slot(&mut self, idx: usize) {
        self.request_slots[idx].used = false;
        self.io_tracker.clear(idx);
    }

    pub(crate) fn pin_to_cpu(&mut self, cpu: usize) -> Result<bool> {
        if self.pin_attempted {
            return Ok(false);
        }
        // Mark that we have attempted to pin, regardless of success or failure
        self.pin_attempted = true;
        let mut set = CpuSet::new();
        if let Err(e) = set.set(cpu) {
            error!("failed to configure CPU set for cpu {cpu}: {e}");
            return Err(crate::ubiblk_error!(CpuPinning { source: e }));
        }
        if let Err(e) = sched_setaffinity(Pid::from_raw(0), &set) {
            error!("failed to pin thread to cpu {cpu}: {e}");
            Err(crate::ubiblk_error!(CpuPinning { source: e }))
        } else {
            let thread_id = std::thread::current().id();
            info!("pinned thread {thread_id:?} to cpu {cpu}");
            Ok(true)
        }
    }

    /// Complete a descriptor chain and write a status byte to guest memory.
    fn complete_io(
        &mut self,
        vring: &mut Vring<'_>,
        desc_chain: &DescChain,
        status_addr: GuestAddress,
        status: u8,
    ) {
        self.ios_pending_signal = true;
        let mem = desc_chain.memory();
        if let Err(e) = mem.write_obj(status, status_addr) {
            error!("failed to write status: {e:?}");
            return;
        }
        let ret = vring
            .get_queue_mut()
            .add_used(mem, desc_chain.head_index(), 0);
        if let Err(e) = ret {
            error!("failed to add used descriptor: {e:?}");
        }
    }

    fn write_to_guest(&self, req: &RequestSlot) -> Result<()> {
        let desc_chain = req
            .desc_chain
            .clone()
            .ok_or(crate::ubiblk_error!(ChannelError {
                reason: "request missing descriptor chain".to_string(),
            }))?;
        let mem = desc_chain.memory();
        let borrow = req.buffer.borrow();
        let buf = borrow.as_slice();
        let mut pos = 0;
        for (data_addr, data_len) in &req.data_descriptors {
            let mut buf_chunk = &buf[pos..pos + *data_len as usize];
            mem.read_exact_volatile_from(*data_addr, &mut buf_chunk, *data_len as usize)
                .map_err(|e| {
                    error!("read_exact_volatile_from failed: {e:?}");
                    crate::ubiblk_error!(GuestMemoryAccess { source: e })
                })?;
            pos += *data_len as usize;
        }

        Ok(())
    }

    /// Drain completed I/O, update guest buffers, and signal used descriptors.
    fn poll_io(&mut self, vring: &mut Vring<'_>) {
        let mut finished_reads = vec![];
        for (request_id, success) in self.io_channel.poll() {
            let req = &self.request_slots[request_id];
            let Some(desc_chain) = req.desc_chain.clone() else {
                error!("Request slot {request_id} missing desc_chain");
                continue;
            };
            let mut write_to_guest_failed = false;
            if req.request_type == RequestType::In && success {
                if self.write_to_guest(req).is_err() {
                    write_to_guest_failed = true;
                }
                finished_reads.push(request_id);
            }
            let status = if success && !write_to_guest_failed {
                VIRTIO_BLK_S_OK
            } else {
                VIRTIO_BLK_S_IOERR
            } as u8;
            self.complete_io(vring, &desc_chain, req.status_addr, status);
            self.put_request_slot(request_id);
        }
    }

    pub(crate) fn request_len(&self, request: &Request) -> usize {
        let mut len = 0;
        for (_, data_len) in &request.data_descriptors {
            len += *data_len;
        }
        len as usize
    }

    fn process_read(&mut self, request: &Request, desc_chain: &DescChain, vring: &mut Vring<'_>) {
        let len = self.request_len(request);
        if !len.is_multiple_of(SECTOR_SIZE) {
            error!("read request length is not a multiple of sector size: {len}");
            self.complete_io(
                vring,
                desc_chain,
                request.status_addr,
                VIRTIO_BLK_S_IOERR as u8,
            );
            return;
        }

        let id = self.get_request_slot(len, request, desc_chain);

        let sector_count = (len / SECTOR_SIZE) as u32;
        self.io_channel.add_read(
            request.sector,
            sector_count,
            self.request_slots[id].buffer.clone(),
            id,
        );
        self.io_tracker
            .add_read(id, request.sector, sector_count as u64);
    }

    fn process_write(&mut self, request: &Request, desc_chain: &DescChain, vring: &mut Vring<'_>) {
        let len = self.request_len(request);
        if !len.is_multiple_of(SECTOR_SIZE) {
            error!("write request length is not a multiple of sector size: {len}");
            self.complete_io(
                vring,
                desc_chain,
                request.status_addr,
                VIRTIO_BLK_S_IOERR as u8,
            );
            return;
        }

        let id = self.get_request_slot(len, request, desc_chain);
        let mem = desc_chain.memory();
        let mut pos: usize = 0;
        let mut read_from_guest_failed = false;
        for (data_addr, data_len) in &request.data_descriptors {
            let mut borrow = self.request_slots[id].buffer.borrow_mut();
            let buf = borrow.as_mut_slice();
            let mut dst = &mut buf[pos..pos + *data_len as usize];
            pos += *data_len as usize;
            let err = mem.write_all_volatile_to(*data_addr, &mut dst, *data_len as usize);
            if let Err(e) = err {
                error!("write_all_volatile_to failed: {e:?}");
                read_from_guest_failed = true;
            }
        }

        if read_from_guest_failed {
            self.complete_io(
                vring,
                desc_chain,
                request.status_addr,
                VIRTIO_BLK_S_IOERR as u8,
            );
            self.put_request_slot(id);
            return;
        }

        let sector_count = (len / SECTOR_SIZE) as u32;

        self.io_channel.add_write(
            request.sector,
            sector_count,
            self.request_slots[id].buffer.clone(),
            id,
        );
        self.io_tracker
            .add_write(id, request.sector, sector_count as u64);
    }

    pub(crate) fn process_flush(
        &mut self,
        request: &Request,
        desc_chain: &DescChain,
        _vring: &mut Vring<'_>,
    ) {
        let id = self.get_request_slot(0, request, desc_chain);
        self.io_channel.add_flush(id);
        self.io_tracker.add_flush(id);
    }

    pub(crate) fn process_get_device_id(
        &mut self,
        request: &Request,
        desc_chain: DescChain,
        vring: &mut Vring<'_>,
    ) {
        let (data_addr, data_len) = request.data_descriptors[0];
        let mem = desc_chain.memory();

        if data_len < VIRTIO_BLK_ID_BYTES {
            self.complete_io(
                vring,
                &desc_chain,
                request.status_addr,
                VIRTIO_BLK_S_IOERR as u8,
            );
            return;
        }

        let mut buf = [0u8; VIRTIO_BLK_ID_BYTES as usize];
        let serial_bytes = self.device_id.as_bytes();
        let copy_len = core::cmp::min(serial_bytes.len(), buf.len());
        buf[..copy_len].copy_from_slice(&serial_bytes[..copy_len]);

        let status = if mem.write_slice(&buf, data_addr).is_err() {
            VIRTIO_BLK_S_IOERR
        } else {
            VIRTIO_BLK_S_OK
        } as u8;
        self.complete_io(vring, &desc_chain, request.status_addr, status);
    }

    #[cfg(test)]
    pub(crate) fn io_tracker_snapshot(&self) -> Vec<(IoKind, u64, u64)> {
        self.io_tracker.snapshot()
    }

    /// Handle available requests and complete I/O, returning whether the queue is busy.
    pub fn process_queue(&mut self, vring: &mut Vring<'_>) -> bool {
        let mut busy = false;

        while let Some(mut desc_chain) = vring
            .get_queue_mut()
            .pop_descriptor_chain(self.mem.memory())
        {
            match Request::parse(&mut desc_chain) {
                Ok(request) => match request.request_type {
                    RequestType::In => self.process_read(&request, &desc_chain, vring),
                    RequestType::Out => self.process_write(&request, &desc_chain, vring),
                    RequestType::Flush => self.process_flush(&request, &desc_chain, vring),
                    RequestType::GetDeviceId => {
                        self.process_get_device_id(&request, desc_chain, vring)
                    }
                    RequestType::Unsupported(_) | RequestType::None => {
                        error!("unknown request type: {:?}", request.request_type);
                        self.complete_io(
                            vring,
                            &desc_chain,
                            request.status_addr,
                            VIRTIO_BLK_S_UNSUPP as u8,
                        );
                    }
                },
                Err(err) => {
                    error!("failed to parse available descriptor chain: {err:?}");
                    self.complete_bad_chain(vring, &desc_chain);
                }
            }
            busy = true;
        }
        self.io_channel.submit().unwrap_or_else(|e| {
            error!("failed to submit io channel: {e:?}");
        });
        self.poll_io(vring);
        busy = busy || self.io_channel.busy();

        let needs_signalling = if self.ios_pending_signal {
            if self.event_idx {
                match vring
                    .get_queue_mut()
                    .needs_notification(self.mem.memory().deref())
                {
                    Ok(need) => need,
                    Err(e) => {
                        error!("needs_notification failed: {e:?}");
                        true
                    }
                }
            } else {
                true
            }
        } else {
            false
        };

        if needs_signalling {
            if let Err(e) = vring.signal_used_queue() {
                error!("failed to signal used queue: {e:?}");
            }
            self.ios_pending_signal = false;
        }

        busy
    }
}

unsafe impl Sync for UbiBlkBackendThread {}
unsafe impl Send for UbiBlkBackendThread {}

mod backend_thread_tests;
