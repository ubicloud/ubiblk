use std::cell::RefCell;
use std::fs;
use std::io::Write;
use std::rc::Rc;
use std::{ops::Deref, sync::RwLockWriteGuard};

use super::Options;
use super::{request::*, SECTOR_SIZE};
use crate::block_device::IoChannel;
use crate::block_device::SharedBuffer;
use crate::{Error, Result};

use libc::EFD_NONBLOCK;
use log::error;
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
    io_debug_file: Option<fs::File>,
}

impl UbiBlkBackendThread {
    pub fn new(
        mem: GuestMemoryAtomic<GuestMemoryMmap>,
        io_channel: Box<dyn IoChannel>,
        options: &Options,
    ) -> Result<Self> {
        let buf_size = options.seg_count_max * options.seg_size_max;
        let request_slots: Vec<RequestSlot> = (0..options.queue_size)
            .map(|_| RequestSlot {
                used: false,
                request_type: RequestType::None,
                buffer: Rc::new(RefCell::new(vec![0; buf_size as usize])),
                len: buf_size as usize,
                status_addr: GuestAddress(0),
                request_sector: 0,
                request_len: 0,
                desc_chain: None,
                data_descriptors: vec![],
            })
            .collect();

        let kill_evt = EventFd::new(EFD_NONBLOCK).map_err(|e| {
            error!("failed to create kill eventfd: {:?}", e);
            Error::ThreadCreation
        })?;

        let io_debug_file = match options.io_debug_path {
            Some(ref path) => {
                let file = fs::OpenOptions::new()
                    .write(true)
                    .create(true)
                    .open(path)
                    .map_err(|e| {
                        error!("failed to open io debug file: {:?}", e);
                        Error::IoError
                    })?;
                Some(file)
            }
            None => None,
        };

        Ok(UbiBlkBackendThread {
            event_idx: false,
            kill_evt,
            mem,
            io_channel,
            request_slots,
            io_debug_file,
        })
    }

    fn get_request_slot(&mut self, len: usize, request: &Request, desc_chain: &DescChain) -> usize {
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
            buffer: Rc::new(RefCell::new(vec![0; len])),
            len,
            request_sector: request.sector,
            request_len: len,
            status_addr: request.status_addr,
            desc_chain: Some(desc_chain.clone()),
            data_descriptors: request.data_descriptors.to_vec(),
        });
        self.request_slots.len() - 1
    }

    fn put_request_slot(&mut self, idx: usize) {
        self.request_slots[idx].used = false;
    }

    fn complete_io(
        &mut self,
        vring: &mut Vring<'_>,
        desc_chain: &DescChain,
        status_addr: GuestAddress,
        status: u8,
    ) {
        let mem = desc_chain.memory();
        if let Err(e) = mem.write_obj(status, status_addr) {
            error!("failed to write status: {:?}", e);
            return;
        }
        let ret = vring
            .get_queue_mut()
            .add_used(mem, desc_chain.head_index(), 0);
        if let Err(e) = ret {
            error!("failed to add used descriptor: {:?}", e);
            return;
        }
    }

    fn write_to_guest(&self, req: &RequestSlot) -> Result<()> {
        let desc_chain = req.desc_chain.clone().unwrap();
        let mem = desc_chain.memory();
        let borrow = req.buffer.borrow();
        let buf = borrow.as_slice();
        let mut pos = 0;
        for (data_addr, data_len) in &req.data_descriptors {
            let mut buf_chunk = &buf[pos..pos + *data_len as usize];
            mem.read_exact_volatile_from(*data_addr, &mut buf_chunk, *data_len as usize)
                .map_err(|e| {
                    error!("read_exact_volatile_from failed: {:?}", e);
                    Error::GuestMemoryAccess
                })?;
            pos += *data_len as usize;
        }

        Ok(())
    }

    fn poll_io(&mut self, vring: &mut Vring<'_>) {
        let mut finished_reads = vec![];
        for (request_id, success) in self.io_channel.poll() {
            let req = &self.request_slots[request_id as usize];
            let desc_chain = req.desc_chain.clone().unwrap();
            let mut write_to_guest_failed = false;
            if req.request_type == RequestType::In && success {
                if let Err(_) = self.write_to_guest(req) {
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
            self.put_request_slot(request_id as usize);
        }

        self.io_debug_file.as_mut().map(|file| {
            for request_id in finished_reads {
                let req = &self.request_slots[request_id as usize];
                let borrow = req.buffer.borrow();
                let buf = borrow.as_slice();
                file.write_fmt(format_args!(
                    "READ\n{}\n{}\n{}\n",
                    req.request_sector,
                    req.request_len,
                    crate::utils::debug::encode_hex(buf, req.request_len)
                ))
                .unwrap_or_else(|e| {
                    error!("failed to write to io debug file: {:?}", e);
                });
                file.flush().unwrap_or_else(|e| {
                    error!("failed to flush io debug file: {:?}", e);
                });
            }
        });
    }

    fn request_len(&self, request: &Request) -> usize {
        let mut len = 0;
        for (_, data_len) in &request.data_descriptors {
            len += *data_len;
        }
        len as usize
    }

    fn process_read(&mut self, request: &Request, desc_chain: &DescChain, vring: &mut Vring<'_>) {
        let len = self.request_len(request);
        if len % SECTOR_SIZE != 0 {
            error!(
                "read request length is not a multiple of sector size: {}",
                len
            );
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
    }

    fn process_write(&mut self, request: &Request, desc_chain: &DescChain, vring: &mut Vring<'_>) {
        let len = self.request_len(request);
        if len % SECTOR_SIZE != 0 {
            error!(
                "write request length is not a multiple of sector size: {}",
                len
            );
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
                error!("write_all_volatile_to failed: {:?}", e);
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

        self.io_debug_file.as_mut().map(|file| {
            let borrow = self.request_slots[id].buffer.borrow();
            let buf = borrow.as_slice();
            file.write_fmt(format_args!(
                "WRITE\n{}\n{}\n{}\n",
                request.sector,
                len,
                crate::utils::debug::encode_hex(buf, len)
            ))
            .unwrap_or_else(|e| {
                error!("failed to write to io debug file: {:?}", e);
            });
            file.flush().unwrap_or_else(|e| {
                error!("failed to flush io debug file: {:?}", e);
            });
        });

        let sector_count = (len / SECTOR_SIZE) as u32;

        self.io_channel.add_write(
            request.sector,
            sector_count,
            self.request_slots[id].buffer.clone(),
            id,
        );
    }

    fn process_flush(&mut self, request: &Request, desc_chain: &DescChain) {
        let id = self.get_request_slot(0, request, desc_chain);
        self.io_channel.add_flush(id);
    }

    fn process_get_device_id(
        &mut self,
        request: &Request,
        desc_chain: DescChain,
        vring: &mut Vring<'_>,
    ) {
        let (data_addr, _) = request.data_descriptors[0];
        let serial = "some_id";
        let mem = desc_chain.memory();
        let status = if let Err(_) = mem.write_slice(serial.as_bytes(), data_addr) {
            VIRTIO_BLK_S_IOERR
        } else {
            VIRTIO_BLK_S_OK
        } as u8;
        self.complete_io(vring, &desc_chain, request.status_addr, status);
    }

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
                    RequestType::Flush => self.process_flush(&request, &desc_chain),
                    RequestType::GetDeviceId => {
                        self.process_get_device_id(&request, desc_chain, vring)
                    }
                    _ => {
                        error!("unknown request type: {:?}", request.request_type);
                    }
                },
                Err(err) => {
                    error!("failed to parse available descriptor chain: {:?}", err);
                }
            }
            busy = true;
        }
        self.io_channel.submit().unwrap_or_else(|e| {
            error!("failed to submit io channel: {:?}", e);
        });
        self.poll_io(vring);
        busy = busy || self.io_channel.busy();

        let mut needs_signalling = false;
        if self.event_idx {
            if vring
                .get_queue_mut()
                .needs_notification(self.mem.memory().deref())
                .unwrap()
            {
                needs_signalling = true;
            }
        } else {
            needs_signalling = true;
        }

        if needs_signalling {
            vring.signal_used_queue().unwrap();
        }

        busy
    }
}

unsafe impl Sync for UbiBlkBackendThread {}
unsafe impl Send for UbiBlkBackendThread {}
