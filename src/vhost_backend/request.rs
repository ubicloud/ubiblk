// This file is mostly based on cloud-hypervisor/block/src/lib.rs, which has
// the following copyright notice and license:
//
// > Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// >
// > Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// > Use of this source code is governed by a BSD-style license that can be
// > found in the LICENSE-BSD-3-Clause file.
// >
// > Copyright © 2020 Intel Corporation
// >
// > SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause
//
// You can find CloudHypervisor's code at
// https://github.com/cloud-hypervisor/cloud-hypervisor

use std::result;

use log::error;
use smallvec::SmallVec;
use thiserror::Error;
use virtio_bindings::virtio_blk::*;
use virtio_queue::DescriptorChain;
use vm_memory::{
    bitmap::Bitmap, Bytes, GuestAddress, GuestMemory, GuestMemoryError, GuestMemoryLoadGuard,
};

#[derive(Error, Debug)]
pub enum Error {
    #[error("Guest gave us bad memory addresses")]
    GuestMemory(GuestMemoryError),
    #[error("Guest gave us offsets that would have overflowed a usize")]
    CheckedOffset(GuestAddress, usize),
    #[error("Guest gave us a write only descriptor that protocol says to read from")]
    UnexpectedWriteOnlyDescriptor,
    #[error("Guest gave us a read only descriptor that protocol says to write to")]
    UnexpectedReadOnlyDescriptor,
    #[error("Guest gave us too few descriptors in a descriptor chain")]
    DescriptorChainTooShort,
    #[error("Guest gave us a descriptor that was too short to use")]
    DescriptorLengthTooSmall,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RequestType {
    None,
    In,
    Out,
    Flush,
    GetDeviceId,
    Unsupported(u32),
}

fn request_type<B: Bitmap + 'static>(
    mem: &vm_memory::GuestMemoryMmap<B>,
    desc_addr: GuestAddress,
) -> result::Result<RequestType, Error> {
    let type_ = mem.read_obj(desc_addr).map_err(Error::GuestMemory)?;
    match type_ {
        VIRTIO_BLK_T_IN => Ok(RequestType::In),
        VIRTIO_BLK_T_OUT => Ok(RequestType::Out),
        VIRTIO_BLK_T_FLUSH => Ok(RequestType::Flush),
        VIRTIO_BLK_T_GET_ID => Ok(RequestType::GetDeviceId),
        t => Ok(RequestType::Unsupported(t)),
    }
}

fn sector<B: Bitmap + 'static>(
    mem: &vm_memory::GuestMemoryMmap<B>,
    desc_addr: GuestAddress,
) -> result::Result<u64, Error> {
    const SECTOR_OFFSET: usize = 8;
    let addr = match mem.checked_offset(desc_addr, SECTOR_OFFSET) {
        Some(v) => v,
        None => return Err(Error::CheckedOffset(desc_addr, SECTOR_OFFSET)),
    };

    mem.read_obj(addr).map_err(Error::GuestMemory)
}

const DEFAULT_DESCRIPTOR_VEC_SIZE: usize = 32;

#[derive(Debug, Clone)]
pub struct Request {
    pub request_type: RequestType,
    pub sector: u64,
    pub data_descriptors: SmallVec<[(GuestAddress, u32); DEFAULT_DESCRIPTOR_VEC_SIZE]>,
    pub status_addr: GuestAddress,
}

impl Request {
    pub fn parse<B: Bitmap + 'static>(
        desc_chain: &mut DescriptorChain<GuestMemoryLoadGuard<vm_memory::GuestMemoryMmap<B>>>,
    ) -> result::Result<Request, Error> {
        let hdr_desc = desc_chain
            .next()
            .ok_or(Error::DescriptorChainTooShort)
            .inspect_err(|_| {
                error!("Missing head descriptor");
            })?;

        // The head contains the request type which MUST be readable.
        if hdr_desc.is_write_only() {
            return Err(Error::UnexpectedWriteOnlyDescriptor);
        }

        let hdr_desc_addr = hdr_desc.addr();

        let mut req = Request {
            request_type: request_type(desc_chain.memory(), hdr_desc_addr)?,
            sector: sector(desc_chain.memory(), hdr_desc_addr)?,
            data_descriptors: SmallVec::with_capacity(DEFAULT_DESCRIPTOR_VEC_SIZE),
            status_addr: GuestAddress(0),
        };

        let status_desc;
        let mut desc = desc_chain
            .next()
            .ok_or(Error::DescriptorChainTooShort)
            .inspect_err(|_| {
                error!("Only head descriptor present: request = {:?}", req);
            })?;

        if !desc.has_next() {
            status_desc = desc;
            // Only flush requests are allowed to skip the data descriptor.
            if req.request_type != RequestType::Flush {
                error!("Need a data descriptor: request = {:?}", req);
                return Err(Error::DescriptorChainTooShort);
            }
        } else {
            req.data_descriptors.reserve_exact(1);
            while desc.has_next() {
                if desc.is_write_only() && req.request_type == RequestType::Out {
                    return Err(Error::UnexpectedWriteOnlyDescriptor);
                }
                if !desc.is_write_only() && req.request_type == RequestType::In {
                    return Err(Error::UnexpectedReadOnlyDescriptor);
                }
                if !desc.is_write_only() && req.request_type == RequestType::GetDeviceId {
                    return Err(Error::UnexpectedReadOnlyDescriptor);
                }

                req.data_descriptors.push((desc.addr(), desc.len()));
                desc = desc_chain
                    .next()
                    .ok_or(Error::DescriptorChainTooShort)
                    .inspect_err(|_| {
                        error!("DescriptorChain corrupted: request = {:?}", req);
                    })?;
            }
            status_desc = desc;
        }

        // The status MUST always be writable.
        if !status_desc.is_write_only() {
            return Err(Error::UnexpectedReadOnlyDescriptor);
        }

        if status_desc.len() < 1 {
            return Err(Error::DescriptorLengthTooSmall);
        }

        req.status_addr = status_desc.addr();

        Ok(req)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use virtio_bindings::bindings::virtio_ring::{VRING_DESC_F_NEXT, VRING_DESC_F_WRITE};
    use virtio_queue::desc::split::Descriptor as SplitDescriptor;
    use virtio_queue::{Queue, QueueOwnedT};
    use vm_memory::{Address, GuestAddress, GuestAddressSpace, GuestMemoryAtomic, GuestMemoryMmap};

    type GuestMemory = GuestMemoryMmap<()>;

    fn setup_mem() -> (GuestMemoryAtomic<GuestMemory>, GuestMemory) {
        let mem = GuestMemory::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let gm = GuestMemoryAtomic::new(mem.clone());
        (gm, mem)
    }

    fn build_chain(
        mem: &GuestMemory,
        descs: &[SplitDescriptor],
    ) -> DescriptorChain<GuestMemoryLoadGuard<GuestMemory>> {
        use virtio_queue::desc::RawDescriptor;
        use virtio_queue::mock::MockSplitQueue;

        let vq = MockSplitQueue::new(mem, 16);
        let raw_descs: Vec<RawDescriptor> =
            descs.iter().cloned().map(RawDescriptor::from).collect();
        vq.add_desc_chains(&raw_descs, 0).unwrap();
        let mut queue: Queue = vq.create_queue().unwrap();
        let atomic = GuestMemoryAtomic::new(mem.clone());
        let mut iter = queue.iter(atomic.memory()).unwrap();
        iter.next().unwrap()
    }

    #[test]
    fn test_request_type_sector() {
        let (gm, mem) = setup_mem();
        let addr = GuestAddress(0x1000);
        mem.write_obj::<u32>(VIRTIO_BLK_T_IN, addr).unwrap();
        mem.write_obj::<u32>(0, addr.unchecked_add(4)).unwrap();
        mem.write_obj::<u64>(0x55, addr.unchecked_add(8)).unwrap();

        let guard = gm.memory();
        assert_eq!(request_type(&*guard, addr).unwrap(), RequestType::In);
        assert_eq!(sector(&*guard, addr).unwrap(), 0x55);
        mem.write_obj::<u32>(0xdead, addr).unwrap();
        let guard = gm.memory();
        assert_eq!(
            request_type(&*guard, addr).unwrap(),
            RequestType::Unsupported(0xdead)
        );
    }

    #[test]
    fn test_parse_out_in_flush() {
        let (_gm, mem) = setup_mem();
        let hdr = GuestAddress(0x1000);
        let data = GuestAddress(0x2000);
        let status = GuestAddress(0x3000);

        // OUT request
        mem.write_obj::<u32>(VIRTIO_BLK_T_OUT, hdr).unwrap();
        mem.write_obj::<u32>(0, hdr.unchecked_add(4)).unwrap();
        mem.write_obj::<u64>(1, hdr.unchecked_add(8)).unwrap();
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(data.0, 512, VRING_DESC_F_NEXT as u16, 2),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_WRITE as u16, 0),
        ];
        let mut chain = build_chain(&mem, &descs);
        let req = Request::parse(&mut chain).unwrap();
        assert_eq!(req.request_type, RequestType::Out);
        assert_eq!(req.sector, 1);
        assert_eq!(req.data_descriptors.len(), 1);

        // IN request
        mem.write_obj::<u32>(VIRTIO_BLK_T_IN, hdr).unwrap();
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(
                data.0,
                512,
                VRING_DESC_F_WRITE as u16 | VRING_DESC_F_NEXT as u16,
                2,
            ),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_WRITE as u16, 0),
        ];
        let mut chain = build_chain(&mem, &descs);
        let req = Request::parse(&mut chain).unwrap();
        assert_eq!(req.request_type, RequestType::In);

        // FLUSH request (no data descriptor)
        mem.write_obj::<u32>(VIRTIO_BLK_T_FLUSH, hdr).unwrap();
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_WRITE as u16, 0),
        ];
        let mut chain = build_chain(&mem, &descs);
        let req = Request::parse(&mut chain).unwrap();
        assert_eq!(req.request_type, RequestType::Flush);
    }

    #[test]
    fn test_parse_errors() {
        let (_gm, mem) = setup_mem();
        let hdr = GuestAddress(0x4000);
        let data = GuestAddress(0x5000);
        let status = GuestAddress(0x6000);

        // write only header
        mem.write_obj::<u32>(VIRTIO_BLK_T_OUT, hdr).unwrap();
        mem.write_obj::<u64>(0, hdr.unchecked_add(8)).unwrap();
        let descs = [
            SplitDescriptor::new(
                hdr.0,
                16,
                VRING_DESC_F_WRITE as u16 | VRING_DESC_F_NEXT as u16,
                1,
            ),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_WRITE as u16, 0),
        ];
        let mut chain = build_chain(&mem, &descs);
        assert!(matches!(
            Request::parse(&mut chain),
            Err(Error::UnexpectedWriteOnlyDescriptor)
        ));

        // missing data descriptor for OUT
        mem.write_obj::<u32>(VIRTIO_BLK_T_OUT, hdr).unwrap();
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_WRITE as u16, 0),
        ];
        let mut chain = build_chain(&mem, &descs);
        assert!(matches!(
            Request::parse(&mut chain),
            Err(Error::DescriptorChainTooShort)
        ));

        // unexpected write-only data descriptor for OUT
        mem.write_obj::<u32>(VIRTIO_BLK_T_OUT, hdr).unwrap();
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(
                data.0,
                512,
                VRING_DESC_F_WRITE as u16 | VRING_DESC_F_NEXT as u16,
                2,
            ),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_WRITE as u16, 0),
        ];
        let mut chain = build_chain(&mem, &descs);
        assert!(matches!(
            Request::parse(&mut chain),
            Err(Error::UnexpectedWriteOnlyDescriptor)
        ));

        // unexpected read-only data descriptor for IN
        mem.write_obj::<u32>(VIRTIO_BLK_T_IN, hdr).unwrap();
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(data.0, 512, VRING_DESC_F_NEXT as u16, 2),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_WRITE as u16, 0),
        ];
        let mut chain = build_chain(&mem, &descs);
        assert!(matches!(
            Request::parse(&mut chain),
            Err(Error::UnexpectedReadOnlyDescriptor)
        ));

        // status not write only
        mem.write_obj::<u32>(VIRTIO_BLK_T_IN, hdr).unwrap();
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(
                data.0,
                512,
                VRING_DESC_F_WRITE as u16 | VRING_DESC_F_NEXT as u16,
                2,
            ),
            SplitDescriptor::new(status.0, 1, VRING_DESC_F_NEXT as u16, 0),
        ];
        let mut chain = build_chain(&mem, &descs);
        assert!(matches!(
            Request::parse(&mut chain),
            Err(Error::UnexpectedReadOnlyDescriptor)
        ));

        // status len too small
        mem.write_obj::<u32>(VIRTIO_BLK_T_IN, hdr).unwrap();
        let descs = [
            SplitDescriptor::new(hdr.0, 16, VRING_DESC_F_NEXT as u16, 1),
            SplitDescriptor::new(
                data.0,
                512,
                VRING_DESC_F_WRITE as u16 | VRING_DESC_F_NEXT as u16,
                2,
            ),
            SplitDescriptor::new(status.0, 0, VRING_DESC_F_WRITE as u16, 0),
        ];
        let mut chain = build_chain(&mem, &descs);
        assert!(matches!(
            Request::parse(&mut chain),
            Err(Error::DescriptorLengthTooSmall)
        ));
    }
}
