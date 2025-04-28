// This file is mostly based on cloud-hypervisor/block/src/lib.rs, which has
// the following copyright notice and license:
//
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright © 2020 Intel Corporation
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use std::result;

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
                println!("Missing head descriptor");
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
                println!("Only head descriptor present: request = {:?}", req);
            })?;

        if !desc.has_next() {
            status_desc = desc;
            // Only flush requests are allowed to skip the data descriptor.
            if req.request_type != RequestType::Flush {
                println!("Need a data descriptor: request = {:?}", req);
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
                        println!("DescriptorChain corrupted: request = {:?}", req);
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
