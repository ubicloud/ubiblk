use serde::{Deserialize, Serialize};
use virtio_bindings::{virtio_blk::*, virtio_config::*, virtio_ring::*};
use vm_memory::ByteValued;

#[derive(Copy, Clone, Debug, Default, Serialize, Deserialize)]
#[repr(C, packed)]
pub struct VirtioBlockConfig {
    pub capacity: u64,
    pub size_max: u32,
    pub seg_max: u32,
    pub geometry: VirtioBlockGeometry,
    pub blk_size: u32,
    pub physical_block_exp: u8,
    pub alignment_offset: u8,
    pub min_io_size: u16,
    pub opt_io_size: u32,
    pub writeback: u8,
    pub unused: u8,
    pub num_queues: u16,
    pub max_discard_sectors: u32,
    pub max_discard_seg: u32,
    pub discard_sector_alignment: u32,
    pub max_write_zeroes_sectors: u32,
    pub max_write_zeroes_seg: u32,
    pub write_zeroes_may_unmap: u8,
    pub unused1: [u8; 3],
}

#[derive(Copy, Clone, Debug, Default, Serialize, Deserialize)]
#[repr(C, packed)]
pub struct VirtioBlockGeometry {
    pub cylinders: u16,
    pub heads: u8,
    pub sectors: u8,
}

// Ensure VirtioBlockConfig is safe for ByteValued
unsafe impl ByteValued for VirtioBlockConfig {}

pub fn print_features(features: u64) {
    let all_features = [
        (VIRTIO_F_ACCESS_PLATFORM, "VIRTIO_F_ACCESS_PLATFORM"),
        (VIRTIO_F_ADMIN_VQ, "VIRTIO_F_ADMIN_VQ"),
        (VIRTIO_F_ANY_LAYOUT, "VIRTIO_F_ANY_LAYOUT"),
        (VIRTIO_F_IN_ORDER, "VIRTIO_F_IN_ORDER"),
        (VIRTIO_F_IOMMU_PLATFORM, "VIRTIO_F_IOMMU_PLATFORM"),
        (VIRTIO_F_NOTIFICATION_DATA, "VIRTIO_F_NOTIFICATION_DATA"),
        (VIRTIO_F_NOTIFY_ON_EMPTY, "VIRTIO_F_NOTIFY_ON_EMPTY"),
        (VIRTIO_F_NOTIF_CONFIG_DATA, "VIRTIO_F_NOTIF_CONFIG_DATA"),
        (VIRTIO_F_ORDER_PLATFORM, "VIRTIO_F_ORDER_PLATFORM"),
        (VIRTIO_F_RING_PACKED, "VIRTIO_F_RING_PACKED"),
        (VIRTIO_F_RING_RESET, "VIRTIO_F_RING_RESET"),
        (VIRTIO_F_SR_IOV, "VIRTIO_F_SR_IOV"),
        (VIRTIO_F_VERSION_1, "VIRTIO_F_VERSION_1"),
        (VIRTIO_BLK_F_BARRIER, "VIRTIO_BLK_F_BARRIER"),
        (VIRTIO_BLK_F_SIZE_MAX, "VIRTIO_BLK_F_SIZE_MAX"),
        (VIRTIO_BLK_F_SEG_MAX, "VIRTIO_BLK_F_SEG_MAX"),
        (VIRTIO_BLK_F_GEOMETRY, "VIRTIO_BLK_F_GEOMETRY"),
        (VIRTIO_BLK_F_RO, "VIRTIO_BLK_F_RO"),
        (VIRTIO_BLK_F_BLK_SIZE, "VIRTIO_BLK_F_BLK_SIZE"),
        (VIRTIO_BLK_F_SCSI, "VIRTIO_BLK_F_SCSI"),
        (VIRTIO_BLK_F_FLUSH, "VIRTIO_BLK_F_FLUSH"),
        (VIRTIO_BLK_F_TOPOLOGY, "VIRTIO_BLK_F_TOPOLOGY"),
        (VIRTIO_BLK_F_CONFIG_WCE, "VIRTIO_BLK_F_CONFIG_WCE"),
        (VIRTIO_BLK_F_MQ, "VIRTIO_BLK_F_MQ"),
        (VIRTIO_BLK_F_DISCARD, "VIRTIO_BLK_F_DISCARD"),
        (VIRTIO_BLK_F_WRITE_ZEROES, "VIRTIO_BLK_F_WRITE_ZEROES"),
        (VIRTIO_BLK_F_SECURE_ERASE, "VIRTIO_BLK_F_SECURE_ERASE"),
        (VIRTIO_RING_F_EVENT_IDX, "VIRTIO_RING_F_EVENT_IDX"),
        (VIRTIO_RING_F_INDIRECT_DESC, "VIRTIO_RING_F_INDIRECT_DESC"),
        (30, "VHOST_USER_F_PROTOCOL_FEATURES"),
    ];

    let mut remaining_features = features;
    let mut first = true;
    print!("Features (0x{:x}): ", features);
    for (feature, name) in all_features.iter() {
        if remaining_features & ((1 as u64) << *feature) != 0 {
            if !first {
                print!(" | ");
            }
            print!("{}", name);
            first = false;
            remaining_features &= !((1 as u64) << *feature);
        }
    }
    if remaining_features != 0 {
        if !first {
            print!(" | ");
        }
        print!("0x{:x}", remaining_features);
    }
    println!();
}
