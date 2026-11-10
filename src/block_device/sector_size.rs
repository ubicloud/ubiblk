use std::{
    fs::Metadata,
    os::unix::fs::{FileTypeExt, MetadataExt},
    path::Path,
};

use crate::{backends::SECTOR_SIZE, utils::aligned_buffer::BUFFER_ALIGNMENT, Result};

/// The logical sector size direct I/O on `path` has to be aligned to: that of
/// a block device, or of the device under a regular file.
pub fn detect_sector_size(path: &Path) -> Result<usize> {
    sector_size_of(&std::fs::metadata(path)?)
}

/// As `detect_sector_size`, for a file that is already open.
///
/// The kernel is asked about the block device rather than about the file.
/// What statx reports as a file's direct I/O alignment is up to the
/// filesystem and can be larger than a sector, or change as the file does,
/// while the sector size is what a guest's partition table depends on.
///
/// A file that is not on a block device the kernel describes, such as one on
/// a network filesystem, has 512-byte sectors.
pub fn sector_size_of(metadata: &Metadata) -> Result<usize> {
    let device = if metadata.file_type().is_block_device() {
        metadata.rdev()
    } else {
        metadata.dev()
    };
    let (major, minor) = (libc::major(device), libc::minor(device));
    let sysfs = format!("/sys/dev/block/{major}:{minor}");
    // A partition has no queue of its own; its disk is the parent directory.
    let Some(sector_size) = [
        format!("{sysfs}/queue/logical_block_size"),
        format!("{sysfs}/../queue/logical_block_size"),
    ]
    .iter()
    .find_map(|path| std::fs::read_to_string(path).ok()) else {
        return Ok(SECTOR_SIZE);
    };

    match sector_size.trim().parse::<usize>() {
        Ok(sector_size)
            if sector_size.is_power_of_two()
                && (SECTOR_SIZE..=BUFFER_ALIGNMENT).contains(&sector_size) =>
        {
            Ok(sector_size)
        }
        _ => Err(crate::ubiblk_error!(InvalidParameter {
            description: format!(
                "Unsupported sector size {} for block device {major}:{minor}",
                sector_size.trim()
            ),
        })),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_a_supported_sector_size_for_a_regular_file() {
        let file = tempfile::NamedTempFile::new().unwrap();
        let sector_size = detect_sector_size(file.path()).unwrap();
        assert!(sector_size.is_power_of_two());
        assert!((SECTOR_SIZE..=BUFFER_ALIGNMENT).contains(&sector_size));
        assert_eq!(
            sector_size_of(&file.as_file().metadata().unwrap()).unwrap(),
            sector_size
        );
    }

    #[test]
    fn a_file_on_no_block_device_has_512_byte_sectors() {
        // procfs is not backed by a block device.
        assert_eq!(
            detect_sector_size(Path::new("/proc/self/status")).unwrap(),
            SECTOR_SIZE
        );
    }

    #[test]
    fn fails_for_a_missing_path() {
        assert!(detect_sector_size(Path::new("/non/existent/path")).is_err());
    }
}
