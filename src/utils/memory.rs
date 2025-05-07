use std::fs::{File, OpenOptions};
use std::io::{Error, ErrorKind, Result};
use std::os::fd::AsRawFd;
use std::os::unix::fs::OpenOptionsExt;

use std::{fs, io, path::Path, ptr};

/// Return the size of the huge‑page we can use:
/// * 2 MiB if any 2 MiB huge‑pages are free;
/// * otherwise 1 GiB if any 1 GiB huge‑pages are free;
/// * otherwise return an error.
fn pick_hugepage_size() -> io::Result<usize> {
    const HUGEPAGE_2M: &str = "/sys/kernel/mm/hugepages/hugepages-2048kB";
    const HUGEPAGE_1G: &str = "/sys/kernel/mm/hugepages/hugepages-1048576kB";

    fn has_free<P: AsRef<Path>>(dir: P) -> io::Result<bool> {
        let n: usize = fs::read_to_string(dir.as_ref().join("free_hugepages"))?
            .trim()
            .parse()
            .unwrap_or(0);
        Ok(n > 0)
    }

    if has_free(HUGEPAGE_2M)? {
        Ok(2 * 1024 * 1024) // 2 MiB
    } else if has_free(HUGEPAGE_1G)? {
        Ok(1024 * 1024 * 1024) // 1 GiB
    } else {
        Err(io::Error::new(
            io::ErrorKind::Other,
            "no huge‑pages available",
        ))
    }
}

/// Allocates shared memory using a hugepage file
///
/// # Returns
///
/// A tuple containing:
/// - File descriptor for the hugepage file
/// - Memory mapping as a raw pointer
/// - Size of the mapped memory
///
/// # Safety
///
/// This function is unsafe because it deals with memory mapping and raw pointers.
/// The caller is responsible for unmapping the memory when no longer needed.
pub fn allocate_hugepage_memory() -> Result<(File, *mut u8, usize)> {
    // Use a full hugepage
    let mem_size = pick_hugepage_size()?;

    // Open a file in the hugepage directory
    let hugepage_file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .mode(0o600)
        .open(Path::new("/dev/hugepages/vhost_memory"))?;

    // Resize the file to the required size
    hugepage_file.set_len(mem_size as u64)?;

    // Memory map the file
    let map = unsafe {
        libc::mmap(
            ptr::null_mut(),
            mem_size,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_SHARED,
            hugepage_file.as_raw_fd(),
            0,
        )
    };

    if map == libc::MAP_FAILED {
        return Err(Error::new(
            ErrorKind::Other,
            "Failed to map memory".to_string(),
        ));
    }

    println!("mmaped memfd");

    Ok((hugepage_file, map as *mut u8, mem_size))
}

/// Unmaps memory that was previously mapped with `allocate_hugepage_memory`
///
/// # Safety
///
/// This function is unsafe because it unmaps memory and there's no guarantee
/// that the pointer is valid or that the memory is not being used elsewhere.
pub unsafe fn unmap_memory(ptr: *mut u8, size: usize) -> Result<()> {
    let result = libc::munmap(ptr as *mut libc::c_void, size);

    if result == -1 {
        return Err(Error::new(
            ErrorKind::Other,
            "Failed to unmap memory".to_string(),
        ));
    }

    Ok(())
}

/// Example of how to use the memory allocation functions
pub fn example_usage() -> Result<()> {
    // Allocate memory
    let (_file, ptr, size) = allocate_hugepage_memory()?;

    // Use the memory...
    // For example, write something to it
    unsafe {
        let slice = std::slice::from_raw_parts_mut(ptr, size);
        // Write some data
        for i in 0..10 {
            slice[i] = i as u8;
        }
    }

    // When done, unmap the memory
    unsafe {
        unmap_memory(ptr, size)?;
    }

    // The file will be closed automatically when it goes out of scope

    Ok(())
}
