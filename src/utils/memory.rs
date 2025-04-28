use std::fs::{File, OpenOptions};
use std::io::{Error, ErrorKind, Result};
use std::os::fd::AsRawFd;
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;
use std::ptr;

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
    // Use a full 2MB hugepage
    let mem_size = 2 * 1024 * 1024;

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
