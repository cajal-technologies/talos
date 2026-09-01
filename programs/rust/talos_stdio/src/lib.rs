//! Rust I/O adapters and the allocator used by Talos Wasm stream programs.

use std::io::{BufReader, BufWriter, Read, Write};

#[cfg(target_arch = "wasm32")]
mod allocator {
    use core::alloc::{GlobalAlloc, Layout};
    use core::cell::UnsafeCell;
    use core::ptr;

    const WASM_PAGE_SIZE: usize = 65_536;

    /// Keep every individual allocation and the bump pointer in the range
    /// accepted by Rust's collection implementations.  In particular this
    /// makes the allocator's explicit OOM path run before `Vec` can take its
    /// separate capacity-overflow panic path on wasm32.
    const MAX_HEAP_END: usize = isize::MAX as usize;

    unsafe extern "C" {
        static __heap_base: u8;
    }

    #[link(wasm_import_module = "talos")]
    unsafe extern "C" {
        /// Terminal resource-exhaustion notification supplied by the host.
        ///
        /// This import is deliberately private to the allocator: application
        /// code cannot classify an arbitrary failure as OOM.
        fn oom();
    }

    #[cold]
    fn abort_oom() -> ! {
        unsafe { oom() };

        // The verified host contract says `talos.oom` traps.  Retain an
        // explicit terminal instruction for an incorrectly linked host that
        // returns anyway.
        core::arch::wasm32::unreachable()
    }

    /// A single-threaded bump allocator for the standalone Wasm programs.
    ///
    /// Allocations advance `next`, growing linear memory by whole Wasm pages
    /// when necessary. Deallocation deliberately does nothing.
    struct BumpAllocator {
        next: UnsafeCell<usize>,
    }

    // Talos programs currently execute as single-threaded Wasm instances.
    unsafe impl Sync for BumpAllocator {}

    unsafe impl GlobalAlloc for BumpAllocator {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            let next = unsafe { &mut *self.next.get() };
            let heap_base = ptr::addr_of!(__heap_base) as usize;
            let current = if *next == 0 { heap_base } else { *next };
            let Some(start) = current
                .checked_add(layout.align() - 1)
                .map(|address| address & !(layout.align() - 1))
            else {
                abort_oom();
            };
            let Some(end) = start.checked_add(layout.size()) else {
                abort_oom();
            };
            if end > MAX_HEAP_END {
                abort_oom();
            }

            let current_pages = core::arch::wasm32::memory_size::<0>();
            let required_pages = end.div_ceil(WASM_PAGE_SIZE);
            if required_pages > current_pages
                && core::arch::wasm32::memory_grow::<0>(required_pages - current_pages)
                    == usize::MAX
            {
                abort_oom();
            }

            *next = end;
            start as *mut u8
        }

        unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
    }

    #[global_allocator]
    static ALLOCATOR: BumpAllocator = BumpAllocator {
        next: UnsafeCell::new(0),
    };
}

mod sys {
    #[link(wasm_import_module = "stdio")]
    unsafe extern "C" {
        pub fn read(count: usize, buf: *mut u8) -> usize;
        pub fn write(count: usize, buf: *const u8);
    }
}

/// Read up to `buf.len()` bytes from the host input stream.
pub fn read(buf: &mut [u8]) -> usize {
    unsafe { sys::read(buf.len(), buf.as_mut_ptr()) }
}

/// Write all bytes in `buf` to the host output stream.
pub fn write(buf: &[u8]) {
    unsafe { sys::write(buf.len(), buf.as_ptr()) }
}

/// An unbuffered byte stream backed by Talos host imports.
pub struct ExtIO;

impl ExtIO {
    pub fn new() -> Self {
        Self
    }

    pub fn buffered() -> (BufReader<Self>, BufWriter<Self>) {
        let reader = BufReader::new(Self::new());
        let writer = BufWriter::new(Self::new());
        (reader, writer)
    }
}

impl Default for ExtIO {
    fn default() -> Self {
        Self::new()
    }
}

impl Read for ExtIO {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Ok(read(buf))
    }
}

impl Write for ExtIO {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        write(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
