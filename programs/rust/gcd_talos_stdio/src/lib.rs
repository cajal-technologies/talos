//! Minimal Talos stream adapter for the fixed-size GCD example.

use std::io::{Read, Write};

#[cfg(target_arch = "wasm32")]
mod allocator {
    use core::alloc::{GlobalAlloc, Layout};
    use core::cell::UnsafeCell;
    use core::ptr;

    unsafe extern "C" {
        static __heap_base: u8;
    }

    #[link(wasm_import_module = "talos")]
    unsafe extern "C" {
        fn oom();
    }

    #[cold]
    fn abort_oom() -> ! {
        unsafe { oom() };
        core::arch::wasm32::unreachable()
    }

    struct FixedBumpAllocator {
        next: UnsafeCell<usize>,
    }

    unsafe impl Sync for FixedBumpAllocator {}

    unsafe impl GlobalAlloc for FixedBumpAllocator {
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
            if end > isize::MAX as usize {
                abort_oom();
            }

            // This support crate is intentionally scoped to `gcd_stdio`: its
            // only allocation is sixteen bytes and the module starts with
            // seventeen pages, so no dynamic memory growth is required.
            *next = end;
            start as *mut u8
        }

        unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
    }

    #[global_allocator]
    static ALLOCATOR: FixedBumpAllocator = FixedBumpAllocator {
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

pub fn read(buf: &mut [u8]) -> usize {
    unsafe { sys::read(buf.len(), buf.as_mut_ptr()) }
}

pub fn write(buf: &[u8]) {
    unsafe { sys::write(buf.len(), buf.as_ptr()) }
}

pub struct ExtIO;

impl ExtIO {
    pub fn new() -> Self {
        Self
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
