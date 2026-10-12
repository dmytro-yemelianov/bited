//! Counts allocations on the calling thread while exercising every public family.
use bited::*;
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::hint::black_box;

struct CountingAllocator;
thread_local! {
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
    static COUNT: Cell<usize> = const { Cell::new(0) };
}
fn record() {
    ACTIVE.with(|active| {
        if active.get() {
            COUNT.with(|count| count.set(count.get() + 1));
        }
    });
}
// The library forbids unsafe code. Only this test delegates to the system allocator.
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record();
        unsafe { System.alloc(layout) }
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        record();
        unsafe { System.alloc_zeroed(layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        record();
        unsafe { System.realloc(ptr, layout, size) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}
#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

#[test]
fn all_public_families_allocate_zero_times() {
    COUNT.with(|count| count.set(0));
    ACTIVE.with(|active| active.set(true));
    let mut buffer = [0xa5; 16];
    for value in [0, 1, 127, 128, u32::MAX as u64, u64::MAX] {
        let value = black_box(value);
        black_box(encoded_len_u64(value));
        black_box(encoded_len_u32(value as u32));
        black_box(encoded_len_i64(value as i64));
        black_box(encoded_len_i32(value as i32));
        let e64 = encode_u64(value);
        let e32 = encode_u32(value as u32);
        let s64 = encode_i64(value as i64);
        let s32 = encode_i32(value as i32);
        black_box((e64.len(), e64.is_empty(), e32.len(), e32.is_empty()));
        black_box(zigzag_i64_to_u64(zigzag_u64_to_i64(value)));
        black_box(zigzag_i32_to_u32(zigzag_u32_to_i32(value as u32)));
        for capacity in [0, 1, 4, 5, 9, 10, 16] {
            let _ = black_box(encode_u64_into(value, &mut buffer[..capacity]));
            let _ = black_box(encode_u32_into(value as u32, &mut buffer[..capacity]));
            let _ = black_box(encode_i64_into(value as i64, &mut buffer[..capacity]));
            let _ = black_box(encode_i32_into(value as i32, &mut buffer[..capacity]));
        }
        for policy in [DecodePolicy::Canonical, DecodePolicy::BoundedNonCanonical] {
            let _ = black_box(decode_u64(e64.as_bytes(), policy));
            let _ = black_box(decode_u32(e32.as_bytes(), policy));
            let _ = black_box(decode_i64(s64.as_bytes(), policy));
            let _ = black_box(decode_i32(s32.as_bytes(), policy));
            let _ = black_box(decode_u64_exact(e64.as_bytes(), policy));
            let _ = black_box(decode_u32_exact(e32.as_bytes(), policy));
            let _ = black_box(decode_i64_exact(s64.as_bytes(), policy));
            let _ = black_box(decode_i32_exact(s32.as_bytes(), policy));
            let mut d64 = DecoderU64::new(policy);
            let mut d32 = DecoderU32::new(policy);
            for byte in [0xff; 12] {
                black_box(d64.push(byte));
                black_box(d32.push(byte));
                black_box((d64.bytes_seen(), d32.bytes_seen()));
            }
            let _ = black_box(d64.finish());
            let _ = black_box(d32.finish());
            d64.reset(policy);
            d32.reset(policy);
            let _ = black_box(d64.finish());
            let _ = black_box(d32.finish());
        }
    }
    ACTIVE.with(|active| active.set(false));
    assert_eq!(COUNT.with(Cell::get), 0);
    println!(
        "state sizes: DecoderU32={}, DecoderU64={}, Encoded32={}, Encoded64={}; allocations=0",
        std::mem::size_of::<DecoderU32>(),
        std::mem::size_of::<DecoderU64>(),
        std::mem::size_of::<Encoded32>(),
        std::mem::size_of::<Encoded64>()
    );
}
