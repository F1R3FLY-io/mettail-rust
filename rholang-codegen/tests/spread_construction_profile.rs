//! Allocation and protobuf-size ladder for compact subject-position channels.
//!
//! This is a separate integration-test binary so its counting allocator does
//! not weaken `rholang-codegen`'s production `#![forbid(unsafe_code)]` boundary.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::time::Instant;

use mettail_rholang_codegen::{spread_term_par, GroundTerm};
use prost::Message;

mod counting_alloc {
    use super::*;

    thread_local! {
        static ALLOCATIONS: Cell<usize> = const { Cell::new(0) };
        static BYTES: Cell<usize> = const { Cell::new(0) };
    }

    fn bump(bytes: usize) {
        let _ = ALLOCATIONS.try_with(|count| count.set(count.get() + 1));
        let _ = BYTES.try_with(|count| count.set(count.get() + bytes));
    }

    fn read() -> (usize, usize) {
        (
            ALLOCATIONS.try_with(Cell::get).unwrap_or(0),
            BYTES.try_with(Cell::get).unwrap_or(0),
        )
    }

    pub struct Counting;

    unsafe impl GlobalAlloc for Counting {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            bump(layout.size());
            unsafe { System.alloc(layout) }
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            unsafe { System.dealloc(ptr, layout) }
        }

        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
            bump(size);
            unsafe { System.realloc(ptr, layout, size) }
        }
    }

    pub fn measure<R>(f: impl FnOnce() -> R) -> (R, usize, usize) {
        let (allocations_before, bytes_before) = read();
        let result = f();
        let (allocations_after, bytes_after) = read();
        (result, allocations_after - allocations_before, bytes_after - bytes_before)
    }
}

#[global_allocator]
static ALLOCATOR: counting_alloc::Counting = counting_alloc::Counting;

fn unary_subject(depth: usize) -> GroundTerm {
    let mut subject = GroundTerm::nullary("leaf");
    for _ in 0..depth {
        subject = GroundTerm::new("n", vec![subject]);
    }
    subject
}

#[test]
fn doubling_depth_has_linear_construction_and_wire_growth() {
    drop(spread_term_par(&unary_subject(8), "profile-fp", "site0"));

    let mut previous = None;
    println!("depth,protobuf_bytes,allocations,allocated_bytes,elapsed_ns");
    for depth in [128usize, 256, 512, 1_024] {
        let subject = unary_subject(depth);
        let started = Instant::now();
        let (spread, allocations, allocated_bytes) =
            counting_alloc::measure(|| spread_term_par(&subject, "profile-fp", "site0"));
        let elapsed = started.elapsed();
        let protobuf_bytes = spread.encoded_len();
        println!(
            "{depth},{protobuf_bytes},{allocations},{allocated_bytes},{}",
            elapsed.as_nanos()
        );

        if let Some((previous_wire, previous_allocations, previous_bytes)) = previous {
            // Doubling a linear construction may cross one Vec capacity boundary,
            // so retain a small allocator-growth margin.  A quadratic absolute-
            // path implementation approaches 4x and fails every bound below.
            assert!(
                protobuf_bytes * 10 <= previous_wire * 23,
                "protobuf size grew faster than linearly"
            );
            assert!(
                allocations * 10 <= previous_allocations * 23,
                "allocation count grew faster than linearly"
            );
            assert!(
                allocated_bytes * 10 <= previous_bytes * 23,
                "allocated bytes grew faster than linearly"
            );
        }
        previous = Some((protobuf_bytes, allocations, allocated_bytes));
        drop(spread);
        drop(subject);
    }
}
