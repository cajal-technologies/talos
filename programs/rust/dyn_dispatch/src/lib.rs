//! Smallest crate that compiles to wasm using `call_indirect` via a
//! `&dyn Trait` vtable. The exported `check(sel, x)` runs two
//! dispatchers on the same input — a dynamic one that goes through
//! `OPS[…].apply(x)` (compiles to `call_indirect`) and an obviously-
//! correct direct dispatch — and traps via `unreachable` iff they
//! disagree.

mod exports;

pub trait Op: Sync {
    fn apply(&self, x: i32) -> i32;
}

pub struct Add(pub i32);
impl Op for Add {
    fn apply(&self, x: i32) -> i32 {
        x.wrapping_add(self.0)
    }
}

pub struct Mul(pub i32);
impl Op for Mul {
    fn apply(&self, x: i32) -> i32 {
        x.wrapping_mul(self.0)
    }
}

/// Two trait objects of distinct concrete types in a single array,
/// forcing dynamic dispatch at the call site below.
pub static OPS: [&dyn Op; 2] = [&Add(1), &Mul(2)];

/// Dynamic dispatch through the vtable in `OPS`. With LTO on, the
/// compiler can't see the concrete type at the call site, so it must
/// emit `call_indirect (type N)` — exactly the wasm instruction we
/// want to exercise.
#[inline(never)]
fn dispatch_dyn(sel: i32, x: i32) -> i32 {
    let i = (sel.unsigned_abs() as usize) % OPS.len();
    OPS[i].apply(x)
}

/// Obviously-correct direct dispatch: pick the concrete impl with a
/// `match` and inline the body. Used as the reference oracle that
/// [`dispatch_dyn`] is checked against.
#[inline(never)]
fn dispatch_naive(sel: i32, x: i32) -> i32 {
    let i = (sel.unsigned_abs() as usize) % 2;
    if i == 0 {
        // `Add(1).apply(x)`
        x.wrapping_add(1)
    } else {
        // `Mul(2).apply(x)`
        x.wrapping_mul(2)
    }
}

fn trap() -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    unreachable!();
}

/// Run both dispatchers on `(sel, x)` and trap if they disagree.
///
/// The wasm export traps iff [`dispatch_dyn`] and [`dispatch_naive`]
/// disagree on some input; proving "this export never traps" therefore
/// proves the vtable dispatch agrees with the direct one on every
/// `(sel, x)`.
pub fn check(sel: i32, x: i32) {
    if dispatch_dyn(sel, x) != dispatch_naive(sel, x) {
        trap();
    }
}
