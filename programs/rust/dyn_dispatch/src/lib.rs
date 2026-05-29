//! Smallest crate that compiles to wasm using `call_indirect` via a
//! `&dyn Trait` vtable. A pair of `Op` implementations sits in a
//! `static` array of trait objects; the exported entry selects one by
//! a runtime index and dispatches `apply` through the vtable.
//!
//! With LTO on, the compiler can't see the concrete type at the call
//! site, so it must emit an indirect call — exactly the
//! `call_indirect (type N)` instruction we want to exercise.

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

/// Indirectly dispatches to `OPS[sel % 2].apply(x)`.
pub fn dispatch(sel: i32, x: i32) -> i32 {
    let i = (sel.unsigned_abs() as usize) % OPS.len();
    OPS[i].apply(x)
}
