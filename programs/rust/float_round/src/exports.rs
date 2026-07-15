fn naive_round(x: f32) -> f32 {
    let t = x.trunc();
    let frac = x - t;
    if frac >= 0.5f32 {
        t.ceil()
    } else if frac <= -0.5f32 {
        t.floor()
    } else {
        t
    }
}

fn opt_round(x: f32) -> f32 {
    x.round_ties_even()
}

#[unsafe(no_mangle)]
pub extern "C" fn check_round(x: f32) -> i32 {
    // Agree for non-half-integer inputs
    if naive_round(x) == opt_round(x) { 1 } else { 0 }
}