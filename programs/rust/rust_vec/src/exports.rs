#[unsafe(no_mangle)]
pub extern "C" fn vec_len() {
    crate::vec_len();
}

#[unsafe(no_mangle)]
pub extern "C" fn vec_push() {
    crate::vec_push();
}

#[unsafe(no_mangle)]
pub extern "C" fn vec_pop() {
    crate::vec_pop();
}

#[unsafe(no_mangle)]
pub extern "C" fn vec_get() {
    crate::vec_get();
}

#[unsafe(no_mangle)]
pub extern "C" fn vec_contains() {
    crate::vec_contains();
}

#[unsafe(no_mangle)]
pub extern "C" fn vec_sum32() {
    crate::vec_sum32();
}
