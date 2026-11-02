#[unsafe(no_mangle)]
pub extern "C" fn map_len() {
    crate::map_len();
}

#[unsafe(no_mangle)]
pub extern "C" fn map_get() {
    crate::map_get();
}

#[unsafe(no_mangle)]
pub extern "C" fn map_contains_key() {
    crate::map_contains_key();
}

#[unsafe(no_mangle)]
pub extern "C" fn map_insert() {
    crate::map_insert();
}

#[unsafe(no_mangle)]
pub extern "C" fn map_remove() {
    crate::map_remove();
}
