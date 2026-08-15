pub mod exports;

fn merge<T: Ord + Clone>(left: &[T], right: &[T], merged: &mut [T]) {
    let mut i = 0;
    let mut j = 0;
    let mut k = 0;
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            merged[k] = left[i].clone();
            i += 1;
            k += 1;
        } else {
            merged[k] = right[j].clone();
            j += 1;
            k += 1;
        }
    }
    while i < left.len() {
        merged[k] = left[i].clone();
        i += 1;
        k += 1;
    }
    while j < right.len() {
        merged[k] = right[j].clone();
        j += 1;
        k += 1;
    }
}

pub fn mergesort<T: Ord + Clone>(arr: &mut [T], scratch: &mut [T]) {
    let len = arr.len();
    if len <= 1 {
        return;
    }
    let mid = len / 2;
    mergesort(&mut arr[..mid], &mut scratch[..mid]);
    mergesort(&mut arr[mid..], &mut scratch[mid..]);
    let (left, right) = arr.split_at(mid);
    merge(left, right, scratch);
    arr.clone_from_slice(scratch);
}
