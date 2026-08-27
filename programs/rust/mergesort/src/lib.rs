pub mod exports;

fn merge(left: &[u32], right: &[u32], merged: &mut [u32]) {
    let mut i = 0;
    let mut j = 0;
    let mut k = 0;
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            merged[k] = left[i];
            i += 1;
            k += 1;
        } else {
            merged[k] = right[j];
            j += 1;
            k += 1;
        }
    }
    while i < left.len() {
        merged[k] = left[i];
        i += 1;
        k += 1;
    }
    while j < right.len() {
        merged[k] = right[j];
        j += 1;
        k += 1;
    }
}

pub fn mergesort(arr: &mut [u32], scratch: &mut [u32]) {
    let len = arr.len();
    if len <= 1 {
        return;
    }
    let mid = len / 2;
    mergesort(&mut arr[..mid], &mut scratch[..mid]);
    mergesort(&mut arr[mid..], &mut scratch[mid..]);
    let (left, right) = arr.split_at(mid);
    merge(left, right, scratch);
    arr.copy_from_slice(scratch);
}

#[cfg(test)]
mod tests {
    #[test]
    fn sorts_u32_values() {
        let mut values = [9, 1, u32::MAX, 1, 4, 0];
        let mut scratch = [0; 6];

        super::mergesort(&mut values, &mut scratch);

        assert_eq!(values, [0, 1, 1, 4, 9, u32::MAX]);
    }
}
