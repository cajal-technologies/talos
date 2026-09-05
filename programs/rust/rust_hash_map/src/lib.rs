//! `HashMap` access patterns over the Talos stdio byte stream.
//!
//! Every export reads one [borsh](https://borsh.io/) value from standard
//! input, applies one map operation, and writes one borsh value back. The
//! interface is functional: an export that changes the map writes the changed
//! map, and an export that also produces a value writes the value beside it.
//! An export that only observes writes the observation alone. Tuple inputs
//! carry the scalars first: a borsh tuple has no framing, and fixed-width
//! leading fields let the reader split at byte four and byte eight.
//!
//! Borsh gives a map a canonical encoding: a `u32` entry count, then the
//! entries sorted by key. A `HashMap` has no order of its own, so the sort is
//! what gives one map one byte string, and a contract can then name the exact
//! bytes an export writes.
//!
//! The map crosses the wire as a `Vec<(u32, u32)>` rather than through borsh's
//! own `HashMap` impl. Borsh gates that impl behind its `std` feature, the
//! verifier builds the whole workspace in one cargo call, and cargo gives a
//! shared dependency one feature set across every member, so a feature here
//! would also change the module that `rust_vec` emits. The bytes are the same
//! either way: borsh's impl sorts the entries by key and writes them through
//! this same `Vec` encoding, and it reads them back as a pair list and
//! collects it. `sorted_entries` and `collect_entries` below are those two
//! steps. Borsh's own reader also rejects keys that do not ascend under the
//! non-default `de_strict_order` feature, which this crate neither enables nor
//! goes through.
//!
//! `borsh::from_slice` rejects trailing bytes, so each export accepts exactly
//! one encoded value and writes nothing otherwise. Empty input is rejected
//! too: borsh encodes an empty map as four zero bytes. Nothing in this crate
//! indexes with `[]`.
//!
//! A panic is not an outcome the contracts allow. This module imports only
//! `stdio.read`, `stdio.write` and `talos.oom`. A panic therefore traps, and
//! that trap is neither a normal return nor the OOM outcome. Three panic
//! paths are new here against `rust_vec`. They are the whole set: the panic
//! messages this module carries and `rust_vec` does not are exactly these
//! three. The rest of the string difference between the two modules is source
//! paths and the export names. The three paragraphs below give the reason each
//! one cannot run.
//!
//! The sort compares `u32` keys under `u32` ordering, which is a total order.
//! The check for a bad comparison function never fires.
//!
//! The default hasher takes its seed from a lazy thread-local. That storage
//! reports an error only during thread teardown. This module runs as one
//! single-shot instance and tears down no thread.
//!
//! `collect_entries` builds the table from a pair list that is already in
//! memory. Each wire pair costs eight bytes, so the input bounds the capacity
//! the table asks for. The bump allocator in `talos_stdio` caps the heap at
//! `MAX_HEAP_END`, which is `isize::MAX`, and raises `talos.oom` at that cap.
//! The capacity therefore stays below the overflow arithmetic in the table.
//! This last argument is stated, not proved: no test reaches the cap, and a
//! test that did would need a two gigabyte input.
//!
//! A repeated key on the wire is not a rejection. The reader collects a pair
//! list, so the last value of a repeated key wins and the map can hold fewer
//! entries than the wire count states.

mod exports;

use std::collections::HashMap;
use talos_stdio::{read, write};

/// The one map type every export works on.
type Map = HashMap<u32, u32>;

/// The wire form of a map: one pair per entry, in the order written.
type Entries = Vec<(u32, u32)>;

/// Read the whole input stream, one `push` per byte. `take` saturates if the
/// host ever reports more than the buffer holds, and it keeps `[]` indexing
/// out of the crate.
fn read_all() -> Vec<u8> {
    let mut data: Vec<u8> = Vec::new();
    let mut chunk = [0u8; 256];
    loop {
        let count = read(&mut chunk);
        if count == 0 {
            return data;
        }
        for &byte in chunk.iter().take(count) {
            data.push(byte);
        }
    }
}

/// Write one borsh value. `to_vec` cannot fail here: it writes into a
/// `Vec<u8>`, whose `Write` is infallible, and its one error path, a length
/// above `u32::MAX`, is unreachable on wasm32. The `if let` keeps a panic path
/// out of the module.
fn reply<T: borsh::BorshSerialize>(value: &T) {
    if let Ok(output) = borsh::to_vec(value) {
        write(&output);
    }
}

// Each helper and kernel below stays out of line so that it is its own wasm
// function, separate from the stream driver, the decoder, allocation, and
// host I/O.

/// The entries of a map, sorted by key. A `HashMap` iterates in whatever order
/// the hash function left, so the sort is what makes the encoding depend on
/// the content alone. This is the step borsh's own map serializer performs.
///
/// The sort is the unstable one. The keys come out of a `HashMap`, so no key
/// repeats. A stable sort would only pay a scratch allocation for an order
/// between equal keys that cannot arise.
#[inline(never)]
fn sorted_entries(map: &Map) -> Entries {
    let mut entries: Entries = map.iter().map(|(&key, &value)| (key, value)).collect();
    entries.sort_unstable_by_key(|&(key, _)| key);
    entries
}

/// The map an entry list denotes, which is `HashMap.ofEntries` in the Lean
/// model and the step borsh's own map deserializer performs. A later value
/// under a key already seen replaces the earlier one.
#[inline(never)]
fn collect_entries(entries: Entries) -> Map {
    entries.into_iter().collect()
}

// `map_len` has no kernel of its own. It counts the map that `collect_entries`
// builds, and a `len` kernel around that count is a call LLVM deletes whatever
// the inline attribute says.

/// `HashMap::insert`, which takes and returns the map so the export stays
/// functional. The displaced value comes back beside the map.
#[inline(never)]
fn insert(mut map: Map, key: u32, value: u32) -> (Option<u32>, Map) {
    let displaced = map.insert(key, value);
    (displaced, map)
}

/// `HashMap::remove`, which returns the removed value beside the rest of the
/// map.
#[inline(never)]
fn remove(mut map: Map, key: u32) -> (Option<u32>, Map) {
    let removed = map.remove(&key);
    (removed, map)
}

/// `HashMap::get`.
#[inline(never)]
fn get(map: &Map, key: u32) -> Option<u32> {
    map.get(&key).copied()
}

/// `HashMap::contains_key`.
#[inline(never)]
fn contains_key(map: &Map, key: u32) -> bool {
    map.contains_key(&key)
}

/// Write the entry count as a borsh `u32`. The map holds at most one entry
/// per wire pair, and that count came from a `u32` header, so the cast is
/// exact.
pub fn map_len() {
    let Ok(entries) = borsh::from_slice::<Entries>(&read_all()) else {
        return;
    };
    reply(&(collect_entries(entries).len() as u32));
}

/// Write the value under the leading key. An absent key gives `None`, which
/// still writes its tag byte.
pub fn map_get() {
    let Ok((key, entries)) = borsh::from_slice::<(u32, Entries)>(&read_all()) else {
        return;
    };
    reply(&get(&collect_entries(entries), key));
}

/// Write whether the leading key has an entry.
pub fn map_contains_key() {
    let Ok((key, entries)) = borsh::from_slice::<(u32, Entries)>(&read_all()) else {
        return;
    };
    reply(&contains_key(&collect_entries(entries), key));
}

/// Insert the leading key and value, then write the displaced value beside
/// the map after the insertion.
pub fn map_insert() {
    let Ok((key, value, entries)) = borsh::from_slice::<(u32, u32, Entries)>(&read_all()) else {
        return;
    };
    let (displaced, map) = insert(collect_entries(entries), key, value);
    reply(&(displaced, sorted_entries(&map)));
}

/// Remove the leading key, then write the removed value beside the map after
/// the removal. An absent key gives `None`, which still writes its tag byte.
pub fn map_remove() {
    let Ok((key, entries)) = borsh::from_slice::<(u32, Entries)>(&read_all()) else {
        return;
    };
    let (removed, map) = remove(collect_entries(entries), key);
    reply(&(removed, sorted_entries(&map)));
}

#[cfg(test)]
mod tests {
    use super::{Entries, Map};

    fn map(entries: &[(u32, u32)]) -> Map {
        entries.iter().copied().collect()
    }

    /// A `u32` count then each key beside its value, all little-endian.
    fn wire(entries: &[(u32, u32)]) -> Vec<u8> {
        let mut bytes = (entries.len() as u32).to_le_bytes().to_vec();
        for (key, value) in entries {
            bytes.extend_from_slice(&key.to_le_bytes());
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        bytes
    }

    #[test]
    fn insert_returns_the_displaced_value_and_the_map() {
        assert_eq!(super::insert(map(&[]), 7, 70), (None, map(&[(7, 70)])));
        assert_eq!(
            super::insert(map(&[(1, 10), (2, 20)]), 2, 21),
            (Some(20), map(&[(1, 10), (2, 21)]))
        );
    }

    #[test]
    fn remove_returns_the_removed_value_and_the_rest() {
        assert_eq!(super::remove(map(&[]), 1), (None, map(&[])));
        assert_eq!(
            super::remove(map(&[(1, 10), (2, 20)]), 1),
            (Some(10), map(&[(2, 20)]))
        );
    }

    #[test]
    fn get_is_none_for_an_absent_key() {
        assert_eq!(super::get(&map(&[(4, 40), (5, 50)]), 4), Some(40));
        assert_eq!(super::get(&map(&[(4, 40), (5, 50)]), 6), None);
        assert_eq!(super::get(&map(&[]), 0), None);
    }

    #[test]
    fn contains_key_finds_a_present_key() {
        assert!(super::contains_key(&map(&[(1, 10), (2, 20)]), 2));
        assert!(!super::contains_key(&map(&[(1, 10), (2, 20)]), 3));
        assert!(!super::contains_key(&map(&[]), 0));
    }

    /// The exact bytes that `CodeLib.RustStd.Borsh` and
    /// `CodeLib.RustStd.HashMap.Codec` state: a map is a `u32` count then the
    /// entries in key order, and each entry is the key beside the value. The
    /// input is built out of key order, so the assertion also shows that the
    /// encoding does not depend on the order of construction.
    #[test]
    fn a_map_goes_out_in_key_order() {
        let entries = super::sorted_entries(&map(&[(9, 90), (1, 10), (5, 50)]));
        assert_eq!(entries, vec![(1, 10), (5, 50), (9, 90)]);
        assert_eq!(
            borsh::to_vec(&entries).unwrap(),
            wire(&[(1, 10), (5, 50), (9, 90)])
        );
        assert_eq!(
            borsh::to_vec(&super::sorted_entries(&map(&[]))).unwrap(),
            [0, 0, 0, 0]
        );
    }

    /// What `HashMap.ofEntries` models: the wire carries a pair list, and a
    /// collect of that list keeps the last value of a repeated key, so the map
    /// holds fewer entries than the count the header states.
    #[test]
    fn a_repeated_key_keeps_its_last_value() {
        let bytes = wire(&[(3, 30), (3, 31)]);
        let entries = borsh::from_slice::<Entries>(&bytes).unwrap();
        let decoded = super::collect_entries(entries);
        assert_eq!(decoded, map(&[(3, 31)]));
        assert_eq!(decoded.len(), 1);
    }

    /// The whole round trip a contract states: a map goes out sorted and comes
    /// back as itself.
    #[test]
    fn a_map_survives_the_round_trip() {
        let original = map(&[(9, 90), (1, 10), (5, 50)]);
        let bytes = borsh::to_vec(&super::sorted_entries(&original)).unwrap();
        let entries = borsh::from_slice::<Entries>(&bytes).unwrap();
        assert_eq!(super::collect_entries(entries), original);
    }

    /// The exact bytes the Lean output functions state. `containsKeyOutput` is
    /// a borsh `bool`, which is one byte. `insertOutput` and `removeOutput`
    /// are an `Option` tag, then the map as a `u32` count and the entries in
    /// key order. A borsh tuple puts no framing between those two halves. Two
    /// of the assertions read back the two input shapes the exports accept.
    ///
    /// The last one is the whole `map_insert` path on an input that is not in
    /// key order. `Project.RustHashMap.Spec.insert_output_sorts` states the
    /// same 29 bytes on the Lean side. The model and this crate are therefore
    /// pinned to each other, not only to themselves.
    #[test]
    fn borsh_layout_matches_the_lean_model() {
        assert_eq!(borsh::to_vec(&true).unwrap(), [1]);
        assert_eq!(borsh::to_vec(&false).unwrap(), [0]);
        assert_eq!(
            borsh::to_vec(&(None::<u32>, super::sorted_entries(&map(&[])))).unwrap(),
            [0, 0, 0, 0, 0]
        );
        assert_eq!(
            borsh::to_vec(&(Some(20u32), super::sorted_entries(&map(&[(1, 10)])))).unwrap(),
            [1, 20, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 10, 0, 0, 0]
        );
        assert_eq!(
            borsh::from_slice::<(u32, Entries)>(&[7, 0, 0, 0, 1, 0, 0, 0, 9, 0, 0, 0, 90, 0, 0, 0])
                .unwrap(),
            (7u32, vec![(9u32, 90u32)])
        );
        assert_eq!(
            borsh::from_slice::<(u32, u32, Entries)>(&[7, 0, 0, 0, 70, 0, 0, 0, 0, 0, 0, 0])
                .unwrap(),
            (7u32, 70u32, Vec::new())
        );
        let (displaced, updated) =
            super::insert(super::collect_entries(vec![(2, 20), (1, 10)]), 3, 30);
        assert_eq!(
            borsh::to_vec(&(displaced, super::sorted_entries(&updated))).unwrap(),
            [
                0, 3, 0, 0, 0, 1, 0, 0, 0, 10, 0, 0, 0, 2, 0, 0, 0, 20, 0, 0, 0, 3, 0, 0, 0, 30, 0,
                0, 0
            ]
        );
    }

    /// `from_slice` rejects each input the spec's reader rejects: empty input,
    /// a short header, a trailing byte, a count that disagrees with the
    /// payload, and a tuple whose map is missing.
    #[test]
    fn borsh_rejects_what_the_spec_rejects() {
        assert!(borsh::from_slice::<Entries>(&[]).is_err());
        assert!(borsh::from_slice::<Entries>(&[1, 0, 0]).is_err());
        assert!(borsh::from_slice::<Entries>(&[0, 0, 0, 0, 9]).is_err());
        assert!(borsh::from_slice::<Entries>(&[1, 0, 0, 0, 5, 0, 0, 0]).is_err());
        assert!(borsh::from_slice::<(u32, Entries)>(&[5, 0, 0, 0]).is_err());
    }
}
