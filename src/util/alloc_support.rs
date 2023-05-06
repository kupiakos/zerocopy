extern crate alloc;

use crate::FromZeroes;
use alloc::vec::Vec;

/// Extends a `Vec<T>` by pushing `additional` new items onto the end of the
/// vector. The new items are initialized with zeroes.
///
/// # Panics
///
/// Panics if `Vec::reserve(additional)` fails to reserve enough memory.
pub fn extend_vec_zeroed<T: FromZeroes>(v: &mut Vec<T>, additional: usize) {
    insert_vec_zeroed(v, v.len(), additional);
}

/// Inserts `additional` new items into `Vec<T>` at `position`.
/// The new items are initialized with zeroes.
///
/// # Panics
///
/// * Panics if `position > v.len()`.
/// * Panics if `Vec::reserve(additional)` fails to reserve enough memory.
pub fn insert_vec_zeroed<T: FromZeroes>(v: &mut Vec<T>, position: usize, additional: usize) {
    assert!(position <= v.len());
    v.reserve(additional);
    // SAFETY: The `reserve` call guarantees that these cannot overflow:
    // * `ptr.add(position)`
    // * `position + additional`
    // * `v.len() + additional`
    //
    // `v.len() - position` cannot overflow because we asserted that
    // `position <= v.len()`.
    unsafe {
        // This is a potentially overlapping copy.
        let ptr = v.as_mut_ptr();
        #[allow(clippy::arithmetic_side_effects)]
        ptr.add(position).copy_to(ptr.add(position + additional), v.len() - position);
        ptr.add(position).write_bytes(0, additional);
        #[allow(clippy::arithmetic_side_effects)]
        v.set_len(v.len() + additional);
    }
}

#[cfg(test)]
mod tests {
    use core::{convert::TryFrom as _, mem};

    use super::*;
    use crate::*;

    #[test]
    fn test_extend_vec_zeroed() {
        // Test extending when there is an existing allocation.
        let mut v: Vec<u64> = Vec::with_capacity(3);
        v.push(100);
        v.push(200);
        v.push(300);
        extend_vec_zeroed(&mut v, 3);
        assert_eq!(v.len(), 6);
        assert_eq!(&*v, &[100, 200, 300, 0, 0, 0]);
        drop(v);

        // Test extending when there is no existing allocation.
        let mut v: Vec<u64> = Vec::new();
        extend_vec_zeroed(&mut v, 3);
        assert_eq!(v.len(), 3);
        assert_eq!(&*v, &[0, 0, 0]);
        drop(v);
    }

    #[test]
    fn test_extend_vec_zeroed_zst() {
        // Test extending when there is an existing (fake) allocation.
        let mut v: Vec<()> = Vec::with_capacity(3);
        v.push(());
        v.push(());
        v.push(());
        extend_vec_zeroed(&mut v, 3);
        assert_eq!(v.len(), 6);
        assert_eq!(&*v, &[(), (), (), (), (), ()]);
        drop(v);

        // Test extending when there is no existing (fake) allocation.
        let mut v: Vec<()> = Vec::new();
        extend_vec_zeroed(&mut v, 3);
        assert_eq!(&*v, &[(), (), ()]);
        drop(v);
    }

    #[test]
    fn test_insert_vec_zeroed() {
        // Insert at start (no existing allocation).
        let mut v: Vec<u64> = Vec::new();
        insert_vec_zeroed(&mut v, 0, 2);
        assert_eq!(v.len(), 2);
        assert_eq!(&*v, &[0, 0]);
        drop(v);

        // Insert at start.
        let mut v: Vec<u64> = Vec::with_capacity(3);
        v.push(100);
        v.push(200);
        v.push(300);
        insert_vec_zeroed(&mut v, 0, 2);
        assert_eq!(v.len(), 5);
        assert_eq!(&*v, &[0, 0, 100, 200, 300]);
        drop(v);

        // Insert at middle.
        let mut v: Vec<u64> = Vec::with_capacity(3);
        v.push(100);
        v.push(200);
        v.push(300);
        insert_vec_zeroed(&mut v, 1, 1);
        assert_eq!(v.len(), 4);
        assert_eq!(&*v, &[100, 0, 200, 300]);
        drop(v);

        // Insert at end.
        let mut v: Vec<u64> = Vec::with_capacity(3);
        v.push(100);
        v.push(200);
        v.push(300);
        insert_vec_zeroed(&mut v, 3, 1);
        assert_eq!(v.len(), 4);
        assert_eq!(&*v, &[100, 200, 300, 0]);
        drop(v);
    }

    #[test]
    fn test_insert_vec_zeroed_zst() {
        // Insert at start (no existing fake allocation).
        let mut v: Vec<()> = Vec::new();
        insert_vec_zeroed(&mut v, 0, 2);
        assert_eq!(v.len(), 2);
        assert_eq!(&*v, &[(), ()]);
        drop(v);

        // Insert at start.
        let mut v: Vec<()> = Vec::with_capacity(3);
        v.push(());
        v.push(());
        v.push(());
        insert_vec_zeroed(&mut v, 0, 2);
        assert_eq!(v.len(), 5);
        assert_eq!(&*v, &[(), (), (), (), ()]);
        drop(v);

        // Insert at middle.
        let mut v: Vec<()> = Vec::with_capacity(3);
        v.push(());
        v.push(());
        v.push(());
        insert_vec_zeroed(&mut v, 1, 1);
        assert_eq!(v.len(), 4);
        assert_eq!(&*v, &[(), (), (), ()]);
        drop(v);

        // Insert at end.
        let mut v: Vec<()> = Vec::with_capacity(3);
        v.push(());
        v.push(());
        v.push(());
        insert_vec_zeroed(&mut v, 3, 1);
        assert_eq!(v.len(), 4);
        assert_eq!(&*v, &[(), (), (), ()]);
        drop(v);
    }

    #[test]
    fn test_new_box_zeroed() {
        assert_eq!(*u64::new_box_zeroed(), 0);
    }

    #[test]
    fn test_new_box_zeroed_array() {
        drop(<[u32; 0x1000]>::new_box_zeroed());
    }

    #[test]
    fn test_new_box_zeroed_zst() {
        // This test exists in order to exercise unsafe code, especially
        // when running under Miri.
        #[allow(clippy::unit_cmp)]
        {
            assert_eq!(*<()>::new_box_zeroed(), ());
        }
    }

    #[test]
    fn test_new_box_slice_zeroed() {
        let mut s: Box<[u64]> = u64::new_box_slice_zeroed(3);
        assert_eq!(s.len(), 3);
        assert_eq!(&*s, &[0, 0, 0]);
        s[1] = 3;
        assert_eq!(&*s, &[0, 3, 0]);
    }

    #[test]
    fn test_new_box_slice_zeroed_empty() {
        let s: Box<[u64]> = u64::new_box_slice_zeroed(0);
        assert_eq!(s.len(), 0);
    }

    #[test]
    fn test_new_box_slice_zeroed_zst() {
        let mut s: Box<[()]> = <()>::new_box_slice_zeroed(3);
        assert_eq!(s.len(), 3);
        assert!(s.get(10).is_none());
        // This test exists in order to exercise unsafe code, especially
        // when running under Miri.
        #[allow(clippy::unit_cmp)]
        {
            assert_eq!(s[1], ());
        }
        s[2] = ();
    }

    #[test]
    fn test_new_box_slice_zeroed_zst_empty() {
        let s: Box<[()]> = <()>::new_box_slice_zeroed(0);
        assert_eq!(s.len(), 0);
    }

    #[test]
    #[should_panic(expected = "mem::size_of::<Self>() * len overflows `usize`")]
    fn test_new_box_slice_zeroed_panics_mul_overflow() {
        let _ = u16::new_box_slice_zeroed(usize::MAX);
    }

    #[test]
    #[should_panic(expected = "total allocation size overflows `isize`: LayoutError")]
    fn test_new_box_slice_zeroed_panics_isize_overflow() {
        let max = usize::try_from(isize::MAX).unwrap();
        let _ = u16::new_box_slice_zeroed((max / mem::size_of::<u16>()) + 1);
    }
}
