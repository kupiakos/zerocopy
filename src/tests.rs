//! Tests of broad properties of zerocopy.
#![allow(clippy::unreadable_literal)]

use core::{
    fmt::{self, Debug, Display, Formatter},
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
        NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize, Wrapping,
    },
    ops::{Deref, DerefMut},
};

use static_assertions::assert_impl_all;

use super::*;

/// A `T` which is aligned to at least `align_of::<A>()`.
#[derive(Default)]
struct Align<T, A> {
    t: T,
    _a: [A; 0],
}

impl<T: Default, A> Align<T, A> {
    fn set_default(&mut self) {
        self.t = T::default();
    }
}

impl<T, A> Align<T, A> {
    const fn new(t: T) -> Align<T, A> {
        Align { t, _a: [] }
    }
}

/// A `T` which is guaranteed not to satisfy `align_of::<A>()`.
///
/// It must be the case that `align_of::<T>() < align_of::<A>()` in order
/// fot this type to work properly.
#[repr(C)]
struct ForceUnalign<T, A> {
    // The outer struct is aligned to `A`, and, thanks to `repr(C)`, `t` is
    // placed at the minimum offset that guarantees its alignment. If
    // `align_of::<T>() < align_of::<A>()`, then that offset will be
    // guaranteed *not* to satisfy `align_of::<A>()`.
    _u: u8,
    t: T,
    _a: [A; 0],
}

impl<T, A> ForceUnalign<T, A> {
    const fn new(t: T) -> ForceUnalign<T, A> {
        ForceUnalign { _u: 0, t, _a: [] }
    }
}

// A `u64` with alignment 8.
//
// Though `u64` has alignment 8 on some platforms, it's not guaranteed.
// By contrast, `AU64` is guaranteed to have alignment 8.
#[derive(
    FromZeroes, FromBytes, AsBytes, Eq, PartialEq, Ord, PartialOrd, Default, Debug, Copy, Clone,
)]
#[repr(C, align(8))]
struct AU64(u64);

impl Display for AU64 {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

// Converts an `AU64` to bytes using this platform's endianness.
fn au64_to_bytes(u: AU64) -> [u8; 8] {
    transmute!(u)
}

// An unsized type.
//
// This is used to test the custom derives of our traits. The `[u8]` type
// gets a hand-rolled impl, so it doesn't exercise our custom derives.
#[derive(Debug, Eq, PartialEq, FromZeroes, FromBytes, AsBytes, Unaligned)]
#[repr(transparent)]
struct Unsized([u8]);

impl Unsized {
    fn from_mut_slice(slc: &mut [u8]) -> &mut Unsized {
        // SAFETY: This *probably* sound - since the layouts of `[u8]` and
        // `Unsized` are the same, so are the layouts of `&mut [u8]` and
        // `&mut Unsized`. [1] Even if it turns out that this isn't actually
        // guaranteed by the language spec, we can just change this since
        // it's in test code.
        //
        // [1] https://github.com/rust-lang/unsafe-code-guidelines/issues/375
        unsafe { mem::transmute(slc) }
    }
}

#[test]
fn test_object_safety() {
    fn _takes_from_zeroes(_: &dyn FromZeroes) {}
    fn _takes_from_bytes(_: &dyn FromBytes) {}
    fn _takes_unaligned(_: &dyn Unaligned) {}
}

#[test]
fn test_from_zeroes_only() {
    // Test types that implement `FromZeroes` but not `FromBytes`.

    assert_eq!(bool::new_zeroed(), false);
    assert_eq!(char::new_zeroed(), '\0');

    #[cfg(feature = "alloc")]
    {
        assert_eq!(bool::new_box_zeroed(), Box::new(false));
        assert_eq!(char::new_box_zeroed(), Box::new('\0'));

        assert_eq!(bool::new_box_slice_zeroed(3).as_ref(), [false, false, false]);
        assert_eq!(char::new_box_slice_zeroed(3).as_ref(), ['\0', '\0', '\0']);

        assert_eq!(bool::new_vec_zeroed(3).as_ref(), [false, false, false]);
        assert_eq!(char::new_vec_zeroed(3).as_ref(), ['\0', '\0', '\0']);
    }

    let mut string = "hello".to_string();
    let s: &mut str = string.as_mut();
    assert_eq!(s, "hello");
    s.zero();
    assert_eq!(s, "\0\0\0\0\0");
}

#[test]
fn test_unalign() {
    // Test methods that don't depend on alignment.
    let mut u = Unalign::new(AU64(123));
    assert_eq!(u.get(), AU64(123));
    assert_eq!(u.into_inner(), AU64(123));
    assert_eq!(u.get_ptr(), <*const _>::cast::<AU64>(&u));
    assert_eq!(u.get_mut_ptr(), <*mut _>::cast::<AU64>(&mut u));
    u.set(AU64(321));
    assert_eq!(u.get(), AU64(321));

    // Test methods that depend on alignment (when alignment is satisfied).
    let mut u: Align<_, AU64> = Align::new(Unalign::new(AU64(123)));
    assert_eq!(u.t.try_deref(), Some(&AU64(123)));
    assert_eq!(u.t.try_deref_mut(), Some(&mut AU64(123)));
    // SAFETY: The `Align<_, AU64>` guarantees proper alignment.
    assert_eq!(unsafe { u.t.deref_unchecked() }, &AU64(123));
    // SAFETY: The `Align<_, AU64>` guarantees proper alignment.
    assert_eq!(unsafe { u.t.deref_mut_unchecked() }, &mut AU64(123));
    *u.t.try_deref_mut().unwrap() = AU64(321);
    assert_eq!(u.t.get(), AU64(321));

    // Test methods that depend on alignment (when alignment is not
    // satisfied).
    let mut u: ForceUnalign<_, AU64> = ForceUnalign::new(Unalign::new(AU64(123)));
    assert_eq!(u.t.try_deref(), None);
    assert_eq!(u.t.try_deref_mut(), None);

    // Test methods that depend on `T: Unaligned`.
    let mut u = Unalign::new(123u8);
    assert_eq!(u.try_deref(), Some(&123));
    assert_eq!(u.try_deref_mut(), Some(&mut 123));
    assert_eq!(u.deref(), &123);
    assert_eq!(u.deref_mut(), &mut 123);
    *u = 21;
    assert_eq!(u.get(), 21);

    // Test that some `Unalign` functions and methods are `const`.
    const _UNALIGN: Unalign<u64> = Unalign::new(0);
    const _UNALIGN_PTR: *const u64 = _UNALIGN.get_ptr();
    const _U64: u64 = _UNALIGN.into_inner();
    // Make sure all code is considered "used".
    //
    // TODO(https://github.com/rust-lang/rust/issues/104084): Remove this
    // attribute.
    #[allow(dead_code)]
    const _: () = {
        let x: Align<_, AU64> = Align::new(Unalign::new(AU64(123)));
        // Make sure that `deref_unchecked` is `const`.
        //
        // SAFETY: The `Align<_, AU64>` guarantees proper alignment.
        let au64 = unsafe { x.t.deref_unchecked() };
        match au64 {
            AU64(123) => {}
            _ => unreachable!(),
        }
    };
}

#[test]
fn test_read_write() {
    const VAL: u64 = 0x12345678;
    #[cfg(target_endian = "big")]
    const VAL_BYTES: [u8; 8] = VAL.to_be_bytes();
    #[cfg(target_endian = "little")]
    const VAL_BYTES: [u8; 8] = VAL.to_le_bytes();

    // Test `FromBytes::{read_from, read_from_prefix, read_from_suffix}`.

    assert_eq!(u64::read_from(&VAL_BYTES[..]), Some(VAL));
    // The first 8 bytes are from `VAL_BYTES` and the second 8 bytes are all
    // zeroes.
    let bytes_with_prefix: [u8; 16] = transmute!([VAL_BYTES, [0; 8]]);
    assert_eq!(u64::read_from_prefix(&bytes_with_prefix[..]), Some(VAL));
    assert_eq!(u64::read_from_suffix(&bytes_with_prefix[..]), Some(0));
    // The first 8 bytes are all zeroes and the second 8 bytes are from
    // `VAL_BYTES`
    let bytes_with_suffix: [u8; 16] = transmute!([[0; 8], VAL_BYTES]);
    assert_eq!(u64::read_from_prefix(&bytes_with_suffix[..]), Some(0));
    assert_eq!(u64::read_from_suffix(&bytes_with_suffix[..]), Some(VAL));

    // Test `AsBytes::{write_to, write_to_prefix, write_to_suffix}`.

    let mut bytes = [0u8; 8];
    assert_eq!(VAL.write_to(&mut bytes[..]), Some(()));
    assert_eq!(bytes, VAL_BYTES);
    let mut bytes = [0u8; 16];
    assert_eq!(VAL.write_to_prefix(&mut bytes[..]), Some(()));
    let want: [u8; 16] = transmute!([VAL_BYTES, [0; 8]]);
    assert_eq!(bytes, want);
    let mut bytes = [0u8; 16];
    assert_eq!(VAL.write_to_suffix(&mut bytes[..]), Some(()));
    let want: [u8; 16] = transmute!([[0; 8], VAL_BYTES]);
    assert_eq!(bytes, want);
}

#[test]
fn test_transmute() {
    // Test that memory is transmuted as expected.
    let array_of_u8s = [0u8, 1, 2, 3, 4, 5, 6, 7];
    let array_of_arrays = [[0, 1], [2, 3], [4, 5], [6, 7]];
    let x: [[u8; 2]; 4] = transmute!(array_of_u8s);
    assert_eq!(x, array_of_arrays);
    let x: [u8; 8] = transmute!(array_of_arrays);
    assert_eq!(x, array_of_u8s);

    // Test that the source expression's value is forgotten rather than
    // dropped.
    #[derive(AsBytes)]
    #[repr(transparent)]
    struct PanicOnDrop(());
    impl Drop for PanicOnDrop {
        fn drop(&mut self) {
            panic!("PanicOnDrop::drop");
        }
    }
    let _: () = transmute!(PanicOnDrop(()));

    // Test that `transmute!` is legal in a const context.
    const ARRAY_OF_U8S: [u8; 8] = [0u8, 1, 2, 3, 4, 5, 6, 7];
    const ARRAY_OF_ARRAYS: [[u8; 2]; 4] = [[0, 1], [2, 3], [4, 5], [6, 7]];
    const X: [[u8; 2]; 4] = transmute!(ARRAY_OF_U8S);
    assert_eq!(X, ARRAY_OF_ARRAYS);
}

#[test]
fn test_address() {
    // Test that the `Deref` and `DerefMut` implementations return a
    // reference which points to the right region of memory.

    let buf = [0];
    let lv = LayoutVerified::<_, u8>::new(&buf[..]).unwrap();
    let buf_ptr = buf.as_ptr();
    let deref_ptr: *const u8 = lv.deref();
    assert_eq!(buf_ptr, deref_ptr);

    let buf = [0];
    let lv = LayoutVerified::<_, [u8]>::new_slice(&buf[..]).unwrap();
    let buf_ptr = buf.as_ptr();
    let deref_ptr = lv.deref().as_ptr();
    assert_eq!(buf_ptr, deref_ptr);
}

// Verify that values written to a `LayoutVerified` are properly shared
// between the typed and untyped representations, that reads via `deref` and
// `read` behave the same, and that writes via `deref_mut` and `write`
// behave the same.
fn test_new_helper(mut lv: LayoutVerified<&mut [u8], AU64>) {
    // assert that the value starts at 0
    assert_eq!(*lv, AU64(0));
    assert_eq!(lv.read(), AU64(0));

    // Assert that values written to the typed value are reflected in the
    // byte slice.
    const VAL1: AU64 = AU64(0xFF00FF00FF00FF00);
    *lv = VAL1;
    assert_eq!(lv.bytes(), &au64_to_bytes(VAL1));
    *lv = AU64(0);
    lv.write(VAL1);
    assert_eq!(lv.bytes(), &au64_to_bytes(VAL1));

    // Assert that values written to the byte slice are reflected in the
    // typed value.
    const VAL2: AU64 = AU64(!VAL1.0); // different from `VAL1`
    lv.bytes_mut().copy_from_slice(&au64_to_bytes(VAL2)[..]);
    assert_eq!(*lv, VAL2);
    assert_eq!(lv.read(), VAL2);
}

// Verify that values written to a `LayoutVerified` are properly shared
// between the typed and untyped representations; pass a value with
// `typed_len` `AU64`s backed by an array of `typed_len * 8` bytes.
fn test_new_helper_slice(mut lv: LayoutVerified<&mut [u8], [AU64]>, typed_len: usize) {
    // Assert that the value starts out zeroed.
    assert_eq!(&*lv, vec![AU64(0); typed_len].as_slice());

    // Check the backing storage is the exact same slice.
    let untyped_len = typed_len * 8;
    assert_eq!(lv.bytes().len(), untyped_len);
    assert_eq!(lv.bytes().as_ptr(), lv.as_ptr().cast::<u8>());

    // Assert that values written to the typed value are reflected in the
    // byte slice.
    const VAL1: AU64 = AU64(0xFF00FF00FF00FF00);
    for typed in &mut *lv {
        *typed = VAL1;
    }
    assert_eq!(lv.bytes(), VAL1.0.to_ne_bytes().repeat(typed_len).as_slice());

    // Assert that values written to the byte slice are reflected in the
    // typed value.
    const VAL2: AU64 = AU64(!VAL1.0); // different from VAL1
    lv.bytes_mut().copy_from_slice(&VAL2.0.to_ne_bytes().repeat(typed_len));
    assert!(lv.iter().copied().all(|x| x == VAL2));
}

// Verify that values written to a `LayoutVerified` are properly shared
// between the typed and untyped representations, that reads via `deref` and
// `read` behave the same, and that writes via `deref_mut` and `write`
// behave the same.
fn test_new_helper_unaligned(mut lv: LayoutVerified<&mut [u8], [u8; 8]>) {
    // assert that the value starts at 0
    assert_eq!(*lv, [0; 8]);
    assert_eq!(lv.read(), [0; 8]);

    // Assert that values written to the typed value are reflected in the
    // byte slice.
    const VAL1: [u8; 8] = [0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00];
    *lv = VAL1;
    assert_eq!(lv.bytes(), &VAL1);
    *lv = [0; 8];
    lv.write(VAL1);
    assert_eq!(lv.bytes(), &VAL1);

    // Assert that values written to the byte slice are reflected in the
    // typed value.
    const VAL2: [u8; 8] = [0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF, 0x00, 0xFF]; // different from VAL1
    lv.bytes_mut().copy_from_slice(&VAL2[..]);
    assert_eq!(*lv, VAL2);
    assert_eq!(lv.read(), VAL2);
}

// Verify that values written to a `LayoutVerified` are properly shared
// between the typed and untyped representations; pass a value with `len`
// `u8`s backed by an array of `len` bytes.
fn test_new_helper_slice_unaligned(mut lv: LayoutVerified<&mut [u8], [u8]>, len: usize) {
    // Assert that the value starts out zeroed.
    assert_eq!(&*lv, vec![0u8; len].as_slice());

    // Check the backing storage is the exact same slice.
    assert_eq!(lv.bytes().len(), len);
    assert_eq!(lv.bytes().as_ptr(), lv.as_ptr());

    // Assert that values written to the typed value are reflected in the
    // byte slice.
    let mut expected_bytes = [0xFF, 0x00].iter().copied().cycle().take(len).collect::<Vec<_>>();
    lv.copy_from_slice(&expected_bytes);
    assert_eq!(lv.bytes(), expected_bytes.as_slice());

    // Assert that values written to the byte slice are reflected in the
    // typed value.
    for byte in &mut expected_bytes {
        *byte = !*byte; // different from `expected_len`
    }
    lv.bytes_mut().copy_from_slice(&expected_bytes);
    assert_eq!(&*lv, expected_bytes.as_slice());
}

#[test]
fn test_new_aligned_sized() {
    // Test that a properly-aligned, properly-sized buffer works for new,
    // new_from_prefix, and new_from_suffix, and that new_from_prefix and
    // new_from_suffix return empty slices. Test that a properly-aligned
    // buffer whose length is a multiple of the element size works for
    // new_slice. Test that xxx_zeroed behaves the same, and zeroes the
    // memory.

    // A buffer with an alignment of 8.
    let mut buf = Align::<[u8; 8], AU64>::default();
    // `buf.t` should be aligned to 8, so this should always succeed.
    test_new_helper(LayoutVerified::<_, AU64>::new(&mut buf.t[..]).unwrap());
    buf.t = [0xFFu8; 8];
    test_new_helper(LayoutVerified::<_, AU64>::new_zeroed(&mut buf.t[..]).unwrap());
    {
        // In a block so that `lv` and `suffix` don't live too long.
        buf.set_default();
        let (lv, suffix) = LayoutVerified::<_, AU64>::new_from_prefix(&mut buf.t[..]).unwrap();
        assert!(suffix.is_empty());
        test_new_helper(lv);
    }
    {
        buf.t = [0xFFu8; 8];
        let (lv, suffix) =
            LayoutVerified::<_, AU64>::new_from_prefix_zeroed(&mut buf.t[..]).unwrap();
        assert!(suffix.is_empty());
        test_new_helper(lv);
    }
    {
        buf.set_default();
        let (prefix, lv) = LayoutVerified::<_, AU64>::new_from_suffix(&mut buf.t[..]).unwrap();
        assert!(prefix.is_empty());
        test_new_helper(lv);
    }
    {
        buf.t = [0xFFu8; 8];
        let (prefix, lv) =
            LayoutVerified::<_, AU64>::new_from_suffix_zeroed(&mut buf.t[..]).unwrap();
        assert!(prefix.is_empty());
        test_new_helper(lv);
    }

    // A buffer with alignment 8 and length 16.
    let mut buf = Align::<[u8; 16], AU64>::default();
    // `buf.t` should be aligned to 8 and have a length which is a multiple
    // of `size_of::<AU64>()`, so this should always succeed.
    test_new_helper_slice(LayoutVerified::<_, [AU64]>::new_slice(&mut buf.t[..]).unwrap(), 2);
    buf.t = [0xFFu8; 16];
    test_new_helper_slice(
        LayoutVerified::<_, [AU64]>::new_slice_zeroed(&mut buf.t[..]).unwrap(),
        2,
    );

    {
        buf.set_default();
        let (lv, suffix) =
            LayoutVerified::<_, [AU64]>::new_slice_from_prefix(&mut buf.t[..], 1).unwrap();
        assert_eq!(suffix, [0; 8]);
        test_new_helper_slice(lv, 1);
    }
    {
        buf.t = [0xFFu8; 16];
        let (lv, suffix) =
            LayoutVerified::<_, [AU64]>::new_slice_from_prefix_zeroed(&mut buf.t[..], 1).unwrap();
        assert_eq!(suffix, [0xFF; 8]);
        test_new_helper_slice(lv, 1);
    }
    {
        buf.set_default();
        let (prefix, lv) =
            LayoutVerified::<_, [AU64]>::new_slice_from_suffix(&mut buf.t[..], 1).unwrap();
        assert_eq!(prefix, [0; 8]);
        test_new_helper_slice(lv, 1);
    }
    {
        buf.t = [0xFFu8; 16];
        let (prefix, lv) =
            LayoutVerified::<_, [AU64]>::new_slice_from_suffix_zeroed(&mut buf.t[..], 1).unwrap();
        assert_eq!(prefix, [0xFF; 8]);
        test_new_helper_slice(lv, 1);
    }
}

#[test]
fn test_new_unaligned_sized() {
    // Test that an unaligned, properly-sized buffer works for
    // `new_unaligned`, `new_unaligned_from_prefix`, and
    // `new_unaligned_from_suffix`, and that `new_unaligned_from_prefix`
    // `new_unaligned_from_suffix` return empty slices. Test that an
    // unaligned buffer whose length is a multiple of the element size works
    // for `new_slice`. Test that `xxx_zeroed` behaves the same, and zeroes
    // the memory.

    let mut buf = [0u8; 8];
    test_new_helper_unaligned(LayoutVerified::<_, [u8; 8]>::new_unaligned(&mut buf[..]).unwrap());
    buf = [0xFFu8; 8];
    test_new_helper_unaligned(
        LayoutVerified::<_, [u8; 8]>::new_unaligned_zeroed(&mut buf[..]).unwrap(),
    );
    {
        // In a block so that `lv` and `suffix` don't live too long.
        buf = [0u8; 8];
        let (lv, suffix) =
            LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix(&mut buf[..]).unwrap();
        assert!(suffix.is_empty());
        test_new_helper_unaligned(lv);
    }
    {
        buf = [0xFFu8; 8];
        let (lv, suffix) =
            LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix_zeroed(&mut buf[..]).unwrap();
        assert!(suffix.is_empty());
        test_new_helper_unaligned(lv);
    }
    {
        buf = [0u8; 8];
        let (prefix, lv) =
            LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix(&mut buf[..]).unwrap();
        assert!(prefix.is_empty());
        test_new_helper_unaligned(lv);
    }
    {
        buf = [0xFFu8; 8];
        let (prefix, lv) =
            LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix_zeroed(&mut buf[..]).unwrap();
        assert!(prefix.is_empty());
        test_new_helper_unaligned(lv);
    }

    let mut buf = [0u8; 16];
    // `buf.t` should be aligned to 8 and have a length which is a multiple
    // of `size_of::AU64>()`, so this should always succeed.
    test_new_helper_slice_unaligned(
        LayoutVerified::<_, [u8]>::new_slice_unaligned(&mut buf[..]).unwrap(),
        16,
    );
    buf = [0xFFu8; 16];
    test_new_helper_slice_unaligned(
        LayoutVerified::<_, [u8]>::new_slice_unaligned_zeroed(&mut buf[..]).unwrap(),
        16,
    );

    {
        buf = [0u8; 16];
        let (lv, suffix) =
            LayoutVerified::<_, [u8]>::new_slice_unaligned_from_prefix(&mut buf[..], 8).unwrap();
        assert_eq!(suffix, [0; 8]);
        test_new_helper_slice_unaligned(lv, 8);
    }
    {
        buf = [0xFFu8; 16];
        let (lv, suffix) =
            LayoutVerified::<_, [u8]>::new_slice_unaligned_from_prefix_zeroed(&mut buf[..], 8)
                .unwrap();
        assert_eq!(suffix, [0xFF; 8]);
        test_new_helper_slice_unaligned(lv, 8);
    }
    {
        buf = [0u8; 16];
        let (prefix, lv) =
            LayoutVerified::<_, [u8]>::new_slice_unaligned_from_suffix(&mut buf[..], 8).unwrap();
        assert_eq!(prefix, [0; 8]);
        test_new_helper_slice_unaligned(lv, 8);
    }
    {
        buf = [0xFFu8; 16];
        let (prefix, lv) =
            LayoutVerified::<_, [u8]>::new_slice_unaligned_from_suffix_zeroed(&mut buf[..], 8)
                .unwrap();
        assert_eq!(prefix, [0xFF; 8]);
        test_new_helper_slice_unaligned(lv, 8);
    }
}

#[test]
fn test_new_oversized() {
    // Test that a properly-aligned, overly-sized buffer works for
    // `new_from_prefix` and `new_from_suffix`, and that they return the
    // remainder and prefix of the slice respectively. Test that
    // `xxx_zeroed` behaves the same, and zeroes the memory.

    let mut buf = Align::<[u8; 16], AU64>::default();
    {
        // In a block so that `lv` and `suffix` don't live too long.
        // `buf.t` should be aligned to 8, so this should always succeed.
        let (lv, suffix) = LayoutVerified::<_, AU64>::new_from_prefix(&mut buf.t[..]).unwrap();
        assert_eq!(suffix.len(), 8);
        test_new_helper(lv);
    }
    {
        buf.t = [0xFFu8; 16];
        // `buf.t` should be aligned to 8, so this should always succeed.
        let (lv, suffix) =
            LayoutVerified::<_, AU64>::new_from_prefix_zeroed(&mut buf.t[..]).unwrap();
        // Assert that the suffix wasn't zeroed.
        assert_eq!(suffix, &[0xFFu8; 8]);
        test_new_helper(lv);
    }
    {
        buf.set_default();
        // `buf.t` should be aligned to 8, so this should always succeed.
        let (prefix, lv) = LayoutVerified::<_, AU64>::new_from_suffix(&mut buf.t[..]).unwrap();
        assert_eq!(prefix.len(), 8);
        test_new_helper(lv);
    }
    {
        buf.t = [0xFFu8; 16];
        // `buf.t` should be aligned to 8, so this should always succeed.
        let (prefix, lv) =
            LayoutVerified::<_, AU64>::new_from_suffix_zeroed(&mut buf.t[..]).unwrap();
        // Assert that the prefix wasn't zeroed.
        assert_eq!(prefix, &[0xFFu8; 8]);
        test_new_helper(lv);
    }
}

#[test]
fn test_new_unaligned_oversized() {
    // Test than an unaligned, overly-sized buffer works for
    // `new_unaligned_from_prefix` and `new_unaligned_from_suffix`, and that
    // they return the remainder and prefix of the slice respectively. Test
    // that `xxx_zeroed` behaves the same, and zeroes the memory.

    let mut buf = [0u8; 16];
    {
        // In a block so that `lv` and `suffix` don't live too long.
        let (lv, suffix) =
            LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix(&mut buf[..]).unwrap();
        assert_eq!(suffix.len(), 8);
        test_new_helper_unaligned(lv);
    }
    {
        buf = [0xFFu8; 16];
        let (lv, suffix) =
            LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix_zeroed(&mut buf[..]).unwrap();
        // Assert that the suffix wasn't zeroed.
        assert_eq!(suffix, &[0xFF; 8]);
        test_new_helper_unaligned(lv);
    }
    {
        buf = [0u8; 16];
        let (prefix, lv) =
            LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix(&mut buf[..]).unwrap();
        assert_eq!(prefix.len(), 8);
        test_new_helper_unaligned(lv);
    }
    {
        buf = [0xFFu8; 16];
        let (prefix, lv) =
            LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix_zeroed(&mut buf[..]).unwrap();
        // Assert that the prefix wasn't zeroed.
        assert_eq!(prefix, &[0xFF; 8]);
        test_new_helper_unaligned(lv);
    }
}

#[test]
#[allow(clippy::cognitive_complexity)]
fn test_new_error() {
    // Fail because the buffer is too large.

    // A buffer with an alignment of 8.
    let mut buf = Align::<[u8; 16], AU64>::default();
    // `buf.t` should be aligned to 8, so only the length check should fail.
    assert!(LayoutVerified::<_, AU64>::new(&buf.t[..]).is_none());
    assert!(LayoutVerified::<_, AU64>::new_zeroed(&mut buf.t[..]).is_none());
    assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned(&buf.t[..]).is_none());
    assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned_zeroed(&mut buf.t[..]).is_none());

    // Fail because the buffer is too small.

    // A buffer with an alignment of 8.
    let mut buf = Align::<[u8; 4], AU64>::default();
    // `buf.t` should be aligned to 8, so only the length check should fail.
    assert!(LayoutVerified::<_, AU64>::new(&buf.t[..]).is_none());
    assert!(LayoutVerified::<_, AU64>::new_zeroed(&mut buf.t[..]).is_none());
    assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned(&buf.t[..]).is_none());
    assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned_zeroed(&mut buf.t[..]).is_none());
    assert!(LayoutVerified::<_, AU64>::new_from_prefix(&buf.t[..]).is_none());
    assert!(LayoutVerified::<_, AU64>::new_from_prefix_zeroed(&mut buf.t[..]).is_none());
    assert!(LayoutVerified::<_, AU64>::new_from_suffix(&buf.t[..]).is_none());
    assert!(LayoutVerified::<_, AU64>::new_from_suffix_zeroed(&mut buf.t[..]).is_none());
    assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix(&buf.t[..]).is_none());
    assert!(
        LayoutVerified::<_, [u8; 8]>::new_unaligned_from_prefix_zeroed(&mut buf.t[..]).is_none()
    );
    assert!(LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix(&buf.t[..]).is_none());
    assert!(
        LayoutVerified::<_, [u8; 8]>::new_unaligned_from_suffix_zeroed(&mut buf.t[..]).is_none()
    );

    // Fail because the length is not a multiple of the element size.

    let mut buf = Align::<[u8; 12], AU64>::default();
    // `buf.t` has length 12, but element size is 8.
    assert!(LayoutVerified::<_, [AU64]>::new_slice(&buf.t[..]).is_none());
    assert!(LayoutVerified::<_, [AU64]>::new_slice_zeroed(&mut buf.t[..]).is_none());
    assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned(&buf.t[..]).is_none());
    assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_zeroed(&mut buf.t[..]).is_none());

    // Fail because the buffer is too short.
    let mut buf = Align::<[u8; 12], AU64>::default();
    // `buf.t` has length 12, but the element size is 8 (and we're expecting
    // two of them).
    assert!(LayoutVerified::<_, [AU64]>::new_slice_from_prefix(&buf.t[..], 2).is_none());
    assert!(LayoutVerified::<_, [AU64]>::new_slice_from_prefix_zeroed(&mut buf.t[..], 2).is_none());
    assert!(LayoutVerified::<_, [AU64]>::new_slice_from_suffix(&buf.t[..], 2).is_none());
    assert!(LayoutVerified::<_, [AU64]>::new_slice_from_suffix_zeroed(&mut buf.t[..], 2).is_none());
    assert!(
        LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix(&buf.t[..], 2).is_none()
    );
    assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix_zeroed(
        &mut buf.t[..],
        2
    )
    .is_none());
    assert!(
        LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix(&buf.t[..], 2).is_none()
    );
    assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix_zeroed(
        &mut buf.t[..],
        2
    )
    .is_none());

    // Fail because the alignment is insufficient.

    // A buffer with an alignment of 8. An odd buffer size is chosen so that
    // the last byte of the buffer has odd alignment.
    let mut buf = Align::<[u8; 13], AU64>::default();
    // Slicing from 1, we get a buffer with size 12 (so the length check
    // should succeed) but an alignment of only 1, which is insufficient.
    assert!(LayoutVerified::<_, AU64>::new(&buf.t[1..]).is_none());
    assert!(LayoutVerified::<_, AU64>::new_zeroed(&mut buf.t[1..]).is_none());
    assert!(LayoutVerified::<_, AU64>::new_from_prefix(&buf.t[1..]).is_none());
    assert!(LayoutVerified::<_, AU64>::new_from_prefix_zeroed(&mut buf.t[1..]).is_none());
    assert!(LayoutVerified::<_, [AU64]>::new_slice(&buf.t[1..]).is_none());
    assert!(LayoutVerified::<_, [AU64]>::new_slice_zeroed(&mut buf.t[1..]).is_none());
    assert!(LayoutVerified::<_, [AU64]>::new_slice_from_prefix(&buf.t[1..], 1).is_none());
    assert!(LayoutVerified::<_, [AU64]>::new_slice_from_prefix_zeroed(&mut buf.t[1..], 1).is_none());
    assert!(LayoutVerified::<_, [AU64]>::new_slice_from_suffix(&buf.t[1..], 1).is_none());
    assert!(LayoutVerified::<_, [AU64]>::new_slice_from_suffix_zeroed(&mut buf.t[1..], 1).is_none());
    // Slicing is unnecessary here because `new_from_suffix[_zeroed]` use
    // the suffix of the slice, which has odd alignment.
    assert!(LayoutVerified::<_, AU64>::new_from_suffix(&buf.t[..]).is_none());
    assert!(LayoutVerified::<_, AU64>::new_from_suffix_zeroed(&mut buf.t[..]).is_none());

    // Fail due to arithmetic overflow.

    let mut buf = Align::<[u8; 16], AU64>::default();
    let unreasonable_len = usize::MAX / mem::size_of::<AU64>() + 1;
    assert!(
        LayoutVerified::<_, [AU64]>::new_slice_from_prefix(&buf.t[..], unreasonable_len).is_none()
    );
    assert!(LayoutVerified::<_, [AU64]>::new_slice_from_prefix_zeroed(
        &mut buf.t[..],
        unreasonable_len
    )
    .is_none());
    assert!(
        LayoutVerified::<_, [AU64]>::new_slice_from_suffix(&buf.t[..], unreasonable_len).is_none()
    );
    assert!(LayoutVerified::<_, [AU64]>::new_slice_from_suffix_zeroed(
        &mut buf.t[..],
        unreasonable_len
    )
    .is_none());
    assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix(
        &buf.t[..],
        unreasonable_len
    )
    .is_none());
    assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_prefix_zeroed(
        &mut buf.t[..],
        unreasonable_len
    )
    .is_none());
    assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix(
        &buf.t[..],
        unreasonable_len
    )
    .is_none());
    assert!(LayoutVerified::<_, [[u8; 8]]>::new_slice_unaligned_from_suffix_zeroed(
        &mut buf.t[..],
        unreasonable_len
    )
    .is_none());
}

// Tests for ensuring that, if a ZST is passed into a slice-like function,
// we always panic. Since these tests need to be separate per-function, and
// they tend to take up a lot of space, we generate them using a macro in a
// submodule instead. The submodule ensures that we can just re-use the name
// of the function under test for the name of the test itself.
mod test_zst_panics {
    macro_rules! zst_test {
        ($name:ident($($tt:tt)*), $constructor_in_panic_msg:tt) => {
            #[test]
            #[should_panic = concat!("LayoutVerified::", $constructor_in_panic_msg, " called on a zero-sized type")]
            fn $name() {
                let mut buffer = [0u8];
                let lv = $crate::LayoutVerified::<_, [()]>::$name(&mut buffer[..], $($tt)*);
                unreachable!("should have panicked, got {:?}", lv);
            }
        }
    }
    zst_test!(new_slice(), "new_slice");
    zst_test!(new_slice_zeroed(), "new_slice");
    zst_test!(new_slice_from_prefix(1), "new_slice");
    zst_test!(new_slice_from_prefix_zeroed(1), "new_slice");
    zst_test!(new_slice_from_suffix(1), "new_slice");
    zst_test!(new_slice_from_suffix_zeroed(1), "new_slice");
    zst_test!(new_slice_unaligned(), "new_slice_unaligned");
    zst_test!(new_slice_unaligned_zeroed(), "new_slice_unaligned");
    zst_test!(new_slice_unaligned_from_prefix(1), "new_slice_unaligned");
    zst_test!(new_slice_unaligned_from_prefix_zeroed(1), "new_slice_unaligned");
    zst_test!(new_slice_unaligned_from_suffix(1), "new_slice_unaligned");
    zst_test!(new_slice_unaligned_from_suffix_zeroed(1), "new_slice_unaligned");
}

#[test]
fn test_as_bytes_methods() {
    /// Run a series of tests by calling `AsBytes` methods on `t`.
    ///
    /// `bytes` is the expected byte sequence returned from `t.as_bytes()`
    /// before `t` has been modified. `post_mutation` is the expected
    /// sequence returned from `t.as_bytes()` after `t.as_bytes_mut()[0]`
    /// has had its bits flipped (by applying `^= 0xFF`).
    ///
    /// `N` is the size of `t` in bytes.
    fn test<const N: usize, T: FromBytes + AsBytes + Debug + Eq + ?Sized>(
        t: &mut T,
        bytes: &[u8],
        post_mutation: &T,
    ) {
        // Test that we can access the underlying bytes, and that we get the
        // right bytes and the right number of bytes.
        assert_eq!(t.as_bytes(), bytes);

        // Test that changes to the underlying byte slices are reflected in
        // the original object.
        t.as_bytes_mut()[0] ^= 0xFF;
        assert_eq!(t, post_mutation);
        t.as_bytes_mut()[0] ^= 0xFF;

        // `write_to` rejects slices that are too small or too large.
        assert_eq!(t.write_to(&mut vec![0; N - 1][..]), None);
        assert_eq!(t.write_to(&mut vec![0; N + 1][..]), None);

        // `write_to` works as expected.
        let mut bytes = [0; N];
        assert_eq!(t.write_to(&mut bytes[..]), Some(()));
        assert_eq!(bytes, t.as_bytes());

        // `write_to_prefix` rejects slices that are too small.
        assert_eq!(t.write_to_prefix(&mut vec![0; N - 1][..]), None);

        // `write_to_prefix` works with exact-sized slices.
        let mut bytes = [0; N];
        assert_eq!(t.write_to_prefix(&mut bytes[..]), Some(()));
        assert_eq!(bytes, t.as_bytes());

        // `write_to_prefix` works with too-large slices, and any bytes past
        // the prefix aren't modified.
        let mut too_many_bytes = vec![0; N + 1];
        too_many_bytes[N] = 123;
        assert_eq!(t.write_to_prefix(&mut too_many_bytes[..]), Some(()));
        assert_eq!(&too_many_bytes[..N], t.as_bytes());
        assert_eq!(too_many_bytes[N], 123);

        // `write_to_suffix` rejects slices that are too small.
        assert_eq!(t.write_to_suffix(&mut vec![0; N - 1][..]), None);

        // `write_to_suffix` works with exact-sized slices.
        let mut bytes = [0; N];
        assert_eq!(t.write_to_suffix(&mut bytes[..]), Some(()));
        assert_eq!(bytes, t.as_bytes());

        // `write_to_suffix` works with too-large slices, and any bytes
        // before the suffix aren't modified.
        let mut too_many_bytes = vec![0; N + 1];
        too_many_bytes[0] = 123;
        assert_eq!(t.write_to_suffix(&mut too_many_bytes[..]), Some(()));
        assert_eq!(&too_many_bytes[1..], t.as_bytes());
        assert_eq!(too_many_bytes[0], 123);
    }

    #[derive(Debug, Eq, PartialEq, FromZeroes, FromBytes, AsBytes)]
    #[repr(C)]
    struct Foo {
        a: u32,
        b: Wrapping<u32>,
        c: Option<NonZeroU32>,
    }

    let expected_bytes: Vec<u8> = if cfg!(target_endian = "little") {
        vec![1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
    } else {
        vec![0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0]
    };
    let post_mutation_expected_a =
        if cfg!(target_endian = "little") { 0x00_00_00_FE } else { 0xFF_00_00_01 };
    test::<12, _>(
        &mut Foo { a: 1, b: Wrapping(2), c: None },
        expected_bytes.as_bytes(),
        &Foo { a: post_mutation_expected_a, b: Wrapping(2), c: None },
    );
    test::<3, _>(
        Unsized::from_mut_slice(&mut [1, 2, 3]),
        &[1, 2, 3],
        Unsized::from_mut_slice(&mut [0xFE, 2, 3]),
    );
}

#[test]
fn test_array() {
    #[derive(FromZeroes, FromBytes, AsBytes)]
    #[repr(C)]
    struct Foo {
        a: [u16; 33],
    }

    let foo = Foo { a: [0xFFFF; 33] };
    let expected = [0xFFu8; 66];
    assert_eq!(foo.as_bytes(), &expected[..]);
}

#[test]
fn test_display_debug() {
    let buf = Align::<[u8; 8], u64>::default();
    let lv = LayoutVerified::<_, u64>::new(&buf.t[..]).unwrap();
    assert_eq!(format!("{}", lv), "0");
    assert_eq!(format!("{:?}", lv), "LayoutVerified(0)");

    let buf = Align::<[u8; 8], u64>::default();
    let lv = LayoutVerified::<_, [u64]>::new_slice(&buf.t[..]).unwrap();
    assert_eq!(format!("{:?}", lv), "LayoutVerified([0])");
}

#[test]
fn test_eq() {
    let buf1 = 0_u64;
    let lv1 = LayoutVerified::<_, u64>::new(buf1.as_bytes()).unwrap();
    let buf2 = 0_u64;
    let lv2 = LayoutVerified::<_, u64>::new(buf2.as_bytes()).unwrap();
    assert_eq!(lv1, lv2);
}

#[test]
fn test_ne() {
    let buf1 = 0_u64;
    let lv1 = LayoutVerified::<_, u64>::new(buf1.as_bytes()).unwrap();
    let buf2 = 1_u64;
    let lv2 = LayoutVerified::<_, u64>::new(buf2.as_bytes()).unwrap();
    assert_ne!(lv1, lv2);
}

#[test]
fn test_ord() {
    let buf1 = 0_u64;
    let lv1 = LayoutVerified::<_, u64>::new(buf1.as_bytes()).unwrap();
    let buf2 = 1_u64;
    let lv2 = LayoutVerified::<_, u64>::new(buf2.as_bytes()).unwrap();
    assert!(lv1 < lv2);
}

#[test]
fn test_new_zeroed() {
    assert_eq!(bool::new_zeroed(), false);
    assert_eq!(u64::new_zeroed(), 0);
    // This test exists in order to exercise unsafe code, especially when
    // running under Miri.
    #[allow(clippy::unit_cmp)]
    {
        assert_eq!(<()>::new_zeroed(), ());
    }
}

#[test]
fn test_transparent_packed_generic_struct() {
    #[derive(AsBytes, FromZeroes, FromBytes, Unaligned)]
    #[repr(transparent)]
    struct Foo<T> {
        _t: T,
        _phantom: PhantomData<()>,
    }

    assert_impl_all!(Foo<u32>: FromZeroes, FromBytes, AsBytes);
    assert_impl_all!(Foo<u8>: Unaligned);

    #[derive(AsBytes, FromZeroes, FromBytes, Unaligned)]
    #[repr(packed)]
    struct Bar<T, U> {
        _t: T,
        _u: U,
    }

    assert_impl_all!(Bar<u8, AU64>: FromZeroes, FromBytes, AsBytes, Unaligned);
}

#[test]
fn test_impls() {
    // Asserts that `$ty` implements any `$trait` and doesn't implement any
    // `!$trait`. Note that all `$trait`s must come before any `!$trait`s.
    macro_rules! assert_impls {
        ($ty:ty: $trait:ident) => {
            #[allow(dead_code)]
            const _: () = { static_assertions::assert_impl_all!($ty: $trait); };
        };
        ($ty:ty: !$trait:ident) => {
            #[allow(dead_code)]
            const _: () = { static_assertions::assert_not_impl_any!($ty: $trait); };
        };
        ($ty:ty: $($trait:ident),* $(,)? $(!$negative_trait:ident),*) => {
            $(
                assert_impls!($ty: $trait);
            )*

            $(
                assert_impls!($ty: !$negative_trait);
            )*
        };
    }

    assert_impls!((): FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!(u8: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!(i8: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!(u16: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(i16: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(u32: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(i32: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(u64: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(i64: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(u128: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(i128: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(usize: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(isize: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(f32: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(f64: FromZeroes, FromBytes, AsBytes, !Unaligned);

    assert_impls!(bool: FromZeroes, AsBytes, Unaligned, !FromBytes);
    assert_impls!(char: FromZeroes, AsBytes, !FromBytes, !Unaligned);
    assert_impls!(str: FromZeroes, AsBytes, Unaligned, !FromBytes);

    assert_impls!(NonZeroU8: AsBytes, Unaligned, !FromZeroes, !FromBytes);
    assert_impls!(NonZeroI8: AsBytes, Unaligned, !FromZeroes, !FromBytes);
    assert_impls!(NonZeroU16: AsBytes, !FromZeroes, !FromBytes, !Unaligned);
    assert_impls!(NonZeroI16: AsBytes, !FromZeroes, !FromBytes, !Unaligned);
    assert_impls!(NonZeroU32: AsBytes, !FromZeroes, !FromBytes, !Unaligned);
    assert_impls!(NonZeroI32: AsBytes, !FromZeroes, !FromBytes, !Unaligned);
    assert_impls!(NonZeroU64: AsBytes, !FromZeroes, !FromBytes, !Unaligned);
    assert_impls!(NonZeroI64: AsBytes, !FromZeroes, !FromBytes, !Unaligned);
    assert_impls!(NonZeroU128: AsBytes, !FromZeroes, !FromBytes, !Unaligned);
    assert_impls!(NonZeroI128: AsBytes, !FromZeroes, !FromBytes, !Unaligned);
    assert_impls!(NonZeroUsize: AsBytes, !FromZeroes, !FromBytes, !Unaligned);
    assert_impls!(NonZeroIsize: AsBytes, !FromZeroes, !FromBytes, !Unaligned);

    assert_impls!(Option<NonZeroU8>: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!(Option<NonZeroI8>: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!(Option<NonZeroU16>: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(Option<NonZeroI16>: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(Option<NonZeroU32>: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(Option<NonZeroI32>: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(Option<NonZeroU64>: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(Option<NonZeroI64>: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(Option<NonZeroU128>: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(Option<NonZeroI128>: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(Option<NonZeroUsize>: FromZeroes, FromBytes, AsBytes, !Unaligned);
    assert_impls!(Option<NonZeroIsize>: FromZeroes, FromBytes, AsBytes, !Unaligned);

    // Implements none of the ZC traits.
    struct NotZerocopy;

    assert_impls!(PhantomData<NotZerocopy>: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!(PhantomData<[u8]>: FromZeroes, FromBytes, AsBytes, Unaligned);

    assert_impls!(ManuallyDrop<u8>: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!(ManuallyDrop<[u8]>: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!(ManuallyDrop<NotZerocopy>: !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
    assert_impls!(ManuallyDrop<[NotZerocopy]>: !FromZeroes, !FromBytes, !AsBytes, !Unaligned);

    assert_impls!(MaybeUninit<u8>: FromZeroes, FromBytes, Unaligned, !AsBytes);
    assert_impls!(MaybeUninit<NotZerocopy>: FromZeroes, FromBytes, !AsBytes, !Unaligned);

    assert_impls!(Wrapping<u8>: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!(Wrapping<NotZerocopy>: !FromZeroes, !FromBytes, !AsBytes, !Unaligned);

    assert_impls!(Unalign<u8>: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!(Unalign<NotZerocopy>: Unaligned, !FromZeroes, !FromBytes, !AsBytes);

    assert_impls!([u8]: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!([NotZerocopy]: !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
    assert_impls!([u8; 0]: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!([NotZerocopy; 0]: !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
    assert_impls!([u8; 1]: FromZeroes, FromBytes, AsBytes, Unaligned);
    assert_impls!([NotZerocopy; 1]: !FromZeroes, !FromBytes, !AsBytes, !Unaligned);
}
