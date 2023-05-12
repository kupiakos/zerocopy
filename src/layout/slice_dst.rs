

#[derive(Debug)]
struct SliceTailLayout {
    tail_len: usize,
    tail_padding: usize,
}

// this crate is largely powered by unsafe traits with checked-for-safety derive macros

/// A slice-based dynamically sized type with a sized header.
///
/// This includes `[T]` as well as any `#[derive(SliceDst)]` type ending in a `SliceDst` type.
///
/// # Example
///
/// ```ignore
/// use zerocopy::layout::SliceDst;
/// #[derive(FromBytes, SliceDst)]
/// struct Packet {
///   source: [u8; 8],
///   dest: [u8; 8],
///   protocol: u8,
///   body: [u8],
/// }
///
/// assert_eq!(, None);
/// ```
unsafe trait SliceDst: UncheckedFromBytes {

    /// What byte offset from the start of the struct does the slice tail start?
    /// This includes any necessary head padding for alignment.
    const TAIL_OFFSET: usize;

    /// `Self` but with a zero-length array of `TailElement` instead of a slice at the end.
    // TODO: check if necessary to include in trait
    type ZeroLen;

    /// The element that the slice tail in `Self` holds.
    type TailElement;

    /// If this slice can read a tail slice length from its `header`, then this returns it.
    ///
    /// To indicate a slice DST can read its tail slice length from a field, mark the field with
    /// `#[tail_len]`.
    fn header_tail_len(header: &Self::ZeroLen) -> Option<usize> { None }

    /// The maximum slice length metadata for `mem::size_of::<Self>() == size`, plus the
    /// remaining bytes of data not used for `Self`.
    ///
    /// Returns `None` if `size` is not an exact size for `self` with any length metadata.
    fn max_slice_len_pad(mut size: usize) -> Option<SliceTailLayout<Self>> {
        // TODO: micro-optimize, remove branching
        let mut rem = size % Self::ALIGN;
        size = size.checked_sub(Self::TAIL_OFFSET)?;
        let tail_size = mem::size_of::<Self::TailElement>();
        let mut len: usize = size / tail_size;
        rem += size % tail_size;
        if rem > tail_size {
            rem -= tail_size;
            len.checked_add(1)?;
        }


        // consider header at the beginning

        // size: 12, align 2, len = 6, rem = 0
        // size: 14, align 4, len = 3, rem = 2

        Some(SliceDstLayout {
            tail_len: len,
            tail_padding: rem,
        })
    }

    // Possible extension: the ability to mark a specific field as containing a length or size
    // when used with TryFromBytes, which allows it to confirm a length for a given size, and
    // provide a remainder which can be accepted or rejected by from
}

unsafe impl<T> SliceDst for [T] {
    const TAIL_OFFSET: usize = 0;
    type ZeroLen = [T; 0];
    type TailElement = T;

    // const MIN_SIZE: usize = 0;
    // const ALIGN: usize = mem::align_of::<T>();
}

/*

Calculating the size of a DST with a given length metadata/reverse:

- align of whole struct is align of max aligned field
- size is always a multiple of align
- the minimum size is the size with length meta 0
- there exists a length squeeze-len which is the maximum length metadata that does not cause `self`
  to exceed the minimum size. this may be > 0.

total align 8
end of last non-tail field: 5 + 8*1
tail size: 2
tail align: 2
start of tail: alignto(5 + 8*1, 2) == 6 + 8*1
squeeze-len: (8 - 6) / 2 = 1

tail align only comes into play for where it much start, and how much head padding it has

leave head padding for a separate concern.

want to find (meta len, remainder) for a given byte `size`
want to find `size` for a given meta len

total align 16
end of last non-tail field: 1 + 16*1
tail size: 6
tail align: 2
start of tail: alignto(1 + 16*1, 2) = 2 + 16*1
squeeze-len: (16 - 2) / 6 = 2 (2 extra padding)

min_size = alignto(tail_offset, total_align) = 32
tail_offset: 18
empty-tail-pad: 14
size(len) = alignto(tail_offset + tail_size*len, 16)
check for modular arithmetic equivalents?

other direction is harder
== size must be a multiple of total align, so that can be assumed as checked ==

meta len for size: (size - tail_offset)
empty_tail_pad = min_size - tail_offset = 14
room_for_tail = size - min_size + tail_offset
divmod(room_for_tail, tail_size) = (meta len, tail padding)

alignto(s, a) = k*a = s + pad (
    k = ceil(s / a)
    pad = k*a - s
)
tsize = k*talign = alignto(tdatasize, talign)
tdatasize = toff + l*esize = tsize - tailpad = k*talign - tailpad(l)
tailpad(0) = alignto(toff, talign)
tailpad(l) = alignto(toff + l*esize, talign) - (toff + l*esize)
           = alignto(tdatasize, talign) - tdatasize
           = ceil(s / a) * a - s

(a + b) % c == (a % c) + (b % c) % c

a := toff
b := l*esize
c := talign
(a + b) = toff + l*esize = tdatasize = tsize - tailpad(l)



(A + B) mod C = (A mod C + B mod C) mod C

tpad = toff+ % talign

fn find_max_len_for_size:
truncate size if not a multiple of align (s / a * a)
tailsize = checked size - toff, return if None. size >= toff.
tailsize divmod esize = l + pad

then 

tail size does not evenly divide align. squeeze-len has extra padding (2)
0: 32 (14 pad)
1: 32 (8 pad)
2: 32 (2 pad)
3: 48 (12 pad)
4: 48 (6 pad)
5: 48 (0 pad)
6: 


if the tail is:
- more aligned than others: it cannot have tail padding? therefore squeeze-len = 0
- tied for most aligned: the same?
- less aligned than most: there may be tail padding. squeeze-len could be >0 but may be 0.

 */

// Based on https://doc.rust-lang.org/src/core/num/uint_macros.rs.html
/// Calculates the smallest value greater than or equal to `size` that
/// is a multiple of `align`. Returns `None` if `align` is zero or the
/// operation would result in overflow.
fn align_to(size: usize, align: usize) -> Option<usize> {
    match size.checked_rem(align)? {
        0 => Some(size),
        // align - r cannot overflow because r is smaller than align
        r => size.checked_add(align - r)
    }
}

#[repr(C)]
struct TestDst {
    foo: u16,
    rest: [u8],
}

unsafe impl UncheckedFromBytes for TestDst {
    const MIN_SIZE: usize = mem::size_of::<<Self as SliceDst>::ZeroLen>();
    const ALIGN: usize =  mem::size_of::<<Self as SliceDst>::ZeroLen>();

    unsafe fn bytecast_ref_unchecked(bytes: &[u8]) -> &Self {
        let len = bytes.len() / mem::size_of::<u8>();
        let data: *const () = bytes.as_ptr().cast();
        let raw = core::ptr::slice_from_raw_parts(data, len) as *const Self;

        // SAFETY:
        // - The length of `[$t]` metadata is the size in bytes divided by `size_of::<$t>()`.
        // - The layout of `bytes` for `Self` has been checked by the caller.
        unsafe { &*raw }
    }

    unsafe fn bytecast_mut_unchecked(bytes: &mut [u8]) -> &mut Self {
        let len = bytes.len() / mem::size_of::<u8>();
        let data: *mut () = bytes.as_mut_ptr().cast();
        let raw = core::ptr::slice_from_raw_parts_mut(data, len) as *mut Self;

        // SAFETY:
        // - The length of `[$t]` metadata is the size in bytes divided by `size_of::<$t>()`.
        // - The layout of `bytes` for `Self` has been checked by the caller.
        unsafe { &mut *raw }
    }
    // const MIN_SIZE: usize = {

    // };
    // const ALIGN
}


mod __TestDst_slicedst {
    #[repr(C)]
    pub(super) struct ZeroLenTestDst {
        foo: u16,
        pub(super) rest: [u8; 0],
    }
}

unsafe impl SliceDst for TestDst {
    // TODO: does having this be a const rather than functions affect the ability to have generic
    // SliceDst derives?
    const TAIL_OFFSET: usize = {
        let x: core::mem::MaybeUninit<Self::ZeroLen> = core::mem::MaybeUninit::uninit();
        let p = x.as_ptr();
        let elem: *const u8 = unsafe { core::ptr::addr_of!((*p).rest).cast() };
        (unsafe { elem.offset_from(p.cast()) }) as usize
    };

    type TailElement = u8;

    type ZeroLen = __TestDst_slicedst::ZeroLenTestDst;
}

#[repr(C, align(8))]
struct A8U64(u64);

// For any given slice DST, there exists some length `squeeze-len` that causes the runtime size of
// `Self` to exceed its minimum size at slice length 0.
// For `[T]`, squeeze-len is 0. For `TestDst`, it is also 0. For `EvilDst`, however, it is 3.
// This is because it has remaining tail padding due to the alignment of `self` until `tail`
// reaches length 3.
struct EvilDst {
    // The whole DST is aligned on 8 bytes
    // So its size must be a multiple of 8 bytes
    // (a u8 here would introduce 7 bytes of padding)
    head: A8U64,

    // Byte 8.
    x: u8,
    // Always one byte of padding here;
    // TODO CONFIRM: the amount of padding between penultimate field and slice DST tail never
    // changes. We could use difference of real (aligned) tail and unaligned empty tail
    // in order to calculate minimum length to next layout.
    // TODO: does the first len of `tail` always evenly align with 

    // tail starts on byte 10. It can get up to len 3 before filling the minimum 16 bytes
    // of `Self`.
    tail: [u16],
}

