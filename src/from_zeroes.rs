use super::*;

/// Types for which a sequence of bytes all set to zero represents a valid
/// instance of the type.
///
/// WARNING: Do not implement this trait yourself! Instead, use
/// `#[derive(FromZeroes)]`.
///
/// Any memory region of the appropriate length which is guaranteed to contain
/// only zero bytes can be viewed as any `FromZeroes` type with no runtime
/// overhead. This is useful whenever memory is known to be in a zeroed state,
/// such memory returned from some allocation routines.
///
/// `FromZeroes` is ignorant of byte order. For byte order-aware types, see the
/// [`byteorder`] module.
///
/// # Safety
///
/// If `T: FromZeroes`, then unsafe code may assume that it is sound to treat
/// any initialized sequence of zero bytes of length `size_of::<T>()` as a `T`.
/// If a type is marked as `FromZeroes` which violates this contract, it may
/// cause undefined behavior.
///
/// If a type has the following properties, then it is safe to implement
/// `FromZeroes` for that type:
/// - If the type is a struct, all of its fields must implement `FromZeroes`
/// - If the type is an enum, it must be fieldless (meaning that all variants have
///   no fields) and it must have a variant with a discriminant of `0` (see [the
///   reference] for a description of how discriminant values are chosen)
/// - TODO: add to fields
///
/// TODO: can this type contain interior mutability? 
///
/// [the reference]: https://doc.rust-lang.org/reference/items/enumerations.html#custom-discriminant-values-for-fieldless-enumerations
///
/// # Rationale
///
/// ## Why isn't an explicit representation required for structs?
///
/// Per the [Rust reference](reference),
///
/// > The representation of a type can change the padding between fields, but
/// does not change the layout of the fields themselves.
///
/// [reference]: https://doc.rust-lang.org/reference/type-layout.html#representations
///
/// Since the layout of structs only consists of padding bytes and field bytes,
/// a struct is soundly `FromZeroes` if:
/// 1. its padding is soundly `FromZeroes`, and
/// 2. its fields are soundly `FromZeroes`.
///
/// The answer to the first question is always yes: padding bytes do not have
/// any validity constraints. A [discussion] of this question in the Unsafe Code
/// Guidelines Working Group concluded that it would be virtually unimaginable
/// for future versions of rustc to add validity constraints to padding bytes.
///
/// [discussion]: https://github.com/rust-lang/unsafe-code-guidelines/issues/174
///
/// Whether a struct is soundly `FromZeroes` therefore solely depends on whether
/// its fields are `FromZeroes`.
// TODO(#146): Document why we don't require an enum to have an explicit `repr`
// attribute.
pub unsafe trait FromZeroes {
    // The `Self: Sized` bound makes it so that `FromZeroes` is still object
    // safe.
    #[doc(hidden)]
    fn only_derive_is_allowed_to_implement_this_trait()
    where
        Self: Sized;

    /// Overwrites `self` with zeroes.
    ///
    /// Sets every byte in `self` to 0. While this is similar to doing `*self =
    /// Self::new_zeroed()`, it differs in that `zero` does not semantically
    /// drop the current value and replace it with a new one - it simply
    /// modifies the bytes of the existing value.
    fn zero(&mut self) {
        let slf: *mut Self = self;
        let len = mem::size_of_val(self);
        // SAFETY:
        // - `self` is guaranteed by the type system to be valid for writes of
        //   size `size_of_val(self)`.
        // - `u8`'s alignment is 1, and thus `self` is guaranteed to be aligned
        //   as required by `u8`.
        // - Since `Self: FromZeroes`, the all-zeroes instance is a valid
        //   instance of `Self.`
        unsafe { ptr::write_bytes(slf.cast::<u8>(), 0, len) };
    }

    /// Creates an instance of `Self` from zeroed bytes.
    fn new_zeroed() -> Self
    where
        Self: Sized,
    {
        // SAFETY: `FromZeroes` says that the all-zeroes bit pattern is legal.
        unsafe { mem::zeroed() }
    }

    /// Creates a `Box<Self>` from zeroed bytes.
    ///
    /// This function is useful for allocating large values on the heap and
    /// zero-initializing them, without ever creating a temporary instance of
    /// `Self` on the stack. For example, `<[u8; 1048576]>::new_box_zeroed()`
    /// will allocate `[u8; 1048576]` directly on the heap; it does not require
    /// storing `[u8; 1048576]` in a temporary variable on the stack.
    ///
    /// On systems that use a heap implementation that supports allocating from
    /// pre-zeroed memory, using `new_box_zeroed` (or related functions) may
    /// have performance benefits.
    ///
    /// Note that `Box<Self>` can be converted to `Arc<Self>` and other
    /// container types without reallocation.
    ///
    /// # Panics
    ///
    /// Panics if allocation of `size_of::<Self>()` bytes fails.
    #[cfg(feature = "alloc")]
    fn new_box_zeroed() -> Box<Self>
    where
        Self: Sized,
    {
        // If `T` is a ZST, then return a proper boxed instance of it. There is
        // no allocation, but `Box` does require a correct dangling pointer.
        let layout = Layout::new::<Self>();
        if layout.size() == 0 {
            return Box::new(Self::new_zeroed());
        }

        // TODO(#61): Add a "SAFETY" comment and remove this `allow`.
        #[allow(clippy::undocumented_unsafe_blocks)]
        unsafe {
            let ptr = alloc::alloc::alloc_zeroed(layout).cast::<Self>();
            if ptr.is_null() {
                alloc::alloc::handle_alloc_error(layout);
            }
            Box::from_raw(ptr)
        }
    }

    /// Creates a `Box<[Self]>` (a boxed slice) from zeroed bytes.
    ///
    /// This function is useful for allocating large values of `[Self]` on the
    /// heap and zero-initializing them, without ever creating a temporary
    /// instance of `[Self; _]` on the stack. For example,
    /// `u8::new_box_slice_zeroed(1048576)` will allocate the slice directly on
    /// the heap; it does not require storing the slice on the stack.
    ///
    /// On systems that use a heap implementation that supports allocating from
    /// pre-zeroed memory, using `new_box_slice_zeroed` may have performance
    /// benefits.
    ///
    /// If `Self` is a zero-sized type, then this function will return a
    /// `Box<[Self]>` that has the correct `len`. Such a box cannot contain any
    /// actual information, but its `len()` property will report the correct
    /// value.
    ///
    /// # Panics
    ///
    /// * Panics if `size_of::<Self>() * len` overflows.
    /// * Panics if allocation of `size_of::<Self>() * len` bytes fails.
    #[cfg(feature = "alloc")]
    fn new_box_slice_zeroed(len: usize) -> Box<[Self]>
    where
        Self: Sized,
    {
        // TODO(#2): Use `Layout::repeat` when `alloc_layout_extra` is
        // stabilized.
        let layout = Layout::from_size_align(
            mem::size_of::<Self>()
                .checked_mul(len)
                .expect("mem::size_of::<Self>() * len overflows `usize`"),
            mem::align_of::<Self>(),
        )
        .expect("total allocation size overflows `isize`");

        // TODO(#61): Add a "SAFETY" comment and remove this `allow`.
        #[allow(clippy::undocumented_unsafe_blocks)]
        unsafe {
            if layout.size() != 0 {
                let ptr = alloc::alloc::alloc_zeroed(layout).cast::<Self>();
                if ptr.is_null() {
                    alloc::alloc::handle_alloc_error(layout);
                }
                Box::from_raw(slice::from_raw_parts_mut(ptr, len))
            } else {
                // `Box<[T]>` does not allocate when `T` is zero-sized or when
                // `len` is zero, but it does require a non-null dangling
                // pointer for its allocation.
                Box::from_raw(slice::from_raw_parts_mut(NonNull::<Self>::dangling().as_ptr(), len))
            }
        }
    }

    /// Creates a `Vec<Self>` from zeroed bytes.
    ///
    /// This function is useful for allocating large values of `Vec`s and
    /// zero-initializing them, without ever creating a temporary instance of
    /// `[Self; _]` (or many temporary instances of `Self`) on the stack. For
    /// example, `u8::new_vec_zeroed(1048576)` will allocate directly on the
    /// heap; it does not require storing intermediate values on the stack.
    ///
    /// On systems that use a heap implementation that supports allocating from
    /// pre-zeroed memory, using `new_vec_zeroed` may have performance benefits.
    ///
    /// If `Self` is a zero-sized type, then this function will return a
    /// `Vec<Self>` that has the correct `len`. Such a `Vec` cannot contain any
    /// actual information, but its `len()` property will report the correct
    /// value.
    ///
    /// # Panics
    ///
    /// * Panics if `size_of::<Self>() * len` overflows.
    /// * Panics if allocation of `size_of::<Self>() * len` bytes fails.
    #[cfg(feature = "alloc")]
    fn new_vec_zeroed(len: usize) -> Vec<Self>
    where
        Self: Sized,
    {
        Self::new_box_slice_zeroed(len).into()
    }
}