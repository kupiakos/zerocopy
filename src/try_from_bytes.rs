use core::convert::Infallible;

use super::*;

#[derive(Debug)]
#[derive(Copy, Clone)]
pub enum TryFromBytesError {
    /// The byte slice was too small.
    Size,

    /// The byte slice was not aligned on an address for `&T`.
    Align,

    /// The byte slice had the correct layout but an invalid byte pattern for `T`.
    Value,
}

impl TryFromBytesError {
    pub fn static_message(&self) -> &'static str {
        match LayoutError::try_from(*self) {
            Ok(e) => e.static_message(),
            Err(_) => "The byte slice had a correct layout but invalid byte pattern for the target type",
        }
    }
}

impl Display for TryFromBytesError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(self.static_message())
    }
}

impl TryFrom<TryFromBytesError> for LayoutError {
    type Error = TryFromBytesError;

    fn try_from(value: TryFromBytesError) -> Result<Self, Self::Error> {
        match value {
            TryFromBytesError::Size => Ok(LayoutError::Size),
            TryFromBytesError::Align => Ok(LayoutError::Align),
            TryFromBytesError::Value => Err(value),
        }
    }
}

impl From<LayoutError> for TryFromBytesError {
    fn from(value: LayoutError) -> Self {
        match value {
            LayoutError::Size => TryFromBytesError::Size,
            LayoutError::Align => TryFromBytesError::Align,
        }
    }
}

pub trait TryFromBytes {
    fn try_read_from<B: ByteSlice>(bytes: B) -> Result<Self, TryFromBytesError>
    where Self: Sized {
        todo!()
    }

    fn try_read_from_prefix<B: ByteSlice>(bytes: B) -> Result<Self, TryFromBytesError>
    where Self: Sized {
        todo!()
    }

    fn try_read_from_suffix<B: ByteSlice>(bytes: B) -> Result<Self, TryFromBytesError>
    where Self: Sized {
        todo!()
    }
}

impl<T> TryFromBytes for T where T: FromBytes {
    fn try_read_from<B: ByteSlice>(bytes: B) -> Result<Self, TryFromBytesError>
    where Self: Sized {
        Ok(T::read_from(bytes).ok_or(TryFromBytesError::Size)?)
    }

    fn try_read_from_prefix<B: ByteSlice>(bytes: B) -> Result<Self, TryFromBytesError>
    where Self: Sized {
        Ok(T::read_from_prefix(bytes).ok_or(TryFromBytesError::Size)?)
    }

    fn try_read_from_suffix<B: ByteSlice>(bytes: B) -> Result<Self, TryFromBytesError>
    where Self: Sized {
        Ok(T::read_from_suffix(bytes).ok_or(TryFromBytesError::Size)?)
    }
}
