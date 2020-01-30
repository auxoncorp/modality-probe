//! A helper for defining variably populated vectors backed
//! by a slice of storage capacity.
use core::borrow::{Borrow, BorrowMut};
use core::convert::From;
use core::hash::{Hash, Hasher};
use core::mem::MaybeUninit;
use core::ops::{Deref, DerefMut};

/// Vec-like structure backed by a storage slice of possibly uninitialized data.
pub struct SliceVec<'a, T: Sized + Copy> {
    /// Backing storage
    storage: &'a mut [MaybeUninit<T>],
    /// The number of items that have been
    /// initialized
    len: usize,
}

impl<'a, T: Sized + Copy> SliceVec<'a, T> {
    /// The length of the SliceVec. The number of initialized
    /// values that have been added to it.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// The maximum amount of items that can live in this SliceVec
    #[inline]
    pub fn capacity(&self) -> usize {
        self.storage.len()
    }

    /// Returns true if there are no items present.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns true if the SliceVec is full to capacity.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len == self.capacity()
    }

    /// Attempt to add a value to the SliceVec. May return an error
    /// if there is not sufficient capacity to hold another item.
    #[inline]
    pub fn try_push(&mut self, value: T) -> Result<(), TryPushError<T>> {
        if self.is_full() {
            return Err(TryPushError(value));
        }
        self.storage[self.len] = MaybeUninit::new(value);
        self.len += 1;
        Ok(())
    }

    /// Remove the last item from the SliceVec.
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        let upcoming_len = self.len - 1;
        let v = Some(unsafe { self.storage[upcoming_len].assume_init() });
        self.len = upcoming_len;
        v
    }

    /// Removes the SliceVec's tracking of all items in it while retaining the
    /// same capacity. Note the utter lack of an attempt to drop any of the
    /// now-inaccessible slice content. Should be safe because we presently limit
    /// the item type to Copy types.
    #[inline]
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Obtain an immutable slice view on the initialized portion of the
    /// SliceVec.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self
    }

    /// Obtain a mutable slice view on the initialized portion of the
    /// SliceVec.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self
    }

    /// Create a well-aligned SliceVec backed by a slice of the provided bytes. The slice is as
    /// large as possible given the item type and alignment of the provided bytes.
    ///
    /// If you are interested in recapturing the prefix and suffix bytes on either side of the
    /// carved-out SliceVec buffer, consider using `CarvedSliceVec::from(bytes)` directly.
    #[inline]
    pub fn carve(bytes: &'a mut [u8]) -> SliceVec<'a, T> {
        CarvedSliceVec::from(bytes).slice_vec
    }
}

/// Error that occurs when a call to `try_push` fails due
/// to insufficient capacity in the SliceVec.
#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
pub struct TryPushError<T>(pub T);

/// Helper struct that tracks the outcome of carving up a byte array
/// to produce an arbitrarily-typed SliceVec.  In particular it
/// provides access to the non-SliceVec portions of that operation -
/// the prefix and suffix bytes that, for alignment or sizing reasons
/// could not be folded into the SliceVec's underlying buffer.
pub struct CarvedSliceVec<'a, T: Sized + Copy> {
    /// Bytes preceding the SliceVec's storage slice
    pub unused_prefix: &'a mut [u8],
    /// A SliceVec of arbitrary type
    pub slice_vec: SliceVec<'a, T>,
    /// Bytes after the SliceVec's storage slice
    pub unused_suffix: &'a mut [u8],
}

impl<'a, T: Sized + Copy> From<&'a mut [u8]> for CarvedSliceVec<'a, T> {
    #[inline]
    fn from(bytes: &'a mut [u8]) -> Self {
        let prefix_offset = bytes.as_ptr().align_offset(core::mem::align_of::<T>());
        if prefix_offset > bytes.len() {
            return CarvedSliceVec {
                unused_prefix: bytes,
                slice_vec: SliceVec {
                    storage: &mut [],
                    len: 0,
                },
                unused_suffix: &mut [],
            };
        }
        let (unused_prefix, middle_bytes) = bytes.split_at_mut(prefix_offset);
        let item_size = core::mem::size_of::<T>();
        let n_items = middle_bytes.len() / item_size;
        let (raw_storage, unused_suffix) = middle_bytes.split_at_mut(n_items * item_size);
        let storage: &'a mut [MaybeUninit<T>] = unsafe {
            core::slice::from_raw_parts_mut(
                raw_storage.as_mut_ptr() as *mut MaybeUninit<T>,
                n_items,
            )
        };
        let slice_vec = storage.into();

        CarvedSliceVec {
            unused_prefix,
            slice_vec,
            unused_suffix,
        }
    }
}

impl<'a, T: Sized + Copy> From<&'a mut [MaybeUninit<T>]> for SliceVec<'a, T> {
    #[inline]
    fn from(v: &'a mut [MaybeUninit<T>]) -> Self {
        SliceVec { storage: v, len: 0 }
    }
}

impl<'a, T: Sized + Copy> From<&'a mut [T]> for SliceVec<'a, T> {
    #[inline]
    fn from(v: &'a mut [T]) -> Self {
        let len = v.len();
        SliceVec {
            storage: unsafe {
                core::slice::from_raw_parts_mut(v.as_mut_ptr() as *mut MaybeUninit<T>, len)
            },
            len,
        }
    }
}

impl<'a, T: Sized + Copy> Hash for SliceVec<'a, T>
where
    T: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<'a, T: Sized + Copy> PartialEq for SliceVec<'a, T>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<'a, T: Sized + Copy> PartialEq<[T]> for SliceVec<'a, T>
where
    T: PartialEq,
{
    #[inline]
    fn eq(&self, other: &[T]) -> bool {
        **self == *other
    }
}

impl<'a, T: Sized + Copy> Eq for SliceVec<'a, T> where T: Eq {}

impl<'a, T: Sized + Copy> Borrow<[T]> for SliceVec<'a, T> {
    #[inline]
    fn borrow(&self) -> &[T] {
        self
    }
}

impl<'a, T: Sized + Copy> BorrowMut<[T]> for SliceVec<'a, T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<'a, T: Sized + Copy> AsRef<[T]> for SliceVec<'a, T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<'a, T: Sized + Copy> AsMut<[T]> for SliceVec<'a, T> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<'a, T: Sized + Copy> core::fmt::Debug for SliceVec<'a, T>
where
    T: core::fmt::Debug,
{
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        (**self).fmt(f)
    }
}

impl<'a, T: Sized + Copy> PartialOrd for SliceVec<'a, T>
where
    T: PartialOrd,
{
    #[inline]
    fn partial_cmp(&self, other: &SliceVec<'a, T>) -> Option<core::cmp::Ordering> {
        (**self).partial_cmp(other)
    }

    #[inline]
    fn lt(&self, other: &Self) -> bool {
        (**self).lt(other)
    }

    #[inline]
    fn le(&self, other: &Self) -> bool {
        (**self).le(other)
    }

    #[inline]
    fn gt(&self, other: &Self) -> bool {
        (**self).gt(other)
    }

    #[inline]
    fn ge(&self, other: &Self) -> bool {
        (**self).ge(other)
    }
}

impl<'a, T: Sized + Copy> Deref for SliceVec<'a, T> {
    type Target = [T];
    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { core::slice::from_raw_parts(self.storage.as_ptr() as *const T, self.len) }
    }
}

impl<'a, T: Sized + Copy> DerefMut for SliceVec<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.storage.as_mut_ptr() as *mut T, self.len) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_uninit() {
        let mut data: [MaybeUninit<u8>; 32] = unsafe { MaybeUninit::uninit().assume_init() };
        let mut sv: SliceVec<u8> = (&mut data[..]).into();
        assert_eq!(0, sv.len());
        assert_eq!(32, sv.capacity());
        assert!(sv.is_empty());
        let sv_as_slice: &[u8] = &sv;
        let empty_slice: &[u8] = &[];
        assert_eq!(empty_slice, sv_as_slice);
        assert_eq!(Ok(()), sv.try_push(3));
        assert_eq!(Ok(()), sv.try_push(1));
        assert_eq!(Ok(()), sv.try_push(4));
        let non_empty_slice: &[u8] = &[3u8, 1, 4];
        assert_eq!(non_empty_slice, &sv as &[u8]);
        let sv_as_mut_slice: &mut [u8] = &mut sv;
        sv_as_mut_slice[1] = 2;
        let non_empty_slice: &[u8] = &[3u8, 2, 4];
        assert_eq!(non_empty_slice, &sv as &[u8]);

        sv.clear();
        assert_eq!(0, sv.len());
        assert!(sv.is_empty());
    }

    #[test]
    fn from_init() {
        let mut data = [2, 7, 1, 9, 8, 3];
        let mut sv: SliceVec<u8> = (&mut data[..]).into();
        assert_eq!(6, sv.len());
        assert_eq!(6, sv.capacity());
        assert_eq!(Some(3), sv.pop());
        assert_eq!(Some(8), sv.pop());
        assert_eq!(Some(9), sv.pop());
        assert_eq!(3, sv.len());
        assert_eq!(6, sv.capacity());
    }

    #[test]
    fn happy_path_carve() {
        let mut data = [0u8; 31];
        let mut sv: SliceVec<usize> = SliceVec::carve(&mut data[..]);
        assert!(sv.is_empty());
        assert!(sv.capacity() > 0);
        for i in 0..sv.capacity() {
            assert_eq!(Ok(()), sv.try_push(i));
        }
        assert!(sv.is_full());
    }
}
