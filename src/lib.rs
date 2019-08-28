use std::mem;
use std::ops::{BitAnd, Shr};

/// Implementation detail: simply extends the integer primitives so they have a
/// static method that returns a 1 of the specific integer type.
pub trait One {
	fn one() -> Self;
}

macro_rules! impl_one {
	($($type:ty)+) => {
		$(impl One for $type {
			#[inline]
			fn one() -> $type {
				1
			}
		})+
	};
}

impl_one!(u8 u16 u32 u64 u128 usize);
impl_one!(i8 i16 i32 i64 i128 isize);

/// This trait takes a generator of integers and transforms it into a stream of
/// the bits that compose each of them. This crate already implements it for all
/// integer types, so it only needs to be brought into scope via
/// `use bits::AsBits`.
///
/// If it were to be implemented by some custom numeric type, the trait
/// [One](./trait.One.html) must be implemented for it.
pub trait AsBits {
	type Iter: Iterator;

	/// Transforms an iterator of integers into a stream of the bits that
	/// compose each of them.
	///
	/// # Examples
	///
	/// ```rust
	/// use bits::AsBits;
	///
	/// let mut bits = [0b1011_0101u8, 0b0100_1110].iter().as_bits();
	/// assert_eq!(bits.next(), Some(1));
	/// assert_eq!(bits.next(), Some(0));
	/// assert_eq!(bits.nth(6), Some(0)); // The next byte
	/// assert_eq!(bits.nth(6), Some(0)); // The last bit
	/// assert_eq!(bits.next(), None);
	/// assert_eq!(bits.next_back(), Some(0)); // It's also double-ended!
	/// ```
	fn as_bits(self) -> Bits<Self::Iter>;
}

#[derive(Clone)]
pub struct Bits<I>
where
	I: Iterator,
{
	unit: I::Item,
	shift: usize,
	source: I,
	rev_unit: I::Item,
	rev_shift: usize,
	rev_source: I,
}

impl<I, T> Bits<I>
where
	Self: Iterator,
	<Self as Iterator>::Item: PartialEq + One,
	I: Iterator<Item = T> + DoubleEndedIterator + Clone,
	T: Default,
{
	fn new(mut source: I) -> Self {
		let mut rev_source = source.clone();
		let rev_unit = rev_source.next_back().unwrap_or_default();
		let unit = source.next().unwrap_or_default();
		let size = mem::size_of::<T>() * 8;
		Bits {
			unit,
			shift: size,
			source,
			rev_unit,
			rev_shift: 0,
			rev_source,
		}
	}

	// There's seemingly no difference in keeping the size in memory and
	// calculating it each time, so might as well lower the memory footprint!
	#[inline]
	fn unit_size(&self) -> usize {
		mem::size_of::<T>() * 8
	}

	/// Returns the next `n` as `Some<usize>`. If there aren't enough bits in the
	/// stream, returns `None` instead. This, otherwise, makes no guarantees in
	/// regards to the size of `n`, meaning that if `usize` is 64-bits long and
	/// `n` equals 65, some information might be lost.
	///
	/// It should be noted that this advances the internal state of the iterator.
	///
	/// # Examples
	///
	/// ```rust
	/// use bits::AsBits;
	///
	/// let mut bit_stream = [0b1100u8].iter().as_bits();
	/// assert_eq!(bit_stream.get_bits(4), Some(0));
	/// assert_eq!(bit_stream.get_bits(2), Some(3)); // 0b11
	/// assert_eq!(bit_stream.get_bits(3), None);
	/// ```
	pub fn get_bits(&mut self, n: usize) -> Option<usize> {
		let mut bits = 0;
		for _ in 0..n {
			let bit = self.next()?;
			bits <<= 1;
			bits |= if bit == <Self as Iterator>::Item::one() {
				1
			} else {
				0
			};
		}
		Some(bits)
	}
}

impl<I, T, S, B> Iterator for Bits<I>
where
	I: Iterator<Item = T> + DoubleEndedIterator + Clone,
	T: Copy + Default + Shr<usize, Output = S>,
	S: BitAnd<S, Output = B> + One,
	B: PartialEq + One,
{
	type Item = B;

	fn next(&mut self) -> Option<Self::Item> {
		if self.shift == 0 {
			self.unit = self.source.next()?;
			self.shift = self.unit_size();
		}
		self.shift -= 1;
		Some((self.unit >> self.shift) & S::one())
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let (lo, up) = self.source.size_hint();
		let lo = lo.saturating_mul(self.unit_size());
		let up = up.and_then(|bound| bound.checked_mul(self.unit_size()));
		(lo, up)
	}
}

impl<I, T, S, B> DoubleEndedIterator for Bits<I>
where
	I: Iterator<Item = T> + DoubleEndedIterator + Clone,
	T: Copy + Default + Shr<usize, Output = S>,
	S: BitAnd<S, Output = B> + One,
	B: PartialEq + One,
{
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.rev_shift == self.unit_size() {
			self.rev_unit = self.rev_source.next_back()?;
			self.rev_shift = 0;
		}
		let bit = (self.rev_unit >> self.rev_shift) & S::one();
		self.rev_shift += 1;
		Some(bit)
	}
}

impl<'a, I, T, S, B> AsBits for I
where
	I: Iterator<Item = &'a T> + DoubleEndedIterator + Clone,
	T: 'a + Copy + Default + Shr<usize, Output = S>,
	S: BitAnd<S, Output = B> + One,
	B: PartialEq + One,
{
	type Iter = std::iter::Copied<Self>;

	fn as_bits(self) -> Bits<Self::Iter> {
		Bits::new(self.copied())
	}
}

#[cfg(test)]
mod tests {
	use super::AsBits;

	#[test]
	fn test_unsigned_bytes() {
		let bytes = [0b1100_1000u8, 0b0101_0110];
		let bits = bytes.iter().as_bits();
		let rev_bits = bytes.iter().as_bits().rev();
		let mut all_bits = vec![1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0];
		assert_eq!(bits.collect::<Vec<_>>(), all_bits);
		all_bits.reverse();
		assert_eq!(rev_bits.collect::<Vec<_>>(), all_bits);
	}

	#[test]
	fn test_unsigned_multi_bytes() {
		let bytes = [0b1100_1000_0101_0110u16];
		let bits = bytes.iter().as_bits();
		let rev_bits = bytes.iter().as_bits().rev();
		let mut all_bits = vec![1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0];
		assert_eq!(bits.collect::<Vec<_>>(), all_bits);
		all_bits.reverse();
		assert_eq!(rev_bits.collect::<Vec<_>>(), all_bits);
	}

	#[test]
	fn test_signed_bytes() {
		let bytes = [0b0000_1100i8, 0b0000_1000];
		let bits = bytes.iter().as_bits();
		let rev_bits = bytes.iter().as_bits().rev();
		let mut all_bits = vec![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0];
		assert_eq!(bits.collect::<Vec<_>>(), all_bits);
		all_bits.reverse();
		assert_eq!(rev_bits.collect::<Vec<_>>(), all_bits);
	}

	#[test]
	fn test_signed_multi_bytes() {
		let bytes = [0b0000_0000_1100_1000i16];
		let bits = bytes.iter().as_bits();
		let rev_bits = bytes.iter().as_bits().rev();
		let mut all_bits = vec![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0];
		assert_eq!(bits.collect::<Vec<_>>(), all_bits);
		all_bits.reverse();
		assert_eq!(rev_bits.collect::<Vec<_>>(), all_bits);
	}
}
