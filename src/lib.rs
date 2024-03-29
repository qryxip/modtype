//! This crate provides modular arithmetic integer types.
//!
//! # Usage
//!
//! ## [`modtype::ModType`]
//!
//! ```
//! #[modtype::use_modtype]
//! type F = modtype::F<1_000_000_007u64>;
//!
//! assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
//! ```
//!
//! ## [`modtype::thread_local::ModType`]
//!
//! ```
//! #[allow(non_snake_case)]
//! modtype::thread_local::F::with(1_000_000_007u64, |F| {
//!     assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
//! });
//! ```
//!
//! ## [`modtype::non_static::ModType`]
//!
//! ```
//! #[allow(non_snake_case)]
//! let F = modtype::non_static::F::factory(1_000_000_007u64);
//!
//! assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
//! ```
//!
//! # Customization
//!
//! `ModType`s can be customized via [`modtype::Cartridge`].
//!
//! ## [`modtype::cartridges::AllowFlexibleRhs`]
//!
//! ```
//! use modtype::cartridges::{AllowFlexibleRhs, Field};
//! use num::{BigInt, BigRational};
//!
//! #[modtype::use_modtype]
//! type F = modtype::ModType<AllowFlexibleRhs<Field<u64>>, 1_000_000_007u64>;
//!
//! let mut x = F(1);
//! x += F(1);
//! x += 1u64;
//! x += 1i32;
//! x += 1f64;
//! x += BigInt::from(1u32);
//! x += BigRational::new(BigInt::from(1u32), BigInt::from(1u32));
//! assert_eq!(x, F(7));
//! ```
//!
//! ## [`modtype::cartridges::Multiplicative`]
//!
//! ```
//! use num::CheckedDiv as _;
//!
//! #[modtype::use_modtype]
//! type Z = modtype::ModType<modtype::cartridges::Multiplicative<u32>, 57u32>;
//!
//! assert_eq!(Z(56) * Z(56), Z(1));
//! assert_eq!(Z(1).checked_div(&Z(13)), Some(Z(22))); // 13・22 ≡ 1 (mod 57)
//! ```
//!
//! ## [`modtype::cartridges::Additive`]
//!
//! ```
//! use num::CheckedAdd as _;
//!
//! #[modtype::use_modtype]
//! type Z = modtype::ModType<modtype::cartridges::Additive<u64>, 1_000_000_007u64>;
//!
//! let mut x = Z(1_000_000_006);
//!
//! x += Z(1);
//! assert_eq!(*x.get_mut_unchecked(), 1_000_000_007);
//!
//! x += Z(u64::max_value() / 2 - 1_000_000_007);
//! assert_eq!(*x.get_mut_unchecked(), u64::max_value() / 2);
//!
//! x += Z(1);
//! assert_eq!(*x.get_mut_unchecked(), (u64::max_value() / 2 + 1) % 1_000_000_007);
//! ```
//!
//! ## [`modtype::cartridges::ManuallyAdjust`]
//!
//! ```
//! use num::CheckedAdd as _;
//!
//! #[modtype::use_modtype]
//! type Z = modtype::ModType<modtype::cartridges::ManuallyAdjust<u64>, 1_000_000_007u64>;
//!
//! let mut x = Z(1_000_000_006);
//!
//! x += Z(u64::max_value() - 1_000_000_006);
//! assert_eq!(*x.get_mut_unchecked(), u64::max_value());
//!
//! x.adjust();
//! assert_eq!(*x.get_mut_unchecked(), u64::max_value() % 1_000_000_007);
//! ```
//!
//! [`modtype::ModType`]: ./struct.ModType.html
//! [`modtype::thread_local::ModType`]: ./thread_local/struct.ModType.html
//! [`modtype::non_static::ModType`]: ./non_static/struct.ModType.html
//! [`modtype::Cartridge`]: ./trait.Cartridge.html
//! [`modtype::cartridges::AllowFlexibleRhs`]: ./cartridges/enum.AllowFlexibleRhs.html
//! [`modtype::cartridges::Multiplicative`]: ./cartridges/enum.Multiplicative.html
//! [`modtype::cartridges::Additive`]: ./cartridges/enum.Additive.html
//! [`modtype::cartridges::ManuallyAdjust`]: ./cartridges/enum.ManuallyAdjust.html

macro_rules! feature_p {
    (Self::$feature:ident $(,)?) => {
        Self::$feature::VALUE
    };
}

macro_rules! adjust_unless {
    (Self::AssumeAlwaysAdjusted, ($x:ident, $($y:ident)?), $modulus:ident $(,)?) => {
        if Self::AssumeAlwaysAdjusted::VALUE {
            ($x, $($y)*)
        } else {
            (
                <Self as crate::Cartridge>::adjusted($x, $modulus),
                $(<Self as crate::Cartridge>::adjusted($y, $modulus),)*
            )
        }
    };
}

macro_rules! expect_feature {
    (Self::$feature:ident $(,)?) => {
        Self::$feature::expect(concat!(
            "this implementation always panics since `Self::",
            stringify!($feature),
            " = False`.",
        ))
    };
}

pub use modtype_derive::{use_modtype, ConstValue, ModType};

use crate::sealed::Sealed;

use num::integer::ExtendedGcd;
use num::rational::Ratio;
use num::{
    integer, BigInt, BigUint, Bounded, Float, FromPrimitive, Integer, Num, One as _, PrimInt,
    Signed, ToPrimitive as _, Unsigned, Zero as _,
};
use rand::Rng;

use std::cell::UnsafeCell;
use std::convert::{TryFrom as _, TryInto as _};
use std::iter::{Product, Sum};
use std::marker::PhantomData;
use std::num::ParseIntError;
use std::ops::{
    AddAssign, BitAndAssign, BitOrAssign, BitXorAssign, DivAssign, MulAssign, Range, RemAssign,
    SubAssign,
};
use std::str::FromStr;
use std::thread::LocalKey;
use std::{cmp, fmt, mem};

/// A trait for `u8`, `u16`, `u32`, `u64`, `u128`, and `usize`.
pub trait UnsignedPrimitive:
    Sealed
    + Unsigned
    + PrimInt
    + Integer
    + Num<FromStrRadixErr = ParseIntError>
    + Bounded
    + FromStr<Err = ParseIntError>
    + FromPrimitive
    + Into<BigUint>
    + Into<BigInt>
    + Default
    + fmt::Display
    + fmt::Debug
    + fmt::LowerHex
    + fmt::UpperHex
    + Sum
    + Product
    + AddAssign
    + SubAssign
    + MulAssign
    + DivAssign
    + RemAssign
    + BitAndAssign
    + BitOrAssign
    + BitXorAssign
    + Send
    + Sync
    + 'static
{
    type Signed: SignedPrimitive;
    type Range: DoubleEndedIterator<Item = Self>;

    fn random<R: Rng>(rng: &mut R) -> Self;
    fn try_from_biguint(biguint: BigUint) -> Option<Self>;
    fn try_from_bigint(bigint: BigInt) -> Option<Self>;
    fn try_from_signed(signed: Self::Signed) -> Option<Self>;
    fn try_into_signed(self) -> Option<Self::Signed>;
    fn rem_biguint(self, biguint: BigUint) -> BigUint;
    fn rem_bigint(self, bigint: BigInt) -> BigInt;
    fn range(self, end: Self) -> Self::Range;
    fn thread_local_modulus_key() -> &'static LocalKey<UnsafeCell<Self>>;

    /// # Safety
    ///
    /// This function is safe as long as `Self::thread_local_modulus_key().with` does not leak the raw pointer.
    unsafe fn thread_local_modulus() -> Self {
        Self::thread_local_modulus_key().with(|m| *m.get())
    }

    /// # Safety
    ///
    /// This function is safe as long as `Self::thread_local_modulus_key().with` does not leak the raw pointer.
    unsafe fn set_thread_local_modulus(modulus: Self) {
        Self::thread_local_modulus_key().with(|m| *m.get() = modulus)
    }
}

impl UnsignedPrimitive for u8 {
    type Signed = i8;
    type Range = Range<u8>;

    #[inline]
    fn random<R: Rng>(rng: &mut R) -> Self {
        rng.gen()
    }

    #[inline]
    fn try_from_biguint(biguint: BigUint) -> Option<Self> {
        biguint.to_u8()
    }

    #[inline]
    fn try_from_bigint(bigint: BigInt) -> Option<Self> {
        bigint.to_u8()
    }

    #[inline]
    fn try_from_signed(signed: i8) -> Option<Self> {
        Self::try_from(signed).ok()
    }

    #[inline]
    fn try_into_signed(self) -> Option<i8> {
        self.try_into().ok()
    }

    #[inline]
    fn rem_biguint(self, biguint: BigUint) -> BigUint {
        biguint % self
    }

    #[inline]
    fn rem_bigint(self, bigint: BigInt) -> BigInt {
        bigint % self
    }

    #[inline]
    fn range(self, end: Self) -> Range<Self> {
        self..end
    }

    #[inline]
    fn thread_local_modulus_key() -> &'static LocalKey<UnsafeCell<Self>> {
        thread_local!(static MODULUS: UnsafeCell<u8> = UnsafeCell::new(0));
        &MODULUS
    }
}

impl UnsignedPrimitive for u16 {
    type Signed = i16;
    type Range = Range<u16>;

    #[inline]
    fn random<R: Rng>(rng: &mut R) -> Self {
        rng.gen()
    }

    #[inline]
    fn try_from_biguint(biguint: BigUint) -> Option<Self> {
        biguint.to_u16()
    }

    #[inline]
    fn try_from_bigint(bigint: BigInt) -> Option<Self> {
        bigint.to_u16()
    }

    #[inline]
    fn try_from_signed(signed: i16) -> Option<Self> {
        Self::try_from(signed).ok()
    }

    #[inline]
    fn try_into_signed(self) -> Option<i16> {
        self.try_into().ok()
    }

    #[inline]
    fn rem_biguint(self, biguint: BigUint) -> BigUint {
        biguint % self
    }

    #[inline]
    fn rem_bigint(self, bigint: BigInt) -> BigInt {
        bigint % self
    }

    #[inline]
    fn range(self, end: Self) -> Range<Self> {
        self..end
    }

    #[inline]
    fn thread_local_modulus_key() -> &'static LocalKey<UnsafeCell<Self>> {
        thread_local!(static MODULUS: UnsafeCell<u16> = UnsafeCell::new(0));
        &MODULUS
    }
}

impl UnsignedPrimitive for u32 {
    type Signed = i32;
    type Range = Range<u32>;

    #[inline]
    fn random<R: Rng>(rng: &mut R) -> Self {
        rng.gen()
    }

    #[inline]
    fn try_from_biguint(biguint: BigUint) -> Option<Self> {
        biguint.to_u32()
    }

    #[inline]
    fn try_from_bigint(bigint: BigInt) -> Option<Self> {
        bigint.to_u32()
    }

    #[inline]
    fn try_from_signed(signed: i32) -> Option<Self> {
        Self::try_from(signed).ok()
    }

    #[inline]
    fn try_into_signed(self) -> Option<i32> {
        self.try_into().ok()
    }

    #[inline]
    fn rem_biguint(self, biguint: BigUint) -> BigUint {
        biguint % self
    }

    #[inline]
    fn rem_bigint(self, bigint: BigInt) -> BigInt {
        bigint % self
    }

    #[inline]
    fn range(self, end: Self) -> Range<Self> {
        self..end
    }

    #[inline]
    fn thread_local_modulus_key() -> &'static LocalKey<UnsafeCell<Self>> {
        thread_local!(static MODULUS: UnsafeCell<u32> = UnsafeCell::new(0));
        &MODULUS
    }
}

impl UnsignedPrimitive for u64 {
    type Signed = i64;
    type Range = Range<u64>;

    #[inline]
    fn random<R: Rng>(rng: &mut R) -> Self {
        rng.gen()
    }

    #[inline]
    fn try_from_biguint(biguint: BigUint) -> Option<Self> {
        biguint.to_u64()
    }

    #[inline]
    fn try_from_bigint(bigint: BigInt) -> Option<Self> {
        bigint.to_u64()
    }

    #[inline]
    fn try_from_signed(signed: i64) -> Option<Self> {
        Self::try_from(signed).ok()
    }

    #[inline]
    fn try_into_signed(self) -> Option<i64> {
        self.try_into().ok()
    }

    #[inline]
    fn rem_biguint(self, biguint: BigUint) -> BigUint {
        biguint % self
    }

    #[inline]
    fn rem_bigint(self, bigint: BigInt) -> BigInt {
        bigint % self
    }

    #[inline]
    fn range(self, end: Self) -> Range<Self> {
        self..end
    }

    #[inline]
    fn thread_local_modulus_key() -> &'static LocalKey<UnsafeCell<Self>> {
        thread_local!(static MODULUS: UnsafeCell<u64> = UnsafeCell::new(0));
        &MODULUS
    }
}

impl UnsignedPrimitive for u128 {
    type Signed = i128;
    type Range = Range<u128>;

    #[inline]
    fn random<R: Rng>(rng: &mut R) -> Self {
        rng.gen()
    }

    #[inline]
    fn try_from_biguint(biguint: BigUint) -> Option<Self> {
        biguint.to_u128()
    }

    #[inline]
    fn try_from_bigint(bigint: BigInt) -> Option<Self> {
        bigint.to_u128()
    }

    #[inline]
    fn try_from_signed(signed: i128) -> Option<Self> {
        Self::try_from(signed).ok()
    }

    #[inline]
    fn try_into_signed(self) -> Option<i128> {
        self.try_into().ok()
    }

    #[inline]
    fn rem_biguint(self, biguint: BigUint) -> BigUint {
        biguint % self
    }

    #[inline]
    fn rem_bigint(self, bigint: BigInt) -> BigInt {
        bigint % self
    }

    #[inline]
    fn range(self, end: Self) -> Range<Self> {
        self..end
    }

    #[inline]
    fn thread_local_modulus_key() -> &'static LocalKey<UnsafeCell<Self>> {
        thread_local!(static MODULUS: UnsafeCell<u128> = UnsafeCell::new(0));
        &MODULUS
    }
}

impl UnsignedPrimitive for usize {
    type Signed = isize;
    type Range = Range<usize>;

    #[inline]
    fn random<R: Rng>(rng: &mut R) -> Self {
        rng.gen()
    }

    #[inline]
    fn try_from_biguint(biguint: BigUint) -> Option<Self> {
        biguint.to_usize()
    }

    #[inline]
    fn try_from_bigint(bigint: BigInt) -> Option<Self> {
        bigint.to_usize()
    }

    #[inline]
    fn try_from_signed(signed: isize) -> Option<Self> {
        Self::try_from(signed).ok()
    }

    #[inline]
    fn try_into_signed(self) -> Option<isize> {
        self.try_into().ok()
    }

    #[inline]
    fn rem_biguint(self, biguint: BigUint) -> BigUint {
        biguint % self
    }

    #[inline]
    fn rem_bigint(self, bigint: BigInt) -> BigInt {
        bigint % self
    }

    #[inline]
    fn range(self, end: Self) -> Range<Self> {
        self..end
    }

    #[inline]
    fn thread_local_modulus_key() -> &'static LocalKey<UnsafeCell<Self>> {
        thread_local!(static MODULUS: UnsafeCell<usize> = UnsafeCell::new(0));
        &MODULUS
    }
}

/// A trait for `i8`, `i16`, `i32`, `i64`, `i128`, and `isize`.
pub trait SignedPrimitive:
    Sealed
    + Signed
    + PrimInt
    + Integer
    + Num<FromStrRadixErr = ParseIntError>
    + Bounded
    + FromStr<Err = ParseIntError>
    + FromPrimitive
    + Into<BigInt>
    + Default
    + fmt::Display
    + fmt::Debug
    + fmt::LowerHex
    + fmt::UpperHex
    + Sum
    + Product
    + AddAssign
    + SubAssign
    + MulAssign
    + DivAssign
    + RemAssign
    + BitAndAssign
    + BitOrAssign
    + BitXorAssign
    + Send
    + Sync
    + 'static
{
}

impl SignedPrimitive for i8 {}
impl SignedPrimitive for i16 {}
impl SignedPrimitive for i32 {}
impl SignedPrimitive for i64 {}
impl SignedPrimitive for i128 {}
impl SignedPrimitive for isize {}

/// A trait for `f32` and `f64`.
pub trait FloatPrimitive:
    Sealed
    + Signed
    + Float
    + Num<FromStrRadixErr = num::traits::ParseFloatError>
    + FromStr<Err = std::num::ParseFloatError>
    + FromPrimitive
    + Default
    + fmt::Display
    + fmt::Debug
    + Sum
    + Product
    + AddAssign
    + SubAssign
    + MulAssign
    + DivAssign
    + RemAssign
    + Send
    + Sync
    + 'static
{
}

impl FloatPrimitive for f32 {}
impl FloatPrimitive for f64 {}

/// A trait that has one associated constant value.
///
/// To implement this trait, use [`use_modtype`] rather than [the derive macro].
///
/// # Example
///
/// ```
/// use modtype::ConstValue;
///
/// #[derive(ConstValue)]
/// #[modtype(const_value = 17u32)]
/// enum Const17U32 {}
///
/// assert_eq!(Const17U32::VALUE, 17u32);
/// ```
///
/// [`use_modtype`]: https://docs.rs/modtype_derive/0.7/modtype_derive/attr.use_modtype.html
/// [the derive macro]: https://docs.rs/modtype_derive/0.7/modtype_derive/derive.ConstValue.html
pub trait ConstValue {
    type Value: Copy;
    const VALUE: Self::Value;
}

/// Actual implementation.
///
/// Note that in the default assumes:
/// - The modulus is larger than `1`.
/// - `(modulus - 1) + (modulus - 1)` does not overflow.
/// - `(modulus - 1) * (modulus - 1)` does not overflow.
pub trait Cartridge {
    type Target: UnsignedPrimitive;
    type AssumePrimeModulus: TypedBool;
    type AssumeAlwaysAdjusted: TypedBool;
    type Equality: TypedBool;
    type Order: TypedBool;
    type Deref: TypedBool;
    type PartialAddition: TypedBool;
    type PartialSubtraction: TypedBool;
    type PartialMultiplication: TypedBool;
    type PartialDivision: TypedBool;
    type FlexibleRhs: TypedBool;

    /// Implementation for [`From`]`<Self::Target>` and `modtype{, ::thread_local}::ModType::new`.
    ///
    /// This method should not be overridden.
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    #[inline(always)]
    fn new<T: PrimInt>(mut raw: T, modulus: T) -> T {
        if Self::should_adjust(raw, modulus) {
            Self::adjust(&mut raw, modulus);
        }
        raw
    }

    /// Whether to call `Self::`[`adjust`].
    ///
    /// The default implementation returns `raw >= modulus`.
    /// If `Self::`[`AssumeAlwaysAdjusted`], this method should not be overridden.
    ///
    /// [`AssumeAlwaysAdjusted`]: ./trait.Cartridge.html#associatedtype.AssumeAlwaysAdjusted
    /// [`adjust`]: ./trait.Cartridge.html#method.adjust
    #[inline(always)]
    fn should_adjust<T: PrimInt>(raw: T, modulus: T) -> bool {
        raw >= modulus
    }

    /// Make `*raw` `*raw % modulus`.
    ///
    /// This method should not be overridden.
    #[inline(always)]
    fn adjust<T: PrimInt>(raw: &mut T, modulus: T) {
        *raw = *raw % modulus;
    }

    /// Make `raw` `raw % modulus`.
    ///
    /// This method should not be overridden.
    #[inline(always)]
    fn adjusted<T: PrimInt>(mut raw: T, modulus: T) -> T {
        if raw >= modulus {
            Self::adjust(&mut raw, modulus);
        }
        raw
    }

    /// Implementation for `modtype{, ::thread_local, ::non_static}::ModType::sqrt`.
    ///
    /// The default implementation uses [Tonelli–Shanks algorithm].
    ///
    /// # Panics
    ///
    /// The default implementation always panics if `Self::`[`AssumePrimeModulus`] is [`False`].
    ///
    /// [Tonelli–Shanks algorithm]: https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm
    /// [`AssumePrimeModulus`]: ./trait.Cartridge.html#associatedtype.AssumePrimeModulus
    /// [`False`]: ./enum.False.html
    #[inline(always)]
    fn sqrt(value: Self::Target, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::PartialMultiplication: IsTrue,
    {
        expect_feature!(Self::AssumePrimeModulus);
        let (value,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (value,), modulus);

        macro_rules! id {
            (0) => {
                Self::Target::zero()
            };
            (1) => {
                Self::Target::one()
            };
            (2) => {{
                id!(1) + id!(1)
            }};
        }

        let (n, p) = (value, modulus);

        let (q, s) = {
            let (mut q, mut s) = (p - id!(1), id!(0));
            while q & id!(1) == id!(0) {
                q /= id!(2);
                s += id!(1);
            }
            (q, s)
        };

        let z = {
            let mut rng = rand::thread_rng();
            loop {
                let z = Self::Target::random(&mut rng) % p;
                if Self::pow_unsigned(z, (p - id!(1)) / id!(2), p) == p - id!(1) {
                    break z;
                }
            }
        };

        let mut m = s;
        let mut c = Self::pow_unsigned(z, q, p);
        let mut t = Self::pow_unsigned(n, q, p);
        let mut r = Self::pow_unsigned(n, (q + id!(1)) / id!(2), p);

        Some(loop {
            if t == id!(0) {
                break id!(0);
            }
            if t == id!(1) {
                break r;
            }

            let i = {
                let (mut acc, mut i) = (Self::mul(t, t, p), id!(1));
                loop {
                    if i == m {
                        return None;
                    }
                    if acc == id!(1) {
                        break i;
                    }
                    acc = Self::mul(acc, acc, p);
                    i += id!(1);
                }
            };

            let b = {
                let mut b = c;
                for _ in id!(0).range(m - i - id!(1)) {
                    b = Self::mul(b, b, p);
                }
                b
            };

            m = i;
            c = Self::mul(b, b, p);
            t = Self::mul(t, Self::mul(b, b, p), p);
            r = Self::mul(r, b, p);
        })
    }

    /// Implementation for [`From`]`::<`[`u8`]`>` and [`FromPrimitive`]`::`[`from_u8`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_u8`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_u8
    #[inline(always)]
    fn from_u8(value: u8, modulus: Self::Target) -> Self::Target {
        if let Some(value) = Self::Target::from_u8(value) {
            Self::new(value, modulus)
        } else {
            let modulus = modulus.to_u8().unwrap();
            Self::Target::from_u8(Self::new(value, modulus)).unwrap()
        }
    }

    /// Implementation for [`From`]`::<`[`u16`]`>` and [`FromPrimitive`]`::`[`from_u16`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_u16`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_u16
    #[inline(always)]
    fn from_u16(value: u16, modulus: Self::Target) -> Self::Target {
        if let Some(value) = Self::Target::from_u16(value) {
            Self::new(value, modulus)
        } else {
            let modulus = modulus.to_u16().unwrap();
            Self::Target::from_u16(Self::new(value, modulus)).unwrap()
        }
    }

    /// Implementation for [`From`]`::<`[`u32`]`>` and [`FromPrimitive`]`::`[`from_u32`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_u32`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_u32
    #[inline(always)]
    fn from_u32(value: u32, modulus: Self::Target) -> Self::Target {
        if let Some(value) = Self::Target::from_u32(value) {
            Self::new(value, modulus)
        } else {
            let modulus = modulus.to_u32().unwrap();
            Self::Target::from_u32(Self::new(value, modulus)).unwrap()
        }
    }

    /// Implementation for [`From`]`::<`[`u64`]`>` and [`FromPrimitive`]`::`[`from_u64`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_u64`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#tymethod.from_u64
    #[inline(always)]
    fn from_u64(value: u64, modulus: Self::Target) -> Self::Target {
        if let Some(value) = Self::Target::from_u64(value) {
            Self::new(value, modulus)
        } else {
            let modulus = modulus.to_u64().unwrap();
            Self::Target::from_u64(Self::new(value, modulus)).unwrap()
        }
    }

    /// Implementation for [`From`]`::<`[`u128`]`>` and [`FromPrimitive`]`::`[`from_u128`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_u128`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_u128
    #[inline(always)]
    fn from_u128(value: u128, modulus: Self::Target) -> Self::Target {
        if let Some(value) = Self::Target::from_u128(value) {
            Self::new(value, modulus)
        } else {
            let modulus = modulus.to_u128().unwrap();
            Self::Target::from_u128(Self::new(value, modulus)).unwrap()
        }
    }

    /// Implementation for [`From`]`::<`[`usize`]`>` and [`FromPrimitive`]`::`[`from_usize`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_usize`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_usize
    #[inline(always)]
    fn from_usize(value: usize, modulus: Self::Target) -> Self::Target {
        if let Some(value) = Self::Target::from_usize(value) {
            Self::new(value, modulus)
        } else {
            let modulus = modulus.to_usize().unwrap();
            Self::Target::from_usize(Self::new(value, modulus)).unwrap()
        }
    }

    /// Implementation for [`From`]`::<`[`i8`]`>` and [`FromPrimitive`]`::`[`from_i8`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_i8`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_i8
    #[inline(always)]
    fn from_i8(value: i8, modulus: Self::Target) -> Self::Target
    where
        Self::PartialSubtraction: IsTrue,
    {
        let (value_abs, is_neg) = if value < 0 {
            (-value, true)
        } else {
            (value, false)
        };

        let acc = if let Some(value_abs) = Self::Target::from_i8(value_abs) {
            Self::new(value_abs, modulus)
        } else {
            let modulus = modulus.to_i8().unwrap();
            Self::Target::from_i8(Self::new(value_abs, modulus)).unwrap()
        };

        if is_neg {
            Self::neg(acc, modulus)
        } else {
            acc
        }
    }

    /// Implementation for [`From`]`::<`[`i16`]`>` and [`FromPrimitive`]`::`[`from_i16`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_i16`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_i16
    #[inline(always)]
    fn from_i16(value: i16, modulus: Self::Target) -> Self::Target
    where
        Self::PartialSubtraction: IsTrue,
    {
        let (value_abs, is_neg) = if value < 0 {
            (-value, true)
        } else {
            (value, false)
        };

        let acc = if let Some(value_abs) = Self::Target::from_i16(value_abs) {
            Self::new(value_abs, modulus)
        } else {
            let modulus = modulus.to_i16().unwrap();
            Self::Target::from_i16(Self::new(value_abs, modulus)).unwrap()
        };

        if is_neg {
            Self::neg(acc, modulus)
        } else {
            acc
        }
    }

    /// Implementation for [`From`]`::<`[`i32`]`>` and [`FromPrimitive`]`::`[`from_i32`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_i32`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_i32
    #[inline(always)]
    fn from_i32(value: i32, modulus: Self::Target) -> Self::Target
    where
        Self::PartialSubtraction: IsTrue,
    {
        let (value_abs, is_neg) = if value < 0 {
            (-value, true)
        } else {
            (value, false)
        };

        let acc = if let Some(value_abs) = Self::Target::from_i32(value_abs) {
            Self::new(value_abs, modulus)
        } else {
            let modulus = modulus.to_i32().unwrap();
            Self::Target::from_i32(Self::new(value_abs, modulus)).unwrap()
        };

        if is_neg {
            Self::neg(acc, modulus)
        } else {
            acc
        }
    }

    /// Implementation for [`From`]`::<`[`i64`]`>` and [`FromPrimitive`]`::`[`from_i64`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_i64`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#tymethod.from_i64
    #[inline(always)]
    fn from_i64(value: i64, modulus: Self::Target) -> Self::Target
    where
        Self::PartialSubtraction: IsTrue,
    {
        let (value_abs, is_neg) = if value < 0 {
            (-value, true)
        } else {
            (value, false)
        };

        let acc = if let Some(value_abs) = Self::Target::from_i64(value_abs) {
            Self::new(value_abs, modulus)
        } else {
            let modulus = modulus.to_i64().unwrap();
            Self::Target::from_i64(Self::new(value_abs, modulus)).unwrap()
        };

        if is_neg {
            Self::neg(acc, modulus)
        } else {
            acc
        }
    }

    /// Implementation for [`From`]`::<`[`i128`]`>` and [`FromPrimitive`]`::`[`from_i128`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_i128`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_i128
    #[inline(always)]
    fn from_i128(value: i128, modulus: Self::Target) -> Self::Target
    where
        Self::PartialSubtraction: IsTrue,
    {
        let (value_abs, is_neg) = if value < 0 {
            (-value, true)
        } else {
            (value, false)
        };

        let acc = if let Some(value_abs) = Self::Target::from_i128(value_abs) {
            Self::new(value_abs, modulus)
        } else {
            let modulus = modulus.to_i128().unwrap();
            Self::Target::from_i128(Self::new(value_abs, modulus)).unwrap()
        };

        if is_neg {
            Self::neg(acc, modulus)
        } else {
            acc
        }
    }

    /// Implementation for [`From`]`::<`[`isize`]`>` and [`FromPrimitive`]`::`[`from_isize`].
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_isize`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#tymethod.from_isize
    #[inline(always)]
    fn from_isize(value: isize, modulus: Self::Target) -> Self::Target
    where
        Self::PartialSubtraction: IsTrue,
    {
        let (value_abs, is_neg) = if value < 0 {
            (-value, true)
        } else {
            (value, false)
        };

        let acc = if let Some(value_abs) = Self::Target::from_isize(value_abs) {
            Self::new(value_abs, modulus)
        } else {
            let modulus = modulus.to_isize().unwrap();
            Self::Target::from_isize(Self::new(value_abs, modulus)).unwrap()
        };

        if is_neg {
            Self::neg(acc, modulus)
        } else {
            acc
        }
    }

    /// Implementation for [`From`]`::<`[`f32`]`, `[`f64`]`>` and [`FromPrimitive`]`::{`[`from_f32`]`, `[`from_f64`]`}`.
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
    /// [`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_f32`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_f32
    /// [`from_f64`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_f64
    #[inline(always)]
    fn from_float_prim<F: FloatPrimitive>(value: F, modulus: Self::Target) -> Self::Target
    where
        Self::AssumePrimeModulus: IsTrue,
        Self::PartialSubtraction: IsTrue,
        Self::PartialMultiplication: IsTrue,
        Self::PartialDivision: IsTrue,
    {
        macro_rules! id {
            (2) => {
                Self::Target::one() + Self::Target::one()
            };
        }

        let (man, exp, sign) = value.integer_decode();
        let acc = Self::mul(
            Self::from_u64(man, modulus),
            Self::pow_signed(id!(2), exp, modulus),
            modulus,
        );
        match sign {
            -1 => Self::neg(acc, modulus),
            _ => acc,
        }
    }

    /// Implementation for [`From`]`<`[`BigUint`]`>`.
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`BigUint`]: https://docs.rs/num-bigint/0.2/num_bigint/struct.BigUint.html
    #[inline(always)]
    fn from_biguint(value: BigUint, modulus: Self::Target) -> Self::Target {
        Self::Target::try_from_biguint(modulus.rem_biguint(value)).unwrap()
    }

    /// Implementation for [`From`]`<`[`BigInt`]`>`.
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`BigInt`]: https://docs.rs/num-bigint/0.2/num_bigint/struct.BigInt.html
    #[inline(always)]
    fn from_bigint(mut value: BigInt, modulus: Self::Target) -> Self::Target
    where
        Self::PartialSubtraction: IsTrue,
    {
        let is_neg = value.is_negative();
        if is_neg {
            value = -value;
        }

        let acc = Self::Target::try_from_bigint(modulus.rem_bigint(value)).unwrap();

        if is_neg {
            Self::neg(acc, modulus)
        } else {
            acc
        }
    }

    /// Implementation for [`From`]`<`[`Ratio`]`<`[`BigUint`]`>>`.
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`Ratio`]: https://docs.rs/num-rational/0.2/num_rational/struct.Ratio.html
    /// [`BigUint`]: https://docs.rs/num-bigint/0.2/num_bigint/struct.BigUint.html
    #[inline(always)]
    fn from_biguint_ratio(value: Ratio<BigUint>, modulus: Self::Target) -> Self::Target
    where
        Self::AssumePrimeModulus: IsTrue,
        Self::PartialDivision: IsTrue,
    {
        let numer = modulus.rem_biguint(value.numer().clone());
        let numer = Self::Target::try_from_biguint(numer).unwrap();
        let denom = modulus.rem_biguint(value.denom().clone());
        let denom = Self::Target::try_from_biguint(denom).unwrap();

        Self::div(numer, denom, modulus)
    }

    /// Implementation for [`From`]`<`[`Ratio`]`<`[`BigInt`]`>>`.
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    /// [`Ratio`]: https://docs.rs/num-rational/0.2/num_rational/struct.Ratio.html
    /// [`BigInt`]: https://docs.rs/num-bigint/0.2/num_bigint/struct.BigInt.html
    #[inline(always)]
    fn from_bigint_ratio(value: Ratio<BigInt>, modulus: Self::Target) -> Self::Target
    where
        Self::AssumePrimeModulus: IsTrue,
        Self::PartialSubtraction: IsTrue,
        Self::PartialDivision: IsTrue,
    {
        let (is_neg, numer, denom) = if value.numer().is_negative() && value.denom().is_negative() {
            (false, -value.numer(), -value.denom())
        } else if value.numer().is_negative() {
            (true, -value.numer(), value.denom().clone())
        } else if value.denom().is_negative() {
            (true, value.numer().clone(), -value.denom())
        } else {
            (false, value.numer().clone(), value.denom().clone())
        };

        let numer = modulus.rem_bigint(numer);
        let numer = Self::Target::try_from_bigint(numer).unwrap();
        let denom = modulus.rem_bigint(denom);
        let denom = Self::Target::try_from_bigint(denom).unwrap();

        let acc = Self::div(numer, denom, modulus);

        if is_neg {
            Self::neg(acc, modulus)
        } else {
            acc
        }
    }

    /// Implementation for [`PartialEq`]`::`[`eq`].
    ///
    /// [`PartialEq`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html
    /// [`eq`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#tymethod.eq
    #[inline(always)]
    fn eq(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> bool
    where
        Self::Equality: IsTrue,
    {
        let (lhs, rhs) = adjust_unless!(Self::AssumeAlwaysAdjusted, (lhs, rhs), modulus);

        lhs == rhs
    }

    /// Implementation for [`PartialOrd`]`::`[`partial_cmp`] and [`Ord`]`::`[`cmp`].
    ///
    /// [`PartialOrd`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html
    /// [`partial_cmp`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#tymethod.partial_cmp
    /// [`Ord`]: https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html
    /// [`cmp`]: https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html#tymethod.cmp
    #[inline(always)]
    fn cmp(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> cmp::Ordering
    where
        Self::Equality: IsTrue,
        Self::Order: IsTrue,
    {
        let (lhs, rhs) = adjust_unless!(Self::AssumeAlwaysAdjusted, (lhs, rhs), modulus);

        lhs.cmp(&rhs)
    }

    /// Implementation for [`Display`].
    ///
    /// [`Display`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html
    #[inline(always)]
    fn fmt_display(
        value: Self::Target,
        modulus: Self::Target,
        fmt: &mut fmt::Formatter,
    ) -> fmt::Result {
        let (value,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (value,), modulus);

        <Self::Target as fmt::Display>::fmt(&value, fmt)
    }

    /// Implementation for [`Debug`].
    ///
    /// [`Debug`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html
    #[inline(always)]
    fn fmt_debug(
        value: Self::Target,
        modulus: Self::Target,
        _ty: &'static str,
        fmt: &mut fmt::Formatter,
    ) -> fmt::Result {
        let (value,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (value,), modulus);

        <Self::Target as fmt::Debug>::fmt(&value, fmt)
    }

    /// Implementation for [`FromStr`].
    ///
    /// [`FromStr`]: https://doc.rust-lang.org/nightly/core/str/trait.FromStr.html
    #[inline(always)]
    fn from_str(str: &str, modulus: Self::Target) -> Result<Self::Target, ParseIntError> {
        str.parse().map(|v| Self::new(v, modulus))
    }

    /// Implementation for [`Neg`].
    ///
    /// [`Neg`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Neg.html
    #[inline(always)]
    fn neg(value: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::PartialSubtraction: IsTrue,
    {
        let (value,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (value,), modulus);

        modulus - value
    }

    /// Implementation for [`Add`].
    ///
    /// [`Add`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Add.html
    #[inline(always)]
    fn add(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::PartialAddition: IsTrue,
    {
        let (lhs, rhs) = adjust_unless!(Self::AssumeAlwaysAdjusted, (lhs, rhs), modulus);

        Self::new(lhs + rhs, modulus)
    }

    /// Implementation for [`Sub`].
    ///
    /// [`Sub`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Sub.html
    #[inline(always)]
    fn sub(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::PartialSubtraction: IsTrue,
    {
        let (lhs, rhs) = adjust_unless!(Self::AssumeAlwaysAdjusted, (lhs, rhs), modulus);

        let acc = if lhs < rhs {
            modulus + lhs - rhs
        } else {
            lhs - rhs
        };
        Self::new(acc, modulus)
    }

    /// Implementation for [`Mul`].
    ///
    /// [`Mul`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Mul.html
    #[inline(always)]
    fn mul(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::PartialMultiplication: IsTrue,
    {
        let (lhs, rhs) = adjust_unless!(Self::AssumeAlwaysAdjusted, (lhs, rhs), modulus);

        Self::new(lhs * rhs, modulus)
    }

    /// Implementation for [`Div`].
    ///
    /// The default implementation is based on [this article].
    ///
    /// # Panics
    ///
    /// The default implementation panics if:
    /// - `rhs`⁻¹ does not exist.
    ///
    /// [`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
    /// [this article]: https://topcoder.g.hatena.ne.jp/iwiwi/20130105/1357363348
    #[inline(always)]
    fn div(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::PartialDivision: IsTrue,
    {
        let (lhs, rhs) = adjust_unless!(Self::AssumeAlwaysAdjusted, (lhs, rhs), modulus);

        if rhs == Self::Target::zero() {
            panic!("attempt to divide by zero");
        }

        let lhs = lhs
            .try_into_signed()
            .expect("too large to convert into signed one");
        let rhs = rhs
            .try_into_signed()
            .expect("too large to convert into signed one");
        let modulus = modulus
            .try_into_signed()
            .expect("too large to convert into signed one");

        let mut a = rhs;
        let mut b = modulus;
        let mut u = <Self::Target as UnsignedPrimitive>::Signed::one();
        let mut v = <Self::Target as UnsignedPrimitive>::Signed::zero();

        while !b.is_zero() {
            let d = a / b;
            a -= b * d;
            u -= v * d;
            mem::swap(&mut a, &mut b);
            mem::swap(&mut u, &mut v);
        }

        let acc = if u.is_negative() {
            lhs * (u + modulus)
        } else {
            lhs * u
        };
        let acc = Self::new(acc, modulus);
        Self::Target::try_from_signed(acc).unwrap()
    }

    /// Implementation for [`Rem`].
    ///
    /// The default implementation always returns `0`.
    ///
    /// # Panics
    ///
    /// The default implementation panics if:
    /// - `rhs` is `0`.
    /// - [`gcd`]`(rhs, modulus)` is not `1`.
    ///
    /// [`Rem`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Rem.html
    /// [`gcd`]: https://docs.rs/num-integer/0.1/num_integer/fn.gcd.html
    #[inline(always)]
    fn rem(_lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::PartialDivision: IsTrue,
    {
        if rhs == Self::Target::zero() {
            panic!("attempt to calculate the remainder with a divisor of zero");
        }
        if !feature_p!(Self::AssumePrimeModulus)
            && integer::gcd(rhs, modulus) != Self::Target::one()
        {
            panic!("cannot divide");
        }
        Self::Target::zero()
    }

    /// Implementation for [`Inv`].
    ///
    /// # Panics
    ///
    /// The default implementation panics if `value`⁻¹ does not exist.
    ///
    /// [`Inv`]: https://docs.rs/num-traits/0.2/num_traits/ops/inv/trait.Inv.html
    #[inline(always)]
    fn inv(value: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::PartialDivision: IsTrue,
    {
        let (value,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (value,), modulus);

        Self::div(Self::Target::one(), value, modulus)
    }

    /// Implementation for [`Num`].
    ///
    /// [`Num`]: https://docs.rs/num-traits/0.2/num_traits/trait.Num.html
    #[inline(always)]
    fn from_str_radix(
        str: &str,
        radix: u32,
        modulus: Self::Target,
    ) -> Result<Self::Target, ParseIntError>
    where
        Self::AssumePrimeModulus: IsTrue,
        Self::Equality: IsTrue,
        Self::Order: IsTrue,
        Self::PartialAddition: IsTrue,
        Self::PartialSubtraction: IsTrue,
        Self::PartialMultiplication: IsTrue,
        Self::PartialDivision: IsTrue,
    {
        Self::Target::from_str_radix(str, radix).map(|v| Self::new(v, modulus))
    }

    /// Implementation for [`Zero`]`::`[`zero`].
    ///
    /// [`Zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html
    /// [`zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html#tymethod.zero
    #[inline(always)]
    fn zero(_modulus: Self::Target) -> Self::Target
    where
        Self::PartialAddition: IsTrue,
    {
        Self::Target::zero()
    }

    /// Implementation for [`Zero`]`::`[`is_zero`].
    ///
    /// [`Zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html
    /// [`is_zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html#tymethod.is_zero
    #[inline(always)]
    fn is_zero(value: Self::Target, modulus: Self::Target) -> bool
    where
        Self::PartialAddition: IsTrue,
    {
        let (value,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (value,), modulus);

        value == Self::Target::zero()
    }

    /// Implementation for [`One`]`::`[`one`].
    ///
    /// [`One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
    /// [`one`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html#tymethod.one
    #[inline(always)]
    fn one(_modulus: Self::Target) -> Self::Target
    where
        Self::PartialMultiplication: IsTrue,
    {
        Self::Target::one()
    }

    /// Implementation for [`One`]`::`[`is_one`].
    ///
    /// [`One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
    /// [`is_one`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html#tymethod.is_one
    #[inline(always)]
    fn is_one(value: Self::Target, modulus: Self::Target) -> bool
    where
        Self::Equality: IsTrue,
        Self::PartialMultiplication: IsTrue,
    {
        let (value,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (value,), modulus);

        value == Self::Target::one()
    }

    /// Implementation for [`CheckedNeg`].
    ///
    /// [`CheckedNeg`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedNeg.html
    #[inline(always)]
    fn checked_neg(value: Self::Target, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::PartialSubtraction: IsTrue,
    {
        let (value,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (value,), modulus);

        Some(Self::neg(value, modulus))
    }

    /// Implementation for [`CheckedAdd`].
    ///
    /// [`CheckedAdd`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedAdd.html
    #[inline(always)]
    fn checked_add(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target>
    where
        Self::PartialAddition: IsTrue,
    {
        let (lhs, rhs) = adjust_unless!(Self::AssumeAlwaysAdjusted, (lhs, rhs), modulus);

        Some(Self::add(lhs, rhs, modulus))
    }

    /// Implementation for [`CheckedSub`].
    ///
    /// [`CheckedSub`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedSub.html
    #[inline(always)]
    fn checked_sub(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target>
    where
        Self::PartialSubtraction: IsTrue,
    {
        let (lhs, rhs) = adjust_unless!(Self::AssumeAlwaysAdjusted, (lhs, rhs), modulus);

        Some(Self::sub(lhs, rhs, modulus))
    }

    /// Implementation for [`CheckedMul`].
    ///
    /// [`CheckedMul`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedMul.html
    #[inline(always)]
    fn checked_mul(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target>
    where
        Self::PartialMultiplication: IsTrue,
    {
        let (lhs, rhs) = adjust_unless!(Self::AssumeAlwaysAdjusted, (lhs, rhs), modulus);

        Some(Self::mul(lhs, rhs, modulus))
    }

    /// Implementation for [`CheckedDiv`].
    ///
    /// [`CheckedDiv`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedDiv.html
    #[inline(always)]
    fn checked_div(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target>
    where
        Self::PartialDivision: IsTrue,
    {
        let (lhs, rhs) = adjust_unless!(Self::AssumeAlwaysAdjusted, (lhs, rhs), modulus);

        if rhs.is_zero() {
            return None;
        }

        let lhs_signed = lhs.try_into_signed()?;
        let rhs_signed = rhs.try_into_signed()?;
        let modulus_signed = modulus.try_into_signed()?;
        let ExtendedGcd { gcd, x, .. } = rhs_signed.extended_gcd(&modulus_signed);

        if lhs_signed % gcd > <Self::Target as UnsignedPrimitive>::Signed::zero() {
            None
        } else {
            let acc = lhs_signed * (x + modulus_signed);
            let acc = Self::adjusted(acc, modulus_signed);
            Self::Target::try_from_signed(acc)
        }
    }

    /// Implementation for [`CheckedRem`].
    ///
    /// [`CheckedRem`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedRem.html
    #[inline(always)]
    fn checked_rem(
        _lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target>
    where
        Self::PartialDivision: IsTrue,
    {
        let (rhs,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (rhs,), modulus);

        if integer::gcd(rhs, modulus) == Self::Target::one() {
            Some(Self::Target::zero())
        } else {
            None
        }
    }

    /// Implementation for [`Pow`]`<{`[`u8`]`, `[`u16`]`, `[`u32`]`, `[`u64`]`, `[`u128`]`, `[`usize`]`}>`.
    ///
    /// [`Pow`]: https://docs.rs/num-traits/0.2/num_traits/pow/trait.Pow.html
    /// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
    /// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
    /// [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
    /// [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
    /// [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
    /// [`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
    #[inline(always)]
    fn pow_unsigned<E: UnsignedPrimitive>(
        base: Self::Target,
        exp: E,
        modulus: Self::Target,
    ) -> Self::Target
    where
        Self::PartialMultiplication: IsTrue,
    {
        let (base,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (base,), modulus);

        let (mut base, mut exp, mut acc) = (base, exp, Self::Target::one());

        while exp > E::zero() {
            if (exp & E::one()) == E::one() {
                acc = Self::mul(acc, base, modulus);
            }
            exp /= E::one() + E::one();
            base = Self::mul(base, base, modulus);
        }

        acc
    }

    /// Implementation for [`Pow`]`<{`[`i8`]`, `[`i16`]`, `[`i32`]`, `[`i64`]`, `[`i128`]`, `[`isize`]`}>`.
    ///
    /// [`Pow`]: https://docs.rs/num-traits/0.2/num_traits/pow/trait.Pow.html
    /// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
    /// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
    /// [`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
    /// [`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
    /// [`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
    /// [`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
    #[inline(always)]
    fn pow_signed<E: SignedPrimitive>(
        base: Self::Target,
        exp: E,
        modulus: Self::Target,
    ) -> Self::Target
    where
        Self::AssumePrimeModulus: IsTrue,
        Self::PartialMultiplication: IsTrue,
        Self::PartialDivision: IsTrue,
    {
        let (base,) = adjust_unless!(Self::AssumeAlwaysAdjusted, (base,), modulus);

        let (mut base, mut exp, mut acc) = (base, exp, Self::Target::one());

        let exp_neg = exp < E::zero();
        if exp_neg {
            exp = -exp;
        }

        while exp > E::zero() {
            if (exp & E::one()) == E::one() {
                acc = Self::mul(acc, base, modulus);
            }
            exp /= E::one() + E::one();
            base = Self::mul(base, base, modulus);
        }

        if exp_neg {
            acc = Self::inv(acc, modulus);
        }

        acc
    }
}

/// Type level boolean.
pub trait TypedBool: Sealed {
    const VALUE: bool;

    /// `panic!(msg)` if `Self` is [`False`].
    ///
    /// [`False`]: ./enum.False.html
    fn expect(msg: &'static str);
}

/// A trait for [`True`].
///
/// [`True`]: ./enum.True.html
pub trait IsTrue: TypedBool {}

/// A [`TypedBool`] which represents "false".
///
/// [`TypedBool`]: ./trait.TypedBool.html
pub enum False {}

impl TypedBool for False {
    const VALUE: bool = false;

    #[inline(always)]
    fn expect(msg: &'static str) {
        panic!(msg);
    }
}

/// A [`TypedBool`] which represents "true".
///
/// [`TypedBool`]: ./trait.TypedBool.html
pub enum True {}

impl TypedBool for True {
    const VALUE: bool = true;

    #[inline(always)]
    fn expect(_: &'static str) {}
}

impl IsTrue for True {}

/// A type alias which [`Cartridge`] is [`modtype::cartridges::Field`]`<M::Value>`.
///
/// [`Cartridge`]: ./trait.Cartridge.html
/// [`modtype::cartridges::Field`]: ./cartridges/type.Field.html
pub type F<M> = ModType<cartridges::Field<<M as ConstValue>::Value>, M>;

/// A modular arithmetic integer type which modulus is **a constant**.
///
/// # Examples
///
/// ```
/// use num::bigint::{ToBigInt as _, ToBigUint as _};
/// use num::pow::Pow as _;
/// use num::rational::Ratio;
/// use num::traits::{CheckedNeg as _, CheckedRem as _, Inv as _};
/// use num::{
///     BigInt, BigUint, CheckedAdd as _, CheckedDiv as _, CheckedMul as _, CheckedSub as _,
///     FromPrimitive as _, Num as _, One as _, ToPrimitive as _, Zero as _,
/// };
///
/// #[modtype::use_modtype]
/// type F = modtype::F<7u32>;
///
/// // Constructor, `new`, `new_unchecked`, `get_mut_unchecked`, `sqrt`
/// assert_eq!(F::new(8), F(1));
/// assert_ne!(F::new_unchecked(8), F(1));
/// assert_eq!(*F(3).get_mut_unchecked(), 3u32);
/// assert_eq!(F(2).sqrt(), Some(F(4)));
///
/// // `From<{{integer}, {float}, BigUint, BigInt, Ratio<BigUint>, Ratio<BigInt>}>`
/// assert_eq!(F::from(3u8), F(3));
/// assert_eq!(F::from(3u16), F(3));
/// assert_eq!(F::from(3u32), F(3));
/// assert_eq!(F::from(3u64), F(3));
/// assert_eq!(F::from(3u128), F(3));
/// assert_eq!(F::from(3usize), F(3));
/// assert_eq!(F::from(-3i8), F(4));
/// assert_eq!(F::from(-3i16), F(4));
/// assert_eq!(F::from(-3i32), F(4));
/// assert_eq!(F::from(-3i64), F(4));
/// assert_eq!(F::from(-3i128), F(4));
/// assert_eq!(F::from(-3isize), F(4));
/// assert_eq!(F::from(0.5f32), F(1) / F(2));
/// assert_eq!(F::from(0.5f64), F(1) / F(2));
/// assert_eq!(F::from(BigUint::from(3u32)), F(3));
/// assert_eq!(F::from(BigInt::from(-4i32)), F(3));
/// assert_eq!(
///     F::from(Ratio::new(BigUint::from(8u32), BigUint::from(3u32))),
///     F(5),
/// );
/// assert_eq!(
///     F::from(Ratio::new(BigInt::from(-1i32), BigInt::from(3u32))),
///     F(2),
/// );
///
/// // `Display`, `Debug`
/// assert_eq!(F(3).to_string(), "3");
/// assert_eq!(format!("{:?}", F(3)), "3");
///
/// // `FromStr`
/// assert_eq!("3".parse::<F>(), Ok(F(3)));
///
/// // `Deref`
/// assert_eq!(*F(3), 3);
/// assert_eq!(F(3).to_i64(), Some(3i64));
/// assert_eq!(F(3).to_biguint(), 3u64.to_biguint());
/// assert_eq!(F(3).to_bigint(), 3u64.to_bigint());
///
/// // `Neg`
/// assert_eq!(-F(1), F(6));
///
/// // `Add`, `Sub`, `Mul`, `Div`, `Rem`
/// assert_eq!(F(3) + F(4), F(0));
/// assert_eq!(F(3) - F(4), F(6));
/// assert_eq!(F(3) * F(4), F(5));
/// assert_eq!(F(3) / F(4), F(6));
/// (0..=6).for_each(|x| (1..=6).for_each(|y| assert_eq!(F(x) % F(y), F(0))));
///
/// // `Num`
/// assert_eq!(F::from_str_radix("111", 2), Ok(F(0)));
///
/// // `Zero`, `One`
/// assert_eq!(F::zero(), F(0));
/// assert_eq!(F::one(), F(1));
///
/// // `FromPrimitive`
/// assert_eq!(F::from_i64(-1), Some(F::from(-1i64)));
///
/// // `Inv`
/// assert_eq!(F(3).inv(), F(5));
///
/// // `CheckedNeg`
/// (0..=6).for_each(|x| assert!(F(x).checked_neg().is_some()));
///
/// // `CheckedAdd`, `CheckedSub`, `CheckedMul`, `CheckedDiv`, `CheckedRem`
/// (0..=6).for_each(|x| (0..=6).for_each(|y| assert!(F(x).checked_add(&F(y)).is_some())));
/// assert_eq!(
///     num::range_step(F(0), F(6), F(2)).collect::<Vec<_>>(),
///     &[F(0), F(2), F(4)],
/// );
/// (0..=6).for_each(|x| (0..=6).for_each(|y| assert!(F(x).checked_sub(&F(y)).is_some())));
/// (0..=6).for_each(|x| (0..=6).for_each(|y| assert!(F(x).checked_mul(&F(y)).is_some())));
/// (0..=6).for_each(|x| (1..=6).for_each(|y| assert!(F(x).checked_div(&F(y)).is_some())));
/// (0..=6).for_each(|x| assert!(F(x).checked_div(&F(0)).is_none()));
/// (0..=6).for_each(|x| (1..=6).for_each(|y| assert!(F(x).checked_rem(&F(y)).is_some())));
/// (0..=6).for_each(|x| assert!(F(x).checked_rem(&F(0)).is_none()));
///
/// // `Pow`
/// assert_eq!(F(3).pow(2u8), F(2));
/// assert_eq!(F(3).pow(2u16), F(2));
/// assert_eq!(F(3).pow(2u32), F(2));
/// assert_eq!(F(3).pow(2u64), F(2));
/// assert_eq!(F(3).pow(2u128), F(2));
/// assert_eq!(F(3).pow(2usize), F(2));
/// assert_eq!(F(3).pow(-2i8), F(4));
/// assert_eq!(F(3).pow(-2i16), F(4));
/// assert_eq!(F(3).pow(-2i32), F(4));
/// assert_eq!(F(3).pow(-2i64), F(4));
/// assert_eq!(F(3).pow(-2i128), F(4));
/// assert_eq!(F(3).pow(-2isize), F(4));
/// ```
#[derive(crate::ModType)]
#[modtype(modulus = "M::VALUE", cartridge = "C", modtype = "crate")]
pub struct ModType<C: Cartridge, M: ConstValue<Value = C::Target>> {
    #[modtype(value)]
    value: C::Target,
    phantom: PhantomData<fn() -> M>,
}

impl<C: Cartridge, M: ConstValue<Value = C::Target>> ModType<C, M> {
    /// Gets the modulus.
    #[inline]
    pub fn modulus() -> C::Target {
        M::VALUE
    }

    /// Creates a new `ModType`.
    #[inline]
    pub fn new(value: C::Target) -> Self {
        Self {
            value: C::new(value, M::VALUE),
            phantom: PhantomData,
        }
    }

    /// Creates a new `ModType` without checking `value`.
    #[inline]
    pub fn new_unchecked(value: C::Target) -> Self {
        Self {
            value,
            phantom: PhantomData,
        }
    }

    /// Returns a mutable reference to the inner value.
    #[inline]
    pub fn get_mut_unchecked(&mut self) -> &mut C::Target {
        &mut self.value
    }

    #[inline]
    pub fn adjust(&mut self)
    where
        C: Cartridge<AssumeAlwaysAdjusted = False>,
    {
        C::adjust(&mut self.value, M::VALUE)
    }

    #[inline]
    pub fn adjusted(self) -> Self
    where
        C: Cartridge<AssumeAlwaysAdjusted = False>,
    {
        Self {
            value: C::adjusted(self.value, M::VALUE),
            phantom: PhantomData,
        }
    }

    /// Returns `r` such that `r * r == self` if it exists.
    #[inline]
    pub fn sqrt(self) -> Option<Self>
    where
        C: Cartridge<PartialMultiplication = True>,
    {
        C::sqrt(self.value, M::VALUE).map(Self::new_unchecked)
    }
}

/// [`Cartridge`]s.
///
/// [`Cartridge`]: ./trait.Cartridge.html
pub mod cartridges {
    use crate::{
        Cartridge, False, FloatPrimitive, IsTrue, SignedPrimitive, True, UnsignedPrimitive,
    };

    use num::rational::Ratio;
    use num::{BigInt, BigUint, PrimInt};

    use std::convert::Infallible;
    use std::marker::PhantomData;
    use std::num::ParseIntError;
    use std::{cmp, fmt};

    /// Allows flexible RHSes.
    ///
    /// ```
    /// use modtype::cartridges::{AllowFlexibleRhs, Field};
    /// use num::{BigInt, BigRational};
    ///
    /// #[modtype::use_modtype]
    /// type F = modtype::ModType<AllowFlexibleRhs<Field<u64>>, 1_000_000_007u64>;
    ///
    /// let mut x = F(1);
    /// x += F(1);
    /// x += 1u64;
    /// x += 1i32;
    /// x += 1f64;
    /// x += BigInt::from(1u32);
    /// x += BigRational::new(BigInt::from(1u32), BigInt::from(1u32));
    /// assert_eq!(x, F(7));
    /// ```
    pub enum AllowFlexibleRhs<C: Cartridge> {
        Infallible(Infallible, PhantomData<fn() -> C>),
    }

    impl<C: Cartridge> Cartridge for AllowFlexibleRhs<C> {
        type Target = C::Target;
        type AssumePrimeModulus = C::AssumePrimeModulus;
        type AssumeAlwaysAdjusted = C::AssumeAlwaysAdjusted;
        type Equality = C::Equality;
        type Order = C::Order;
        type Deref = C::Deref;
        type PartialAddition = C::PartialAddition;
        type PartialSubtraction = C::PartialSubtraction;
        type PartialMultiplication = C::PartialMultiplication;
        type PartialDivision = C::PartialDivision;
        type FlexibleRhs = True;

        #[allow(clippy::new_ret_no_self)]
        #[inline(always)]
        fn new<T: PrimInt>(raw: T, modulus: T) -> T {
            C::new(raw, modulus)
        }

        #[inline(always)]
        fn should_adjust<T: PrimInt>(raw: T, modulus: T) -> bool {
            C::should_adjust(raw, modulus)
        }

        #[inline(always)]
        fn adjust<T: PrimInt>(raw: &mut T, modulus: T) {
            C::adjust(raw, modulus)
        }

        #[inline(always)]
        fn adjusted<T: PrimInt>(raw: T, modulus: T) -> T {
            C::adjusted(raw, modulus)
        }

        #[inline(always)]
        fn sqrt(value: C::Target, modulus: C::Target) -> Option<C::Target>
        where
            C::PartialMultiplication: IsTrue,
        {
            C::sqrt(value, modulus)
        }

        #[inline(always)]
        fn from_u8(value: u8, modulus: C::Target) -> C::Target {
            C::from_u8(value, modulus)
        }

        #[inline(always)]
        fn from_u16(value: u16, modulus: C::Target) -> C::Target {
            C::from_u16(value, modulus)
        }

        #[inline(always)]
        fn from_u32(value: u32, modulus: C::Target) -> C::Target {
            C::from_u32(value, modulus)
        }

        #[inline(always)]
        fn from_u64(value: u64, modulus: C::Target) -> C::Target {
            C::from_u64(value, modulus)
        }

        #[inline(always)]
        fn from_u128(value: u128, modulus: C::Target) -> C::Target {
            C::from_u128(value, modulus)
        }

        #[inline(always)]
        fn from_usize(value: usize, modulus: C::Target) -> C::Target {
            C::from_usize(value, modulus)
        }

        #[inline(always)]
        fn from_i8(value: i8, modulus: C::Target) -> C::Target
        where
            C::PartialSubtraction: IsTrue,
        {
            C::from_i8(value, modulus)
        }

        #[inline(always)]
        fn from_i16(value: i16, modulus: C::Target) -> C::Target
        where
            C::PartialSubtraction: IsTrue,
        {
            C::from_i16(value, modulus)
        }

        #[inline(always)]
        fn from_i32(value: i32, modulus: C::Target) -> C::Target
        where
            C::PartialSubtraction: IsTrue,
        {
            C::from_i32(value, modulus)
        }

        #[inline(always)]
        fn from_i64(value: i64, modulus: C::Target) -> C::Target
        where
            C::PartialSubtraction: IsTrue,
        {
            C::from_i64(value, modulus)
        }

        #[inline(always)]
        fn from_i128(value: i128, modulus: C::Target) -> C::Target
        where
            C::PartialSubtraction: IsTrue,
        {
            C::from_i128(value, modulus)
        }

        #[inline(always)]
        fn from_isize(value: isize, modulus: C::Target) -> C::Target
        where
            C::PartialSubtraction: IsTrue,
        {
            C::from_isize(value, modulus)
        }

        #[inline(always)]
        fn from_float_prim<F: FloatPrimitive>(value: F, modulus: C::Target) -> C::Target
        where
            C::AssumePrimeModulus: IsTrue,
            C::PartialSubtraction: IsTrue,
            C::PartialMultiplication: IsTrue,
            C::PartialDivision: IsTrue,
        {
            C::from_float_prim(value, modulus)
        }

        #[inline(always)]
        fn from_biguint(value: BigUint, modulus: C::Target) -> C::Target {
            C::from_biguint(value, modulus)
        }

        #[inline(always)]
        fn from_bigint(value: BigInt, modulus: C::Target) -> C::Target
        where
            C::PartialSubtraction: IsTrue,
        {
            C::from_bigint(value, modulus)
        }

        #[inline(always)]
        fn from_biguint_ratio(value: Ratio<BigUint>, modulus: C::Target) -> C::Target
        where
            C::AssumePrimeModulus: IsTrue,
            C::PartialDivision: IsTrue,
        {
            C::from_biguint_ratio(value, modulus)
        }

        #[inline(always)]
        fn from_bigint_ratio(value: Ratio<BigInt>, modulus: C::Target) -> C::Target
        where
            C::AssumePrimeModulus: IsTrue,
            C::PartialSubtraction: IsTrue,
            C::PartialDivision: IsTrue,
        {
            C::from_bigint_ratio(value, modulus)
        }

        #[inline(always)]
        fn eq(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> bool
        where
            C::Equality: IsTrue,
        {
            C::eq(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn cmp(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> cmp::Ordering
        where
            C::Equality: IsTrue,
            C::Order: IsTrue,
        {
            C::cmp(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn fmt_display(
            value: C::Target,
            modulus: C::Target,
            fmt: &mut fmt::Formatter,
        ) -> fmt::Result {
            C::fmt_display(value, modulus, fmt)
        }

        #[inline(always)]
        fn fmt_debug(
            value: C::Target,
            modulus: C::Target,
            ty: &'static str,
            fmt: &mut fmt::Formatter,
        ) -> fmt::Result {
            C::fmt_debug(value, modulus, ty, fmt)
        }

        #[inline(always)]
        fn from_str(str: &str, modulus: C::Target) -> Result<C::Target, ParseIntError> {
            C::from_str(str, modulus)
        }

        #[inline(always)]
        fn neg(value: C::Target, modulus: C::Target) -> C::Target
        where
            C::PartialSubtraction: IsTrue,
        {
            C::neg(value, modulus)
        }

        #[inline(always)]
        fn add(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> C::Target
        where
            C::PartialAddition: IsTrue,
        {
            C::add(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn sub(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> C::Target
        where
            C::PartialSubtraction: IsTrue,
        {
            C::sub(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn mul(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> C::Target
        where
            C::PartialMultiplication: IsTrue,
        {
            C::mul(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn div(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> C::Target
        where
            C::PartialDivision: IsTrue,
        {
            C::div(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn rem(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> C::Target
        where
            C::PartialDivision: IsTrue,
        {
            C::rem(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn inv(value: C::Target, modulus: C::Target) -> C::Target
        where
            C::PartialDivision: IsTrue,
        {
            C::inv(value, modulus)
        }

        #[inline(always)]
        fn from_str_radix(
            str: &str,
            radix: u32,
            modulus: C::Target,
        ) -> Result<C::Target, ParseIntError>
        where
            C::AssumePrimeModulus: IsTrue,
            C::Equality: IsTrue,
            C::Order: IsTrue,
            C::PartialAddition: IsTrue,
            C::PartialSubtraction: IsTrue,
            C::PartialMultiplication: IsTrue,
            C::PartialDivision: IsTrue,
        {
            C::from_str_radix(str, radix, modulus)
        }

        #[inline(always)]
        fn zero(modulus: C::Target) -> C::Target
        where
            C::PartialAddition: IsTrue,
        {
            C::zero(modulus)
        }

        #[inline(always)]
        fn is_zero(value: C::Target, modulus: C::Target) -> bool
        where
            C::PartialAddition: IsTrue,
        {
            C::is_zero(value, modulus)
        }

        #[inline(always)]
        fn one(modulus: C::Target) -> C::Target
        where
            C::PartialMultiplication: IsTrue,
        {
            C::one(modulus)
        }

        #[inline(always)]
        fn is_one(value: C::Target, modulus: C::Target) -> bool
        where
            C::Equality: IsTrue,
            C::PartialMultiplication: IsTrue,
        {
            C::is_one(value, modulus)
        }

        #[inline(always)]
        fn checked_neg(value: C::Target, modulus: C::Target) -> Option<C::Target>
        where
            C::PartialSubtraction: IsTrue,
        {
            C::checked_neg(value, modulus)
        }

        #[inline(always)]
        fn checked_add(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> Option<C::Target>
        where
            C::PartialAddition: IsTrue,
        {
            C::checked_add(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn checked_sub(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> Option<C::Target>
        where
            C::PartialSubtraction: IsTrue,
        {
            C::checked_sub(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn checked_mul(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> Option<C::Target>
        where
            C::PartialMultiplication: IsTrue,
        {
            C::checked_mul(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn checked_div(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> Option<C::Target>
        where
            C::PartialDivision: IsTrue,
        {
            C::checked_div(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn checked_rem(lhs: C::Target, rhs: C::Target, modulus: C::Target) -> Option<C::Target>
        where
            C::PartialDivision: IsTrue,
        {
            C::checked_rem(lhs, rhs, modulus)
        }

        #[inline(always)]
        fn pow_unsigned<E: UnsignedPrimitive>(
            base: C::Target,
            exp: E,
            modulus: C::Target,
        ) -> C::Target
        where
            C::PartialMultiplication: IsTrue,
        {
            C::pow_unsigned(base, exp, modulus)
        }

        #[inline(always)]
        fn pow_signed<E: SignedPrimitive>(base: C::Target, exp: E, modulus: C::Target) -> C::Target
        where
            C::AssumePrimeModulus: IsTrue,
            C::PartialMultiplication: IsTrue,
            C::PartialDivision: IsTrue,
        {
            C::pow_signed(base, exp, modulus)
        }
    }

    /// A [`Cartridge`] which assumes moduluses are primes.
    ///
    /// [`Cartridge`]: ../trait.Cartridge.html
    pub enum Field<T: UnsignedPrimitive> {
        Infallible(Infallible, PhantomData<fn() -> T>),
    }

    impl<T: UnsignedPrimitive> Cartridge for Field<T> {
        type Target = T;
        type AssumePrimeModulus = True;
        type AssumeAlwaysAdjusted = True;
        type Equality = True;
        type Order = True;
        type Deref = True;
        type PartialAddition = True;
        type PartialSubtraction = True;
        type PartialMultiplication = True;
        type PartialDivision = True;
        type FlexibleRhs = False;
    }

    /// A [`Cartridge`] which does not assume moduluses are primes.
    ///
    /// ```
    /// use num::CheckedDiv as _;
    ///
    /// #[modtype::use_modtype]
    /// type Z = modtype::ModType<modtype::cartridges::Multiplicative<u32>, 57u32>;
    ///
    /// assert_eq!(Z(56) * Z(56), Z(1));
    /// assert_eq!(Z(1).checked_div(&Z(13)), Some(Z(22))); // 13・22 ≡ 1 (mod 57)
    /// ```
    ///
    /// [`Cartridge`]: ../trait.Cartridge.html
    pub enum Multiplicative<T: UnsignedPrimitive> {
        Infallible(Infallible, PhantomData<fn() -> T>),
    }

    impl<T: UnsignedPrimitive> Cartridge for Multiplicative<T> {
        type Target = T;
        type AssumePrimeModulus = False;
        type AssumeAlwaysAdjusted = True;
        type Equality = True;
        type Order = True;
        type Deref = True;
        type PartialAddition = True;
        type PartialSubtraction = True;
        type PartialMultiplication = True;
        type PartialDivision = True;
        type FlexibleRhs = False;

        fn sqrt(_: T, _: T) -> Option<T> {
            panic!("`sqrt` for non-prime moduluses is not implemented");
        }

        fn div(_: T, _: T, _: T) -> T {
            panic!(
                "this implementation always panics. use `num::CheckedDiv::checked_div` instead.",
            );
        }
    }

    /// A [`Cartridge`] which does not automatically adjust the inner value until it gets greater than `T::`[`max_value`]` / 2`.
    ///
    /// ```
    /// use num::CheckedAdd as _;
    ///
    /// #[modtype::use_modtype]
    /// type Z = modtype::ModType<modtype::cartridges::Additive<u64>, 1_000_000_007u64>;
    ///
    /// let mut x = Z(1_000_000_006);
    ///
    /// x += Z(1);
    /// assert_eq!(*x.get_mut_unchecked(), 1_000_000_007);
    ///
    /// x += Z(u64::max_value() / 2 - 1_000_000_007);
    /// assert_eq!(*x.get_mut_unchecked(), u64::max_value() / 2);
    ///
    /// x += Z(1);
    /// assert_eq!(*x.get_mut_unchecked(), (u64::max_value() / 2 + 1) % 1_000_000_007);
    /// ```
    ///
    /// [`Cartridge`]: ../trait.Cartridge.html
    /// [`max_value`]: https://docs.rs/num-traits/0.2/num_traits/bounds/trait.Bounded.html#tymethod.max_value
    pub enum Additive<T: UnsignedPrimitive> {
        Infallible(Infallible, PhantomData<fn() -> T>),
    }

    impl<T: UnsignedPrimitive> Cartridge for Additive<T> {
        type Target = T;
        type AssumePrimeModulus = False;
        type AssumeAlwaysAdjusted = False;
        type Equality = False;
        type Order = False;
        type Deref = False;
        type PartialAddition = True;
        type PartialSubtraction = False;
        type PartialMultiplication = False;
        type PartialDivision = False;
        type FlexibleRhs = False;

        #[inline(always)]
        fn should_adjust<S: PrimInt>(value: S, _: S) -> bool {
            value > S::max_value() / (S::one() + S::one())
        }

        #[inline(always)]
        fn fmt_debug(
            value: T,
            modulus: T,
            _ty: &'static str,
            fmt: &mut fmt::Formatter,
        ) -> fmt::Result {
            fmt.debug_tuple("")
                .field(&format_args!(
                    "{} * {} + {} = {}",
                    value / modulus,
                    modulus,
                    value % modulus,
                    value,
                ))
                .finish()
        }

        #[inline(always)]
        fn add(lhs: T, rhs: T, modulus: T) -> T {
            // does not check overflowing
            Self::new(lhs + rhs, modulus)
        }

        #[inline(always)]
        fn checked_add(lhs: T, rhs: T, modulus: T) -> Option<T> {
            lhs.checked_add(&rhs).map(|r| Self::new(r, modulus))
        }
    }

    /// A [`Cartridge`] which does not automatically adjust the inner value.
    ///
    /// ```
    /// use num::CheckedAdd as _;
    ///
    /// #[modtype::use_modtype]
    /// type Z = modtype::ModType<modtype::cartridges::ManuallyAdjust<u64>, 1_000_000_007u64>;
    ///
    /// let mut x = Z(1_000_000_006);
    ///
    /// x += Z(u64::max_value() - 1_000_000_006);
    /// assert_eq!(*x.get_mut_unchecked(), u64::max_value());
    ///
    /// x.adjust();
    /// assert_eq!(*x.get_mut_unchecked(), u64::max_value() % 1_000_000_007);
    /// ```
    ///
    /// [`Cartridge`]: ../trait.Cartridge.html
    pub enum ManuallyAdjust<T: UnsignedPrimitive> {
        Infallible(Infallible, PhantomData<fn() -> T>),
    }

    impl<T: UnsignedPrimitive> Cartridge for ManuallyAdjust<T> {
        type Target = T;
        type AssumePrimeModulus = False;
        type AssumeAlwaysAdjusted = False;
        type Equality = False;
        type Order = False;
        type Deref = False;
        type PartialAddition = True;
        type PartialSubtraction = True;
        type PartialMultiplication = True;
        type PartialDivision = False;
        type FlexibleRhs = False;

        #[inline(always)]
        fn should_adjust<S: PrimInt>(_: S, _: S) -> bool {
            false
        }

        #[inline(always)]
        fn sqrt(_: T, _: T) -> Option<T> {
            panic!("`sqrt` for non-prime moduluses is not implemented");
        }

        #[inline(always)]
        fn fmt_debug(
            value: T,
            modulus: T,
            _ty: &'static str,
            fmt: &mut fmt::Formatter,
        ) -> fmt::Result {
            fmt.debug_tuple("")
                .field(&format_args!(
                    "{} * {} + {} = {}",
                    value / modulus,
                    modulus,
                    value % modulus,
                    value,
                ))
                .finish()
        }

        #[inline(always)]
        fn add(lhs: T, rhs: T, modulus: T) -> T {
            // does not check overflowing
            Self::new(lhs + rhs, modulus)
        }

        #[inline(always)]
        fn sub(lhs: T, rhs: T, modulus: T) -> T {
            Self::add(lhs, Self::neg(rhs, modulus), modulus)
        }

        #[inline(always)]
        fn mul(lhs: T, rhs: T, modulus: T) -> T {
            // does not check overflowing
            Self::new(lhs * rhs, modulus)
        }

        #[inline(always)]
        fn checked_add(lhs: T, rhs: T, modulus: T) -> Option<T> {
            lhs.checked_add(&rhs).map(|r| Self::new(r, modulus))
        }

        #[inline(always)]
        fn checked_sub(lhs: T, rhs: T, modulus: T) -> Option<T> {
            lhs.checked_add(&Self::neg(rhs, modulus))
                .map(|r| Self::new(r, modulus))
        }

        #[inline(always)]
        fn checked_mul(lhs: T, rhs: T, modulus: T) -> Option<T> {
            lhs.checked_mul(&rhs).map(|r| Self::new(r, modulus))
        }
    }
}

/// A modular arithmetic integer type which modulus is **a `struct` field**.
pub mod non_static {
    use crate::{cartridges, Cartridge, False, True, UnsignedPrimitive};

    /// A type alias which [`Cartridge`] is [`modtype::cartridges::Field`]`<T>`.
    ///
    /// [`Cartridge`]: ../trait.Cartridge.html
    /// [`modtype::cartridges::Field`]: ../cartridges/type.Field.html
    pub type F<T> = ModType<cartridges::Field<T>>;

    /// A modular arithmetic integer type which modulus is **a `struct` field**.
    ///
    /// # Example
    ///
    /// ```
    /// #[allow(non_snake_case)]
    /// let F = modtype::non_static::F::factory(1_000_000_007u64);
    ///
    /// assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
    /// ```
    #[derive(crate::ModType)]
    #[modtype(
        modulus = "self.modulus",
        cartridge = "C",
        modtype = "crate",
        non_static_modulus
    )]
    pub struct ModType<C: Cartridge> {
        #[modtype(value)]
        value: C::Target,
        modulus: C::Target,
    }

    impl<T: UnsignedPrimitive, C: Cartridge<Target = T>> ModType<C> {
        /// Constructs a new `ModType`.
        #[inline]
        pub fn new(value: T, modulus: T) -> Self {
            Self {
                value: C::new(value, modulus),
                modulus,
            }
        }

        /// Constructs a new `ModType` without checking the value.
        #[inline]
        pub fn new_unchecked(value: T, modulus: T) -> Self {
            Self { value, modulus }
        }

        /// Same as `move |n| Self::`[`new`]`(n, modulus)`.
        ///
        /// [`new`]: ./struct.Z.html#method.new
        #[inline]
        pub fn factory(modulus: T) -> impl Fn(T) -> Self {
            move |n| Self::new(n, modulus)
        }

        /// Returns a mutable reference to the inner value.
        #[inline]
        pub fn get_mut_unchecked(&mut self) -> &mut T {
            &mut self.value
        }

        #[inline]
        pub fn adjust(&mut self)
        where
            C: Cartridge<AssumeAlwaysAdjusted = False>,
        {
            C::adjust(&mut self.value, self.modulus)
        }

        #[inline]
        pub fn adjusted(self) -> Self
        where
            C: Cartridge<AssumeAlwaysAdjusted = False>,
        {
            Self {
                value: C::adjusted(self.value, self.modulus),
                modulus: self.modulus,
            }
        }

        /// Gets the modulus.
        #[inline]
        pub fn modulus(self) -> T {
            self.modulus
        }

        /// Returns `r` such that `r * r == self` if it exists.
        #[inline]
        pub fn sqrt(self) -> Option<Self>
        where
            C: Cartridge<PartialMultiplication = True>,
        {
            C::sqrt(self.value, self.modulus).map(|v| Self::new_unchecked(v, self.modulus))
        }
    }
}

/// A modular arithmetic integer type which modulus is **`thread_local`**.
pub mod thread_local {
    use crate::{cartridges, Cartridge, False, True, UnsignedPrimitive as _};

    use num::Zero as _;

    /// A type alias which [`Cartridge`] is [`modtype::cartridges::Field`]`<T>`.
    ///
    /// [`Cartridge`]: ../trait.Cartridge.html
    /// [`modtype::cartridges::Field`]: ../cartridges/type.Field.html
    pub type F<T> = ModType<cartridges::Field<T>>;

    /// A modular arithmetic integer type which modulus is **`thread_local`**.
    ///
    /// # Example
    ///
    /// ```
    /// #[allow(non_snake_case)]
    /// modtype::thread_local::F::with(1_000_000_007u64, |F| {
    ///     assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
    /// });
    /// ```
    #[derive(crate::ModType)]
    #[modtype(
        modulus = "unsafe { C::Target::thread_local_modulus() }",
        cartridge = "C",
        modtype = "crate"
    )]
    pub struct ModType<C: Cartridge> {
        #[modtype(value)]
        value: C::Target,
    }

    impl<C: Cartridge> ModType<C> {
        /// Sets `modulus` and run `f`.
        ///
        /// The modulus is set to `0` when `f` finished.
        pub fn with<O, F: FnOnce(fn(C::Target) -> Self) -> O>(modulus: C::Target, f: F) -> O {
            unsafe { C::Target::set_thread_local_modulus(modulus) };
            let ret = f(Self::new);
            unsafe { C::Target::set_thread_local_modulus(C::Target::zero()) };
            ret
        }

        /// Gets the modulus.
        #[inline]
        pub fn modulus() -> C::Target {
            unsafe { C::Target::thread_local_modulus() }
        }

        /// Creates a new `ModType`.
        #[inline]
        pub fn new(value: C::Target) -> Self {
            Self {
                value: C::new(value, Self::modulus()),
            }
        }

        /// Creates a new `ModType` without checking `value`.
        #[inline]
        pub fn new_unchecked(value: C::Target) -> Self {
            Self { value }
        }

        /// Returns a mutable reference to the inner value.
        #[inline]
        pub fn get_mut_unchecked(&mut self) -> &mut C::Target {
            &mut self.value
        }

        #[inline]
        pub fn adjust(&mut self)
        where
            C: Cartridge<AssumeAlwaysAdjusted = False>,
        {
            C::adjust(&mut self.value, unsafe {
                C::Target::thread_local_modulus()
            })
        }

        #[inline]
        pub fn adjusted(self) -> Self
        where
            C: Cartridge<AssumeAlwaysAdjusted = False>,
        {
            Self {
                value: C::adjusted(self.value, unsafe { C::Target::thread_local_modulus() }),
            }
        }

        /// Returns `r` such that `r * r == self` if it exists.
        #[inline]
        pub fn sqrt(self) -> Option<Self>
        where
            C: Cartridge<PartialMultiplication = True>,
        {
            C::sqrt(self.value, unsafe { C::Target::thread_local_modulus() })
                .map(|value| Self { value })
        }
    }
}

mod sealed {
    use crate::{False, True};

    pub trait Sealed {}

    impl Sealed for False {}
    impl Sealed for True {}
    impl Sealed for u8 {}
    impl Sealed for u16 {}
    impl Sealed for u32 {}
    impl Sealed for u64 {}
    impl Sealed for u128 {}
    impl Sealed for usize {}
    impl Sealed for i8 {}
    impl Sealed for i16 {}
    impl Sealed for i32 {}
    impl Sealed for i64 {}
    impl Sealed for i128 {}
    impl Sealed for isize {}
    impl Sealed for f32 {}
    impl Sealed for f64 {}
}
