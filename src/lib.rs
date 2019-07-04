//! This crate provides modular arithmetic integer types.
//!
//! # Usage
//!
//! ## [`modtype::ModType`]
//!
//! ```
//! #[modtype::use_modtype]
//! type F = modtype::DefaultModType<1_000_000_007u64>;
//!
//! assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
//! ```
//!
//! ## [`modtype::thread_local::ModType`]
//!
//! ```
//! #[allow(non_snake_case)]
//! modtype::thread_local::DefaultModType::with(57u32, |Z| {
//!     assert_eq!(Z(42) + Z(15), Z(0));
//! });
//! ```
//!
//! ## [`modtype::field_param::ModType`]
//!
//! ```
//! use num::CheckedDiv as _;
//!
//! #[allow(non_snake_case)]
//! let Z = modtype::field_param::DefaultModType::factory(1000u32);
//!
//! assert_eq!(Z(1).checked_div(&Z(777)), Some(Z(713))); // 777 × 713 ≡ 1 (mod 1000)
//! ```
//!
//! # Customization
//!
//! `ModType`s can be customized via [`modtype::Cartridge`].
//!
//! ```
//! #[modtype::use_modtype]
//! type F = modtype::ModType<u64, Cartridge, 1_000_000_007u64>;
//!
//! enum Cartridge {}
//!
//! impl modtype::Cartridge for Cartridge {
//!     type Target = u64;
//!     type Features = modtype::DefaultFeatures;
//!
//!     // your implementation here
//! }
//! ```
//!
//! [`modtype::ModType`]: ./struct.ModType.html
//! [`modtype::thread_local::ModType`]: ./thread_local/struct.ModType.html
//! [`modtype::field_param::ModType`]: ./field_param/struct.ModType.html
//! [`modtype::Cartridge`]: ./trait.Cartridge.html

macro_rules! expect_feature {
    ($feature:ident $(, $extra:literal)? $(,)?) => {
        <Self::Features as Features>::$feature::expect(concat!(
            "this implementation always panics since `Self::Features::",
            stringify!($feature),
            " = False`.",
            $(" ", $extra,)*
        ))
    };
}

pub use modtype_derive::{use_modtype, ConstValue, ModType};

use crate::util::UnsignedPrimitiveUtil as _;

use num::{
    integer, BigInt, BigUint, CheckedAdd as _, CheckedMul as _, CheckedSub as _, Float,
    FromPrimitive, Integer, Num, One as _, PrimInt, Signed, ToPrimitive as _, Unsigned, Zero as _,
};

use std::convert::Infallible;
use std::fmt;
use std::iter::{Product, Sum};
use std::marker::PhantomData;
use std::num::ParseIntError;
use std::ops::{
    AddAssign, BitAndAssign, BitOrAssign, BitXorAssign, DivAssign, MulAssign, RemAssign, SubAssign,
};
use std::str::FromStr;

/// A trait for `u8`, `u16`, `u32`, `u64`, `u128`, and `usize`.
pub trait UnsignedPrimitive:
    hidden::Sealed
    + Unsigned
    + PrimInt
    + Integer
    + Num<FromStrRadixErr = ParseIntError>
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
    + util::UnsignedPrimitiveUtil
    + 'static
{
}

impl UnsignedPrimitive for u8 {}
impl UnsignedPrimitive for u16 {}
impl UnsignedPrimitive for u32 {}
impl UnsignedPrimitive for u64 {}
impl UnsignedPrimitive for u128 {}
impl UnsignedPrimitive for usize {}

/// A trait for `i8`, `i16`, `i32`, `i64`, `i128`, and `isize`.
pub trait SignedPrimitive:
    hidden::Sealed
    + Signed
    + PrimInt
    + Integer
    + Num<FromStrRadixErr = ParseIntError>
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
    hidden::Sealed
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
/// [`use_modtype`]: https://docs.rs/modtype_derive/0.6/modtype_derive/attr.use_modtype.html
/// [the derive macro]: https://docs.rs/modtype_derive/0.6/modtype_derive/derive.ConstValue.html
pub trait ConstValue {
    type Value: Copy;
    const VALUE: Self::Value;
}

/// Actual implementation.
///
/// Note that in the default implementation:
/// - It is assumed that given/return values are always smaller than the modulus.
/// - It is assumed that the modulus is larger than `1`.
/// - It is assumed that `modulus + modulus` does not overflow.
/// - It is assumed that `modulus * modulus` does not overflow.
/// - The following methods always panic if `Self::Features::`[`AssumePrimeModulus`]` = `[`False`].
///     - `{..}::ModType::sqrt`
///     - [`Div`]`::div` (`/` operator. not [`CheckedDiv`]`::checked_div`)
///     - [`DivAssign`]`::div_assign` (`/=` operator)
///     - [`Rem`]`::rem` (`%` operator. not [`CheckedRem`]`::checked_rem`)
///     - [`RemAssign`]`::rem_assign` (`%=` operator)
///     - [`Inv`]`::inv`
///     - [`FromPrimitive`]`::{from_f32, from_f64}`
///
/// [`AssumePrimeModulus`]: ./trait.Features.html#associatedtype.AssumePrimeModulus
/// [`False`]: ./enum.False.html
/// [`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
/// [`CheckedDiv`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedDiv.html
/// [`DivAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.DivAssign.html
/// [`Rem`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Rem.html
/// [`CheckedRem`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedRem.html
/// [`RemAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.RemAssign.html
/// [`Inv`]: https://docs.rs/num-traits/0.2/num_traits/ops/inv/trait.Inv.html
/// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
pub trait Cartridge {
    type Target: UnsignedPrimitive;
    type Features: Features;

    /// Implementation for [`From`]`<Self::Target>` and `modtype{, ::thread_local}::ModType::new`.
    ///
    /// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
    #[inline(always)]
    fn new(value: Self::Target, modulus: Self::Target) -> Self::Target {
        if value >= modulus {
            value % modulus
        } else {
            value
        }
    }

    /// Implementation for `modtype{, ::thread_local, ::field_param}::ModType::get`.
    #[inline(always)]
    fn get(value: Self::Target, _modulus: Self::Target) -> Self::Target {
        value
    }

    /// Implementation for `modtype{, ::thread_local, ::field_param}::ModType::sqrt`.
    ///
    /// The default implementation uses [Tonelli–Shanks algorithm].
    ///
    /// # Panics
    ///
    /// The default implementation always panics if `Self::Features::`[`AssumePrimeModulus`] is [`False`].
    ///
    /// [Tonelli–Shanks algorithm]: https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm
    /// [`AssumePrimeModulus`]: ./trait.Features.html#associatedtype.AssumePrimeModulus
    /// [`False`]: ./enum.False.html
    #[inline(always)]
    fn sqrt(value: Self::Target, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<PartialMultiplication = True>,
    {
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

        expect_feature!(AssumePrimeModulus);

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
                if DefaultCartridge::pow_unsigned(z, (p - id!(1)) / id!(2), p) == p - id!(1) {
                    break z;
                }
            }
        };

        let mut m = s;
        let mut c = DefaultCartridge::pow_unsigned(z, q, p);
        let mut t = DefaultCartridge::pow_unsigned(n, q, p);
        let mut r = DefaultCartridge::pow_unsigned(n, (q + id!(1)) / id!(2), p);

        Some(loop {
            if t == id!(0) {
                break id!(0);
            }
            if t == id!(1) {
                break r;
            }

            let i = {
                let (mut acc, mut i) = (DefaultCartridge::mul(t, t, p), id!(1));
                loop {
                    if i == m {
                        return None;
                    }
                    if acc == id!(1) {
                        break i;
                    }
                    acc = DefaultCartridge::mul(acc, acc, p);
                    i += id!(1);
                }
            };

            let b = {
                let mut b = c;
                for _ in util::range(id!(0), m - i - id!(1)) {
                    b = DefaultCartridge::mul(b, b, p);
                }
                b
            };

            m = i;
            c = DefaultCartridge::mul(b, b, p);
            t = DefaultCartridge::mul(t, DefaultCartridge::mul(b, b, p), p);
            r = DefaultCartridge::mul(r, b, p);
        })
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
    fn from_bigint(mut value: BigInt, modulus: Self::Target) -> Self::Target {
        let is_neg = value.is_negative();
        if is_neg {
            value = -value;
        }
        let acc = Self::Target::try_from_bigint(modulus.rem_bigint(value)).unwrap();
        if is_neg {
            modulus - acc
        } else {
            acc
        }
    }

    /// Implementation for [`Display`].
    ///
    /// [`Display`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html
    #[inline(always)]
    fn fmt_display(
        value: Self::Target,
        _modulus: Self::Target,
        fmt: &mut fmt::Formatter,
    ) -> fmt::Result {
        <Self::Target as fmt::Display>::fmt(&value, fmt)
    }

    /// Implementation for [`Debug`].
    ///
    /// [`Debug`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html
    #[inline(always)]
    fn fmt_debug(
        value: Self::Target,
        _modulus: Self::Target,
        _ty: &'static str,
        fmt: &mut fmt::Formatter,
    ) -> fmt::Result {
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
        Self::Features: Features<PartialSubtraction = True>,
    {
        modulus - value
    }

    /// Implementation for [`Add`].
    ///
    /// [`Add`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Add.html
    #[inline(always)]
    fn add(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<PartialAddition = True>,
    {
        Self::new(lhs + rhs, modulus)
    }

    /// Implementation for [`Sub`].
    ///
    /// [`Sub`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Sub.html
    #[inline(always)]
    fn sub(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<PartialSubtraction = True>,
    {
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
        Self::Features: Features<PartialMultiplication = True>,
    {
        Self::new(lhs * rhs, modulus)
    }

    /// Implementation for [`Div`].
    ///
    /// [`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
    #[inline(always)]
    fn div(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<PartialDivision = True>,
    {
        expect_feature!(
            AssumePrimeModulus,
            "use `num::CheckedDiv::checked_div` instead",
        );

        if rhs == Self::Target::zero() {
            panic!("attempt to divide by zero");
        }
        Self::checked_div(lhs, rhs, modulus)
            .expect("could not divide. if the modulus is a prime, THIS IS A BUG.")
    }

    /// Implementation for [`Rem`].
    ///
    /// [`Rem`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Rem.html
    #[inline(always)]
    fn rem(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<PartialDivision = True>,
    {
        expect_feature!(
            AssumePrimeModulus,
            "use `num::traits::CheckedRem::checked_rem` instead",
        );

        if rhs == Self::Target::zero() {
            panic!("attempt to calculate the remainder with a divisor of zero");
        }
        if integer::gcd(rhs, modulus) != Self::Target::one() {
            panic!("{}/{} (mod {}) does not exist", lhs, rhs, modulus);
        }
        Self::Target::zero()
    }

    /// Implementation for [`Inv`].
    ///
    /// [`Inv`]: https://docs.rs/num-traits/0.2/num_traits/ops/inv/trait.Inv.html
    #[inline(always)]
    fn inv(value: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<PartialDivision = True>,
    {
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
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialAddition = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::Target::from_str_radix(str, radix).map(|v| Self::new(v, modulus))
    }

    /// Implementation for [`Bounded`]`::`[`min_value`].
    ///
    /// [`Bounded`]: https://docs.rs/num-traits/0.2/num_traits/bounds/trait.Bounded.html
    /// [`min_value`]: https://docs.rs/num-traits/0.2/num_traits/bounds/trait.Bounded.html#method.min_value
    #[inline(always)]
    fn min_value(_modulus: Self::Target) -> Self::Target {
        Self::Target::zero()
    }

    /// Implementation for [`Bounded`]`::`[`max_value`].
    ///
    /// [`Bounded`]: https://docs.rs/num-traits/0.2/num_traits/bounds/trait.Bounded.html
    /// [`max_value`]: https://docs.rs/num-traits/0.2/num_traits/bounds/trait.Bounded.html#method.max_value
    #[inline(always)]
    fn max_value(modulus: Self::Target) -> Self::Target {
        modulus - Self::Target::one()
    }

    /// Implementation for [`Zero`]`::`[`zero`].
    ///
    /// [`Zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html
    /// [`zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html#tymethod.zero
    #[inline(always)]
    fn zero(_modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<PartialAddition = True>,
    {
        Self::Target::zero()
    }

    /// Implementation for [`Zero`]`::`[`is_zero`].
    ///
    /// [`Zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html
    /// [`is_zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html#tymethod.is_zero
    #[inline(always)]
    fn is_zero(value: Self::Target, _modulus: Self::Target) -> bool
    where
        Self::Features: Features<PartialAddition = True>,
    {
        value == Self::Target::zero()
    }

    /// Implementation for [`One`]`::`[`one`].
    ///
    /// [`One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
    /// [`one`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html#tymethod.one
    #[inline(always)]
    fn one(_modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<PartialMultiplication = True>,
    {
        Self::Target::one()
    }

    /// Implementation for [`One`]`::`[`is_one`].
    ///
    /// [`One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
    /// [`is_one`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html#tymethod.is_one
    #[inline(always)]
    fn is_one(value: Self::Target, _modulus: Self::Target) -> bool
    where
        Self::Features: Features<PartialMultiplication = True>,
    {
        value == Self::Target::one()
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_i64`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_i64`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#tymethod.from_i64
    #[inline(always)]
    fn from_i64(value: i64, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::from_i128(value.to_i128()?, modulus)
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_u64`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_u64`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#tymethod.from_u64
    #[inline(always)]
    fn from_u64(value: u64, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::from_u128(value.to_u128()?, modulus)
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_isize`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_isize`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#tymethod.from_isize
    #[inline(always)]
    fn from_isize(value: isize, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::from_i128(value.to_i128()?, modulus)
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_isize`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_isize`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_isize
    #[inline(always)]
    fn from_i8(value: i8, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::from_i128(value.to_i128()?, modulus)
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_i16`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_i16`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_i16
    #[inline(always)]
    fn from_i16(value: i16, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::from_i128(value.to_i128()?, modulus)
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_i32`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_i32`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_i32
    #[inline(always)]
    fn from_i32(value: i32, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::from_i128(value.to_i128()?, modulus)
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_i128`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_i128`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_i128
    #[inline(always)]
    fn from_i128(value: i128, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        if value < 0 {
            Self::from_u128((-value).to_u128()?, modulus).map(|v| Self::neg(v, modulus))
        } else {
            Self::from_u128(value.to_u128()?, modulus)
        }
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_usize`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_usize`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_usize
    #[inline(always)]
    fn from_usize(value: usize, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::from_u128(value.to_u128()?, modulus)
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_u8`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_u8`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_u8
    #[inline(always)]
    fn from_u8(value: u8, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::from_u128(value.to_u128()?, modulus)
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_u16`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_u16`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_u16
    #[inline(always)]
    fn from_u16(value: u16, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::from_u128(value.to_u128()?, modulus)
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_u32`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_u32`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_u32
    #[inline(always)]
    fn from_u32(value: u32, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        Self::from_u128(value.to_u128()?, modulus)
    }

    /// Implementation for [`FromPrimitive`]`::`[`from_u128`].
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_u128`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_u128
    #[inline(always)]
    fn from_u128(mut value: u128, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        let modulus = modulus.to_u128()?;
        if value >= modulus {
            value %= modulus;
        }
        Self::Target::from_u128(value)
    }

    /// Implementation for [`FromPrimitive`]`::{`[`from_f32`]`, `[`from_f64`]`}`.
    ///
    /// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
    /// [`from_f32`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_f32
    /// [`from_f64`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html#method.from_f64
    #[inline(always)]
    fn from_float_prim<F: FloatPrimitive>(value: F, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialSubtraction = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
        macro_rules! id {
            (2) => {
                Self::Target::one() + Self::Target::one()
            };
        }

        let (man, exp, sign) = value.integer_decode();
        let acc = Self::mul(
            Self::from_u64(man, modulus)?,
            Self::pow_signed(id!(2), exp, modulus),
            modulus,
        );
        Some(match sign {
            -1 => Self::neg(acc, modulus),
            _ => acc,
        })
    }

    /// Implementation for [`CheckedNeg`].
    ///
    /// [`CheckedNeg`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedNeg.html
    #[inline(always)]
    fn checked_neg(value: Self::Target, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<PartialSubtraction = True>,
    {
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
        Self::Features: Features<PartialAddition = True>,
    {
        lhs.checked_add(&rhs).map(|v| Self::new(v, modulus))
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
        Self::Features: Features<PartialSubtraction = True>,
    {
        (lhs + modulus)
            .checked_sub(&rhs)
            .map(|v| Self::new(v, modulus))
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
        Self::Features: Features<PartialMultiplication = True>,
    {
        lhs.checked_mul(&rhs).map(|v| Self::new(v, modulus))
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
        Self::Features: Features<PartialDivision = True>,
    {
        #[allow(clippy::many_single_char_names)]
        fn egcd(a: i128, b: i128) -> (i128, i128, i128) {
            if a == 0 {
                (b, 0, 1)
            } else {
                let (d, u, v) = egcd(b % a, a);
                (d, v - (b / a) * u, u)
            }
        }

        let lhs = lhs.to_i128()?;
        let rhs = rhs.to_i128()?;
        let modulus = modulus.to_i128()?;

        if rhs == 0 {
            return None;
        }

        let (d, u, _) = egcd(rhs, modulus);

        if rhs % d != 0 {
            return None;
        }

        let mut acc = (lhs * u) % modulus;
        if acc < 0 {
            acc += modulus;
        }
        Self::Target::from_i128(acc)
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
        Self::Features: Features<PartialDivision = True>,
    {
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
        Self::Features: Features<PartialMultiplication = True>,
    {
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
        Self::Features: Features<
            AssumePrimeModulus = True,
            PartialMultiplication = True,
            PartialDivision = True,
        >,
    {
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

/// The default implementation.
pub enum DefaultCartridge<T: UnsignedPrimitive> {
    Infallible(Infallible, PhantomData<fn() -> T>),
}

impl<T: UnsignedPrimitive> Cartridge for DefaultCartridge<T> {
    type Target = T;
    type Features = DefaultFeatures;
}

/// The implementation for non prime moduluses.
pub enum NonPrime<T: UnsignedPrimitive> {
    Infallible(Infallible, PhantomData<fn() -> T>),
}

impl<T: UnsignedPrimitive> Cartridge for NonPrime<T> {
    type Target = T;
    type Features = DefaultFeatures;
}

/// Features.
pub trait Features {
    type AssumePrimeModulus: TypedBool;
    type Deref: TypedBool;
    type PartialAddition: TypedBool;
    type PartialSubtraction: TypedBool;
    type PartialMultiplication: TypedBool;
    type PartialDivision: TypedBool;
}

/// The default features.
pub enum DefaultFeatures {}

impl Features for DefaultFeatures {
    type AssumePrimeModulus = True;
    type Deref = True;
    type PartialAddition = True;
    type PartialSubtraction = True;
    type PartialMultiplication = True;
    type PartialDivision = True;
}

/// Type level boolean.
pub trait TypedBool: hidden::Sealed {
    /// `panic!(msg)` if `Self` is [`False`].
    ///
    /// [`False`]: ./enum.False.html
    fn expect(msg: &'static str);
}

/// A [`TypedBool`] which represents "false".
///
/// [`TypedBool`]: ./trait.TypedBool.html
pub enum False {}

impl TypedBool for False {
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
    #[inline(always)]
    fn expect(_: &'static str) {}
}

/// A type alias which [`Cartridge`] is [`DefaultCartridge`]`<M::Value>`.
///
/// [`Cartridge`]: ./trait.Cartridge.html
/// [`DefaultCartridge`]: ./enum.DefaultCartridge.html
pub type DefaultModType<M> =
    ModType<<M as ConstValue>::Value, DefaultCartridge<<M as ConstValue>::Value>, M>;

/// A modular arithmetic integer type which modulus is **a constant**.
///
/// # Examples
///
/// ```
/// use modtype::{use_modtype, DefaultModType};
/// use num::bigint::{Sign, ToBigInt as _, ToBigUint as _};
/// use num::pow::Pow as _;
/// use num::traits::{CheckedNeg as _, CheckedRem as _, Inv as _};
/// use num::{
///     BigInt, BigUint, Bounded as _, CheckedAdd as _, CheckedDiv as _, CheckedMul as _,
///     CheckedSub as _, FromPrimitive as _, Num as _, One as _, ToPrimitive as _, Unsigned,
///     Zero as _,
/// };
///
/// #[use_modtype]
/// type F = DefaultModType<7u32>;
///
/// fn static_assert_unsigned<T: Unsigned>() {}
///
/// // Constructor, `new`, `new_unchecked`, `get`, `sqrt`
/// assert_eq!(F::new(8), F(1));
/// assert_ne!(F::new_unchecked(8), F(1));
/// assert_eq!(F(3).get(), 3u32);
/// assert_eq!(F(2).sqrt(), Some(F(4)));
///
/// // `From<{T, BigUint, BigInt}>`
/// assert_eq!(F::from(3), F(3));
/// assert_eq!(F::from(BigUint::new(vec![3])), F(3));
/// assert_eq!(F::from(BigInt::new(Sign::Minus, vec![4])), F(3));
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
/// // `Unsigned`
/// static_assert_unsigned::<F>();
///
/// // `Bounded`
/// assert_eq!((F::min_value(), F::max_value()), (F(0), F(6)));
///
/// // `Zero`, `One`
/// assert_eq!(F::zero(), F(0));
/// assert_eq!(F::one(), F(1));
///
/// // `FromPrimitive`
/// assert_eq!(F::from_i128(-1), Some(-F(1)));
/// assert_eq!(F::from_f64(0.5), Some(F(1) / F(2)));
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
pub struct ModType<T: UnsignedPrimitive, C: Cartridge<Target = T>, M: ConstValue<Value = T>> {
    #[modtype(value)]
    value: T,
    phantom: PhantomData<fn() -> (C, M)>,
}

impl<T: UnsignedPrimitive, C: Cartridge<Target = T>, M: ConstValue<Value = T>> ModType<T, C, M> {
    /// Gets the modulus.
    #[inline]
    pub fn modulus() -> T {
        <M as ConstValue>::VALUE
    }

    /// Creates a new `ModType`.
    #[inline]
    pub fn new(value: T) -> Self {
        Self {
            value: C::new(value, Self::modulus()),
            phantom: PhantomData,
        }
    }

    /// Creates a new `ModType` without checking `value`.
    #[inline]
    pub fn new_unchecked(value: T) -> Self {
        Self {
            value,
            phantom: PhantomData,
        }
    }

    /// Gets the inner value.
    #[inline]
    pub fn get(self) -> T {
        self.value
    }

    /// Returns a mutable reference to the inner value.
    #[inline]
    pub fn get_mut_unchecked(&mut self) -> &mut T {
        &mut self.value
    }

    /// Returns `r` such that `r * r == self` if it exists.
    #[inline]
    pub fn sqrt(self) -> Option<Self>
    where
        C::Features: Features<PartialMultiplication = True>,
    {
        C::sqrt(self.value, M::VALUE).map(Self::new_unchecked)
    }
}

/// A modular arithmetic integer type which modulus is **a `struct` field**.
pub mod field_param {
    use crate::{Cartridge, DefaultCartridge, Features, True, UnsignedPrimitive};

    use std::marker::PhantomData;

    /// A type alias which [`Cartridge`] is [`DefaultCartridge`]`<T>`.
    ///
    /// [`Cartridge`]: ../trait.Cartridge.html
    /// [`DefaultCartridge`]: ../enum.DefaultCartridge.html
    pub type DefaultModType<T> = ModType<T, DefaultCartridge<T>>;

    /// A modular arithmetic integer type which modulus is **a `struct` field**.
    ///
    /// # Example
    ///
    /// ```
    /// use num::CheckedDiv as _;
    ///
    /// #[allow(non_snake_case)]
    /// let Z = modtype::field_param::DefaultModType::factory(1000u32);
    ///
    /// assert_eq!(Z(1).checked_div(&Z(777)), Some(Z(713))); // 777 × 713 ≡ 1 (mod 1000)
    /// ```
    #[derive(crate::ModType)]
    #[modtype(
        modulus = "self.modulus",
        cartridge = "C",
        modtype = "crate",
        non_static_modulus
    )]
    pub struct ModType<T: UnsignedPrimitive, C: Cartridge<Target = T>> {
        #[modtype(value)]
        value: T,
        modulus: T,
        phantom: PhantomData<fn() -> C>,
    }

    impl<T: UnsignedPrimitive, C: Cartridge<Target = T>> ModType<T, C> {
        /// Constructs a new `ModType`.
        #[inline]
        pub fn new(value: T, modulus: T) -> Self {
            Self {
                value: C::new(value, modulus),
                modulus,
                phantom: PhantomData,
            }
        }

        /// Constructs a new `ModType` without checking the value.
        #[inline]
        pub fn new_unchecked(value: T, modulus: T) -> Self {
            Self {
                value,
                modulus,
                phantom: PhantomData,
            }
        }

        /// Same as `move |n| Self::`[`new`]`(n, modulus)`.
        ///
        /// [`new`]: ./struct.Z.html#method.new
        #[inline]
        pub fn factory(modulus: T) -> impl Fn(T) -> Self {
            move |n| Self::new(n, modulus)
        }

        /// Gets the inner value.
        #[inline]
        pub fn get(self) -> T {
            self.value
        }

        /// Returns a mutable reference to the inner value.
        #[inline]
        pub fn get_mut_unchecked(&mut self) -> &mut T {
            &mut self.value
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
            C::Features: Features<PartialMultiplication = True>,
        {
            C::sqrt(self.value, self.modulus).map(|v| Self::new_unchecked(v, self.modulus))
        }
    }
}

/// A modular arithmetic integer type which modulus is **`thread_local`**.
pub mod thread_local {
    use crate::{Cartridge, DefaultCartridge, Features, True, UnsignedPrimitive};

    use std::cell::UnsafeCell;
    use std::marker::PhantomData;
    use std::thread::LocalKey;

    /// A type alias which [`Cartridge`] is [`DefaultCartridge`]`<T>`.
    ///
    /// [`Cartridge`]: ../trait.Cartridge.html
    /// [`DefaultCartridge`]: ../enum.DefaultCartridge.html
    pub type DefaultModType<T> = ModType<T, DefaultCartridge<T>>;

    /// A modular arithmetic integer type which modulus is **`thread_local`**.
    ///
    /// # Example
    ///
    /// ```
    /// #[allow(non_snake_case)]
    /// modtype::thread_local::DefaultModType::with(57u32, |Z| {
    ///     assert_eq!(Z(42) + Z(15), Z(0));
    /// });
    /// ```
    #[derive(crate::ModType)]
    #[modtype(
        modulus = "unsafe { T::modulus() }",
        cartridge = "C",
        modtype = "crate"
    )]
    pub struct ModType<T: HasThreadLocalModulus, C: Cartridge<Target = T>> {
        #[modtype(value)]
        value: T,
        phantom: PhantomData<fn() -> C>,
    }

    impl<T: HasThreadLocalModulus, C: Cartridge<Target = T>> ModType<T, C> {
        /// Sets `modulus` and run `f`.
        ///
        /// The modulus is set to `0` when `f` finished.
        pub fn with<O, F: FnOnce(fn(T) -> Self) -> O>(modulus: T, f: F) -> O {
            unsafe { T::set_modulus(modulus) };
            let ret = f(Self::new);
            unsafe { T::set_modulus(T::zero()) };
            ret
        }

        /// Gets the modulus.
        #[inline]
        pub fn modulus() -> T {
            unsafe { T::modulus() }
        }

        /// Creates a new `ModType`.
        #[inline]
        pub fn new(value: T) -> Self {
            Self {
                value: C::new(value, Self::modulus()),
                phantom: PhantomData,
            }
        }

        /// Creates a new `ModType` without checking `value`.
        #[inline]
        pub fn new_unchecked(value: T) -> Self {
            Self {
                value,
                phantom: PhantomData,
            }
        }

        /// Gets the inner value.
        #[inline]
        pub fn get(self) -> T {
            self.value
        }

        /// Returns a mutable reference to the inner value.
        #[inline]
        pub fn get_mut_unchecked(&mut self) -> &mut T {
            &mut self.value
        }

        /// Returns `r` such that `r * r == self` if it exists.
        #[inline]
        pub fn sqrt(self) -> Option<Self>
        where
            C::Features: Features<PartialMultiplication = True>,
        {
            C::sqrt(self.value, unsafe { T::modulus() }).map(Self::new_unchecked)
        }
    }

    /// A trait that represents an associated `LocalKey<UnsafeCell<Self>>`.
    pub trait HasThreadLocalModulus: UnsignedPrimitive {
        /// The `LocalKey<UnsafeCell<Self>>`.
        fn local_key() -> &'static LocalKey<UnsafeCell<Self>>;

        /// Gets the value of the `LocalKey<UnsafeCell<Self>>`.
        ///
        /// # Safety
        ///
        /// This function is safe as long as `Self::local_key().with` does not leak the raw pointer.
        unsafe fn modulus() -> Self {
            Self::local_key().with(|m| *m.get())
        }

        /// Sets `modulus`.
        ///
        /// # Safety
        ///
        /// This function is safe as long as `Self::local_key().with` does not leak the raw pointer.
        unsafe fn set_modulus(modulus: Self) {
            Self::local_key().with(|m| *m.get() = modulus)
        }
    }

    impl HasThreadLocalModulus for u8 {
        fn local_key() -> &'static LocalKey<UnsafeCell<Self>> {
            &MODULUS_U8
        }
    }

    impl HasThreadLocalModulus for u16 {
        fn local_key() -> &'static LocalKey<UnsafeCell<Self>> {
            &MODULUS_U16
        }
    }

    impl HasThreadLocalModulus for u32 {
        fn local_key() -> &'static LocalKey<UnsafeCell<Self>> {
            &MODULUS_U32
        }
    }

    impl HasThreadLocalModulus for u64 {
        fn local_key() -> &'static LocalKey<UnsafeCell<Self>> {
            &MODULUS_U64
        }
    }

    impl HasThreadLocalModulus for u128 {
        fn local_key() -> &'static LocalKey<UnsafeCell<Self>> {
            &MODULUS_U128
        }
    }

    impl HasThreadLocalModulus for usize {
        fn local_key() -> &'static LocalKey<UnsafeCell<Self>> {
            &MODULUS_USIZE
        }
    }

    thread_local! {
        static MODULUS_U8: UnsafeCell<u8> = UnsafeCell::new(0);
        static MODULUS_U16: UnsafeCell<u16> = UnsafeCell::new(0);
        static MODULUS_U32: UnsafeCell<u32> = UnsafeCell::new(0);
        static MODULUS_U64: UnsafeCell<u64> = UnsafeCell::new(0);
        static MODULUS_U128: UnsafeCell<u128> = UnsafeCell::new(0);
        static MODULUS_USIZE: UnsafeCell<usize> = UnsafeCell::new(0);
    }
}

pub mod util {
    use num::{BigInt, BigUint, ToPrimitive as _};
    use rand::Rng;

    use std::ops::Range;

    pub fn range<T: UnsignedPrimitiveUtil>(start: T, end: T) -> T::Range {
        start.range(end)
    }

    pub trait UnsignedPrimitiveUtil: Sized {
        type Range: Iterator<Item = Self>;
        fn random<R: Rng>(rng: &mut R) -> Self;
        fn try_from_biguint(biguint: BigUint) -> Option<Self>;
        fn try_from_bigint(bigint: BigInt) -> Option<Self>;
        fn rem_biguint(self, biguint: BigUint) -> BigUint;
        fn rem_bigint(self, bigint: BigInt) -> BigInt;
        fn range(self, end: Self) -> Self::Range;
    }

    impl UnsignedPrimitiveUtil for u8 {
        type Range = Range<u8>;

        fn random<R: Rng>(rng: &mut R) -> Self {
            rng.gen()
        }

        fn try_from_biguint(biguint: BigUint) -> Option<Self> {
            biguint.to_u8()
        }
        fn try_from_bigint(bigint: BigInt) -> Option<Self> {
            bigint.to_u8()
        }

        fn rem_biguint(self, biguint: BigUint) -> BigUint {
            biguint % self
        }

        fn rem_bigint(self, bigint: BigInt) -> BigInt {
            bigint % self
        }

        fn range(self, end: Self) -> Range<Self> {
            self..end
        }
    }

    impl UnsignedPrimitiveUtil for u16 {
        type Range = Range<u16>;

        fn random<R: Rng>(rng: &mut R) -> Self {
            rng.gen()
        }

        fn try_from_biguint(biguint: BigUint) -> Option<Self> {
            biguint.to_u16()
        }
        fn try_from_bigint(bigint: BigInt) -> Option<Self> {
            bigint.to_u16()
        }

        fn rem_biguint(self, biguint: BigUint) -> BigUint {
            biguint % self
        }

        fn rem_bigint(self, bigint: BigInt) -> BigInt {
            bigint % self
        }

        fn range(self, end: Self) -> Range<Self> {
            self..end
        }
    }

    impl UnsignedPrimitiveUtil for u32 {
        type Range = Range<u32>;

        fn random<R: Rng>(rng: &mut R) -> Self {
            rng.gen()
        }

        fn try_from_biguint(biguint: BigUint) -> Option<Self> {
            biguint.to_u32()
        }
        fn try_from_bigint(bigint: BigInt) -> Option<Self> {
            bigint.to_u32()
        }

        fn rem_biguint(self, biguint: BigUint) -> BigUint {
            biguint % self
        }

        fn rem_bigint(self, bigint: BigInt) -> BigInt {
            bigint % self
        }

        fn range(self, end: Self) -> Range<Self> {
            self..end
        }
    }

    impl UnsignedPrimitiveUtil for u64 {
        type Range = Range<u64>;

        fn random<R: Rng>(rng: &mut R) -> Self {
            rng.gen()
        }

        fn try_from_biguint(biguint: BigUint) -> Option<Self> {
            biguint.to_u64()
        }
        fn try_from_bigint(bigint: BigInt) -> Option<Self> {
            bigint.to_u64()
        }

        fn rem_biguint(self, biguint: BigUint) -> BigUint {
            biguint % self
        }

        fn rem_bigint(self, bigint: BigInt) -> BigInt {
            bigint % self
        }

        fn range(self, end: Self) -> Range<Self> {
            self..end
        }
    }

    impl UnsignedPrimitiveUtil for u128 {
        type Range = Range<u128>;

        fn random<R: Rng>(rng: &mut R) -> Self {
            rng.gen()
        }

        fn try_from_biguint(biguint: BigUint) -> Option<Self> {
            biguint.to_u128()
        }
        fn try_from_bigint(bigint: BigInt) -> Option<Self> {
            bigint.to_u128()
        }

        fn rem_biguint(self, biguint: BigUint) -> BigUint {
            biguint % self
        }

        fn rem_bigint(self, bigint: BigInt) -> BigInt {
            bigint % self
        }

        fn range(self, end: Self) -> Range<Self> {
            self..end
        }
    }

    impl UnsignedPrimitiveUtil for usize {
        type Range = Range<usize>;

        fn random<R: Rng>(rng: &mut R) -> Self {
            rng.gen()
        }

        fn try_from_biguint(biguint: BigUint) -> Option<Self> {
            biguint.to_usize()
        }
        fn try_from_bigint(bigint: BigInt) -> Option<Self> {
            bigint.to_usize()
        }

        fn rem_biguint(self, biguint: BigUint) -> BigUint {
            biguint % self
        }

        fn rem_bigint(self, bigint: BigInt) -> BigInt {
            bigint % self
        }

        fn range(self, end: Self) -> Range<Self> {
            self..end
        }
    }
}

mod hidden {
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
