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

pub use modtype_derive::{use_modtype, ConstValue, ModType};

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

/// A trait for primitive unsigned integer types. (i.e. `u8`, `u16`, `u32`, `u64`, `u128`, `usize`)
pub trait UnsignedPrimitive:
    Unsigned
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
    + 'static
{
}

impl UnsignedPrimitive for u8 {}
impl UnsignedPrimitive for u16 {}
impl UnsignedPrimitive for u32 {}
impl UnsignedPrimitive for u64 {}
impl UnsignedPrimitive for u128 {}
impl UnsignedPrimitive for usize {}

/// A trait for primitive signed integer types. (i.e. `i8`, `i16`, `i32`, `i64`, `i128`, `isize`)
pub trait SignedPrimitive:
    Signed
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

/// A trait for primitive floating point number type. (i.e. `f32`, `f64`)
pub trait FloatPrimitive:
    Signed
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
/// Note that the default implementation assumes:
/// - Given/Return values are always smaller than the modulus.
/// - The modulus is larger than `1`.
/// - `modulus + modulus` does not overflow.
/// - `modulus * modulus` does not overflow.
/// - If any of the following methods is used, the modulus is a prime.
///     - [`Div`]`::div` (`/` operator. not [`CheckedDiv`]`::checked_div`)
///     - [`DivAssign`]`::div_assign` (`/=` operator)
///     - [`Rem`]`::rem` (`%` operator. not [`CheckedRem`]`::checked_rem`)
///     - [`RemAssign`]`::rem_assign` (`%=` operator)
///     - [`Inv`]`::inv`
///     - [`FromPrimitive`]`::{from_f32, from_f64}`
///
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

    #[inline(always)]
    fn new(value: Self::Target, modulus: Self::Target) -> Self::Target {
        if value >= modulus {
            value % modulus
        } else {
            value
        }
    }

    #[inline(always)]
    fn get(value: Self::Target, _modulus: Self::Target) -> Self::Target {
        value
    }

    #[inline(always)]
    fn from_biguint(value: BigUint, modulus: Self::Target) -> Self::Target {
        let modulus = Into::<BigUint>::into(modulus);
        (value % modulus).to_string().parse().unwrap()
    }

    #[inline(always)]
    fn from_bigint(mut value: BigInt, modulus: Self::Target) -> Self::Target {
        let is_neg = value.is_negative();
        if is_neg {
            value = -value;
        }
        let modulus_big = Into::<BigInt>::into(modulus);
        let acc = (value % modulus_big)
            .to_string()
            .parse::<Self::Target>()
            .unwrap();
        if is_neg {
            modulus - acc
        } else {
            acc
        }
    }

    #[inline(always)]
    fn fmt_display(
        value: Self::Target,
        _modulus: Self::Target,
        fmt: &mut fmt::Formatter,
    ) -> fmt::Result {
        <Self::Target as fmt::Display>::fmt(&value, fmt)
    }

    #[inline(always)]
    fn fmt_debug(
        value: Self::Target,
        _modulus: Self::Target,
        _ty: &'static str,
        fmt: &mut fmt::Formatter,
    ) -> fmt::Result {
        <Self::Target as fmt::Debug>::fmt(&value, fmt)
    }

    #[inline(always)]
    fn from_str(str: &str, modulus: Self::Target) -> Result<Self::Target, ParseIntError> {
        str.parse().map(|v| Self::new(v, modulus))
    }

    #[inline(always)]
    fn neg(value: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<Subtraction = True>,
    {
        modulus - value
    }

    #[inline(always)]
    fn add(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<Addition = True>,
    {
        Self::new(lhs + rhs, modulus)
    }

    #[inline(always)]
    fn sub(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<Subtraction = True>,
    {
        let acc = if lhs < rhs {
            modulus + lhs - rhs
        } else {
            lhs - rhs
        };
        Self::new(acc, modulus)
    }

    #[inline(always)]
    fn mul(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<Multiplication = True>,
    {
        Self::new(lhs * rhs, modulus)
    }

    #[inline(always)]
    fn div(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<Division = True>,
    {
        if rhs == Self::Target::zero() {
            panic!("attempt to divide by zero");
        }
        Self::checked_div(lhs, rhs, modulus)
            .expect("could not divide. if the modulus is a prime, THIS IS A BUG.")
    }

    #[inline(always)]
    fn rem(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<Division = True>,
    {
        if rhs == Self::Target::zero() {
            panic!("attempt to calculate the remainder with a divisor of zero");
        }
        if integer::gcd(rhs, modulus) != Self::Target::one() {
            panic!("{}/{} (mod {}) does not exist", lhs, rhs, modulus);
        }
        Self::Target::zero()
    }

    #[inline(always)]
    fn inv(value: Self::Target, modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<Division = True>,
    {
        Self::div(Self::Target::one(), value, modulus)
    }

    #[inline(always)]
    fn from_str_radix(
        str: &str,
        radix: u32,
        modulus: Self::Target,
    ) -> Result<Self::Target, ParseIntError>
    where
        Self::Features:
            Features<Addition = True, Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::Target::from_str_radix(str, radix).map(|v| Self::new(v, modulus))
    }

    #[inline(always)]
    fn min_value(_modulus: Self::Target) -> Self::Target {
        Self::Target::zero()
    }

    #[inline(always)]
    fn max_value(modulus: Self::Target) -> Self::Target {
        modulus - Self::Target::one()
    }

    #[inline(always)]
    fn zero(_modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<Addition = True>,
    {
        Self::Target::zero()
    }

    #[inline(always)]
    fn is_zero(value: Self::Target, _modulus: Self::Target) -> bool
    where
        Self::Features: Features<Addition = True>,
    {
        value == Self::Target::zero()
    }

    #[inline(always)]
    fn one(_modulus: Self::Target) -> Self::Target
    where
        Self::Features: Features<Multiplication = True>,
    {
        Self::Target::one()
    }

    #[inline(always)]
    fn is_one(value: Self::Target, _modulus: Self::Target) -> bool
    where
        Self::Features: Features<Multiplication = True>,
    {
        value == Self::Target::one()
    }

    #[inline(always)]
    fn from_i64(value: i64, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::from_i128(value.to_i128()?, modulus)
    }

    #[inline(always)]
    fn from_u64(value: u64, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::from_u128(value.to_u128()?, modulus)
    }

    #[inline(always)]
    fn from_isize(value: isize, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::from_i128(value.to_i128()?, modulus)
    }

    #[inline(always)]
    fn from_i8(value: i8, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::from_i128(value.to_i128()?, modulus)
    }

    #[inline(always)]
    fn from_i16(value: i16, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::from_i128(value.to_i128()?, modulus)
    }

    #[inline(always)]
    fn from_i32(value: i32, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::from_i128(value.to_i128()?, modulus)
    }

    #[inline(always)]
    fn from_i128(value: i128, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        if value < 0 {
            Self::from_u128((-value).to_u128()?, modulus).map(|v| Self::neg(v, modulus))
        } else {
            Self::from_u128(value.to_u128()?, modulus)
        }
    }

    #[inline(always)]
    fn from_usize(value: usize, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::from_u128(value.to_u128()?, modulus)
    }

    #[inline(always)]
    fn from_u8(value: u8, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::from_u128(value.to_u128()?, modulus)
    }

    #[inline(always)]
    fn from_u16(value: u16, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::from_u128(value.to_u128()?, modulus)
    }

    #[inline(always)]
    fn from_u32(value: u32, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        Self::from_u128(value.to_u128()?, modulus)
    }

    #[inline(always)]
    fn from_u128(mut value: u128, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        let modulus = modulus.to_u128()?;
        if value >= modulus {
            value %= modulus;
        }
        Self::Target::from_u128(value)
    }

    #[inline(always)]
    fn from_float_prim<F: FloatPrimitive>(value: F, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True, Multiplication = True, Division = True>,
    {
        let (man, exp, sign) = value.integer_decode();
        let acc = Self::mul(
            Self::from_u64(man, modulus)?,
            Self::pow_signed(Self::Target::one() + Self::Target::one(), exp, modulus),
            modulus,
        );
        Some(match sign {
            -1 => Self::neg(acc, modulus),
            _ => acc,
        })
    }

    #[inline(always)]
    fn checked_neg(value: Self::Target, modulus: Self::Target) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True>,
    {
        Some(Self::neg(value, modulus))
    }

    #[inline(always)]
    fn checked_add(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target>
    where
        Self::Features: Features<Addition = True>,
    {
        lhs.checked_add(&rhs).map(|v| Self::new(v, modulus))
    }

    #[inline(always)]
    fn checked_sub(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target>
    where
        Self::Features: Features<Subtraction = True>,
    {
        (lhs + modulus)
            .checked_sub(&rhs)
            .map(|v| Self::new(v, modulus))
    }

    #[inline(always)]
    fn checked_mul(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target>
    where
        Self::Features: Features<Multiplication = True>,
    {
        lhs.checked_mul(&rhs).map(|v| Self::new(v, modulus))
    }

    #[inline(always)]
    fn checked_div(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target>
    where
        Self::Features: Features<Division = True>,
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

    #[inline(always)]
    fn checked_rem(
        _lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target> {
        if integer::gcd(rhs, modulus) == Self::Target::one() {
            Some(Self::Target::zero())
        } else {
            None
        }
    }

    #[inline(always)]
    fn pow_unsigned<E: UnsignedPrimitive>(
        base: Self::Target,
        exp: E,
        modulus: Self::Target,
    ) -> Self::Target
    where
        Self::Features: Features<Multiplication = True>,
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

    #[inline(always)]
    fn pow_signed<E: SignedPrimitive>(
        base: Self::Target,
        exp: E,
        modulus: Self::Target,
    ) -> Self::Target
    where
        Self::Features: Features<Multiplication = True, Division = True>,
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
    type Addition: TypedBool;
    type Subtraction: TypedBool;
    type Multiplication: TypedBool;
    type Division: TypedBool;
}

/// The default features.
pub enum DefaultFeatures {}

impl Features for DefaultFeatures {
    type Addition = True;
    type Subtraction = True;
    type Multiplication = True;
    type Division = True;
}

/// Type level boolean.
pub trait TypedBool {}

/// A [`TypedBool`] which represents "true".
///
/// [`TypedBool`]: ./trait.TypedBool.html
pub enum True {}

impl TypedBool for True {}

/// A [`TypedBool`] which represents "false".
///
/// [`TypedBool`]: ./trait.TypedBool.html
pub enum False {}

impl TypedBool for False {}

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
/// // Constructor, `new`, `new_unchecked`, `get`
/// assert_eq!(F::new(8), F(1));
/// assert_ne!(F::new_unchecked(8), F(1));
/// assert_eq!(F(3).get(), 3u32);
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
}

/// A modular arithmetic integer type which modulus is **a `struct` field**.
pub mod field_param {
    use crate::{Cartridge, DefaultCartridge, UnsignedPrimitive};

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

        /// Gets the modulus.
        #[inline]
        pub fn modulus(self) -> T {
            self.modulus
        }
    }
}

/// A modular arithmetic integer type which modulus is **`thread_local`**.
pub mod thread_local {
    use crate::{Cartridge, DefaultCartridge, UnsignedPrimitive};

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
