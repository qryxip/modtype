//! This crate provides modular arithmetic integer types.
//!
//! # Usage
//!
//! ## [`modtype::Z`]
//!
//! ```
//! #[modtype::use_modtype]
//! type F = modtype::u64::Z<1_000_000_007u64>;
//!
//! assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
//! ```
//!
//! ## [`modtype::thread_local::Z`]
//!
//! ```
//! #[allow(non_snake_case)]
//! modtype::thread_local::u32::Z::with(57, |Z| {
//!     assert_eq!(Z(42) + Z(15), Z(0));
//! });
//! ```
//!
//! ## [`modtype::field_param::Z`]
//!
//! ```
//! use modtype::field_param::u32::Z;
//! use num::CheckedDiv as _;
//!
//! #[allow(non_snake_case)]
//! let Z = Z::factory(1000);
//!
//! assert_eq!(Z(1).checked_div(&Z(777)), Some(Z(713))); // 777 × 713 ≡ 1 (mod 1000)
//! ```
//!
//! # Customization
//!
//! `Z`s can be customized via [`modtype::Impl`].
//!
//! ```
//! #[modtype::use_modtype]
//! type F = modtype::Z<u64, Impl, 1_000_000_007u64>;
//!
//! enum Impl {}
//!
//! impl modtype::Impl for Impl {
//!     type Target = u64;
//!
//!     // your implementation here
//! }
//! ```
//!
//! # Attributes for [`use_modtype`]
//!
//! | Name          | Format                         | Optional                                                |
//! | :------------ | :----------------------------- | :------------------------------------------------------ |
//! | `constant`    | `constant($`[`Ident`]`)`       | Yes (default = `concat!(_, $value, $type_pascal_case)`) |
//! | `constructor` | `constructor($`[`Ident`]`)`    | Yes (default = the type alias)                          |
//!
//! [`Ident`]: https://docs.rs/syn/0.15/syn/struct.Ident.html
//! [`modtype::Z`]: ./struct.Z.html
//! [`modtype::thread_local::Z`]: ./thread_local/struct.Z.html
//! [`modtype::field_param::Z`]: ./field_param/struct.Z.html
//! [`modtype::Impl`]: ./trait.Impl.html
//! [`use_modtype`]: https://docs.rs/modtype_derive/0.5/modtype_derive/attr.use_modtype.html

pub use modtype_derive::use_modtype;

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
/// use modtype::derive::ConstValue;
/// use modtype::ConstValue as _;
///
/// #[derive(ConstValue)]
/// #[modtype(const_value = 17u32)]
/// enum Const17U32 {}
///
/// assert_eq!(Const17U32::VALUE, 17u32);
/// ```
///
/// [`use_modtype`]: https://docs.rs/modtype_derive/0.5/modtype_derive/attr.use_modtype.html
/// [the derive macro]: https://docs.rs/modtype_derive/0.5/modtype_derive/derive.ConstValue.html
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
pub trait Impl {
    type Target: UnsignedPrimitive;

    #[inline]
    fn new(value: Self::Target, modulus: Self::Target) -> Self::Target {
        if value >= modulus {
            value % modulus
        } else {
            value
        }
    }

    #[inline]
    fn get(value: Self::Target, _modulus: Self::Target) -> Self::Target {
        value
    }

    #[inline]
    fn from_biguint(value: BigUint, modulus: Self::Target) -> Self::Target {
        let modulus = Into::<BigUint>::into(modulus);
        (value % modulus).to_string().parse().unwrap()
    }

    #[inline]
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

    #[inline]
    fn fmt_display(
        value: Self::Target,
        _modulus: Self::Target,
        fmt: &mut fmt::Formatter,
    ) -> fmt::Result {
        <Self::Target as fmt::Display>::fmt(&value, fmt)
    }

    #[inline]
    fn fmt_debug(
        value: Self::Target,
        _modulus: Self::Target,
        _ty: &'static str,
        fmt: &mut fmt::Formatter,
    ) -> fmt::Result {
        <Self::Target as fmt::Debug>::fmt(&value, fmt)
    }

    #[inline]
    fn from_str(str: &str, modulus: Self::Target) -> Result<Self::Target, ParseIntError> {
        str.parse().map(|v| Self::new(v, modulus))
    }

    #[inline]
    fn neg(value: Self::Target, modulus: Self::Target) -> Self::Target {
        modulus - value
    }

    #[inline]
    fn add(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target {
        Self::new(lhs + rhs, modulus)
    }

    #[inline]
    fn sub(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target {
        let acc = if lhs < rhs {
            modulus + lhs - rhs
        } else {
            lhs - rhs
        };
        Self::new(acc, modulus)
    }

    #[inline]
    fn mul(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target {
        Self::new(lhs * rhs, modulus)
    }

    #[inline]
    fn div(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target {
        if rhs == Self::Target::zero() {
            panic!("attempt to divide by zero");
        }
        Self::checked_div(lhs, rhs, modulus)
            .expect("could not divide. if the modulus is a prime, THIS IS A BUG.")
    }

    #[inline]
    fn rem(lhs: Self::Target, rhs: Self::Target, modulus: Self::Target) -> Self::Target {
        if rhs == Self::Target::zero() {
            panic!("attempt to calculate the remainder with a divisor of zero");
        }
        if integer::gcd(rhs, modulus) != Self::Target::one() {
            panic!("{}/{} (mod {}) does not exist", lhs, rhs, modulus);
        }
        Self::Target::zero()
    }

    #[inline]
    fn inv(value: Self::Target, modulus: Self::Target) -> Self::Target {
        Self::div(Self::Target::one(), value, modulus)
    }

    #[inline]
    fn from_str_radix(
        str: &str,
        radix: u32,
        modulus: Self::Target,
    ) -> Result<Self::Target, ParseIntError> {
        Self::Target::from_str_radix(str, radix).map(|v| Self::new(v, modulus))
    }

    #[inline]
    fn min_value(_modulus: Self::Target) -> Self::Target {
        Self::Target::zero()
    }

    #[inline]
    fn max_value(modulus: Self::Target) -> Self::Target {
        modulus - Self::Target::one()
    }

    #[inline]
    fn zero(_modulus: Self::Target) -> Self::Target {
        Self::Target::zero()
    }

    #[inline]
    fn is_zero(value: Self::Target, _modulus: Self::Target) -> bool {
        value == Self::Target::zero()
    }

    #[inline]
    fn one(_modulus: Self::Target) -> Self::Target {
        Self::Target::one()
    }

    #[inline]
    fn is_one(value: Self::Target, _modulus: Self::Target) -> bool {
        value == Self::Target::one()
    }

    #[inline]
    fn from_i64(value: i64, modulus: Self::Target) -> Option<Self::Target> {
        Self::from_i128(value.to_i128()?, modulus)
    }

    #[inline]
    fn from_u64(value: u64, modulus: Self::Target) -> Option<Self::Target> {
        Self::from_u128(value.to_u128()?, modulus)
    }

    #[inline]
    fn from_isize(value: isize, modulus: Self::Target) -> Option<Self::Target> {
        Self::from_i128(value.to_i128()?, modulus)
    }

    #[inline]
    fn from_i8(value: i8, modulus: Self::Target) -> Option<Self::Target> {
        Self::from_i128(value.to_i128()?, modulus)
    }

    #[inline]
    fn from_i16(value: i16, modulus: Self::Target) -> Option<Self::Target> {
        Self::from_i128(value.to_i128()?, modulus)
    }

    #[inline]
    fn from_i32(value: i32, modulus: Self::Target) -> Option<Self::Target> {
        Self::from_i128(value.to_i128()?, modulus)
    }

    #[inline]
    fn from_i128(value: i128, modulus: Self::Target) -> Option<Self::Target> {
        if value < 0 {
            Self::from_u128((-value).to_u128()?, modulus).map(|v| Self::neg(v, modulus))
        } else {
            Self::from_u128(value.to_u128()?, modulus)
        }
    }

    #[inline]
    fn from_usize(value: usize, modulus: Self::Target) -> Option<Self::Target> {
        Self::from_u128(value.to_u128()?, modulus)
    }

    #[inline]
    fn from_u8(value: u8, modulus: Self::Target) -> Option<Self::Target> {
        Self::from_u128(value.to_u128()?, modulus)
    }

    #[inline]
    fn from_u16(value: u16, modulus: Self::Target) -> Option<Self::Target> {
        Self::from_u128(value.to_u128()?, modulus)
    }

    #[inline]
    fn from_u32(value: u32, modulus: Self::Target) -> Option<Self::Target> {
        Self::from_u128(value.to_u128()?, modulus)
    }

    #[inline]
    fn from_u128(mut value: u128, modulus: Self::Target) -> Option<Self::Target> {
        let modulus = modulus.to_u128()?;
        if value >= modulus {
            value %= modulus;
        }
        Self::Target::from_u128(value)
    }

    #[inline]
    fn from_float_prim<F: FloatPrimitive>(value: F, modulus: Self::Target) -> Option<Self::Target> {
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

    #[inline]
    fn checked_neg(value: Self::Target, modulus: Self::Target) -> Option<Self::Target> {
        Some(Self::neg(value, modulus))
    }

    #[inline]
    fn checked_add(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target> {
        lhs.checked_add(&rhs).map(|v| Self::new(v, modulus))
    }

    #[inline]
    fn checked_sub(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target> {
        (lhs + modulus)
            .checked_sub(&rhs)
            .map(|v| Self::new(v, modulus))
    }

    #[inline]
    fn checked_mul(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target> {
        lhs.checked_mul(&rhs).map(|v| Self::new(v, modulus))
    }

    #[inline]
    fn checked_div(
        lhs: Self::Target,
        rhs: Self::Target,
        modulus: Self::Target,
    ) -> Option<Self::Target> {
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

    #[inline]
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

    #[inline]
    fn pow_unsigned<E: UnsignedPrimitive>(
        base: Self::Target,
        exp: E,
        modulus: Self::Target,
    ) -> Self::Target {
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

    #[inline]
    fn pow_signed<E: SignedPrimitive>(
        base: Self::Target,
        exp: E,
        modulus: Self::Target,
    ) -> Self::Target {
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
pub enum DefaultImpl<T: UnsignedPrimitive> {
    Infallible(Infallible, PhantomData<fn() -> T>),
}

impl<T: UnsignedPrimitive> Impl for DefaultImpl<T> {
    type Target = T;
}

/// A modular arithmetic integer type which modulus is **a constant**.
///
/// # Examples
///
/// ```
/// use modtype::use_modtype;
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
/// type F = modtype::u32::Z<7u32>;
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
#[derive(
    crate::derive::new,
    crate::derive::new_unchecked,
    crate::derive::get,
    crate::derive::Clone,
    crate::derive::Copy,
    crate::derive::Default,
    crate::derive::PartialEq,
    crate::derive::Eq,
    crate::derive::PartialOrd,
    crate::derive::Ord,
    crate::derive::From,
    crate::derive::Display,
    crate::derive::Debug,
    crate::derive::FromStr,
    crate::derive::Deref,
    crate::derive::Neg,
    crate::derive::Add,
    crate::derive::AddAssign,
    crate::derive::Sub,
    crate::derive::SubAssign,
    crate::derive::Mul,
    crate::derive::MulAssign,
    crate::derive::Div,
    crate::derive::DivAssign,
    crate::derive::Rem,
    crate::derive::RemAssign,
    crate::derive::Num,
    crate::derive::Unsigned,
    crate::derive::Bounded,
    crate::derive::Zero,
    crate::derive::One,
    crate::derive::FromPrimitive,
    crate::derive::Inv,
    crate::derive::CheckedNeg,
    crate::derive::CheckedAdd,
    crate::derive::CheckedSub,
    crate::derive::CheckedMul,
    crate::derive::CheckedDiv,
    crate::derive::CheckedRem,
    crate::derive::Pow,
)]
#[modtype(modulus = "M::VALUE", implementation = "I", modtype = "crate")]
pub struct Z<T: UnsignedPrimitive, I: Impl<Target = T>, M: ConstValue<Value = T>> {
    #[modtype(value)]
    value: T,
    phantom: PhantomData<fn() -> (M, I)>,
}

impl<T: UnsignedPrimitive, I: Impl<Target = T>, M: ConstValue<Value = T>> Z<T, I, M> {
    /// Gets the modulus.
    #[inline]
    pub fn modulus() -> T {
        <M as ConstValue>::VALUE
    }
}

/// A type alias.
pub mod u8 {
    use crate::DefaultImpl;

    /// A type alias.
    pub type Z<M> = crate::Z<u8, DefaultImpl<u8>, M>;
}

/// A type alias.
pub mod u16 {
    use crate::DefaultImpl;

    /// A type alias.
    pub type Z<M> = crate::Z<u16, DefaultImpl<u16>, M>;
}

/// A type alias.
pub mod u32 {
    use crate::DefaultImpl;

    /// A type alias.
    pub type Z<M> = crate::Z<u32, DefaultImpl<u32>, M>;
}

/// A type alias.
pub mod u64 {
    use crate::DefaultImpl;

    /// A type alias.
    pub type Z<M> = crate::Z<u64, DefaultImpl<u64>, M>;
}

/// A type alias.
pub mod u128 {
    use crate::DefaultImpl;

    /// A type alias.
    pub type Z<M> = crate::Z<u128, DefaultImpl<u128>, M>;
}

/// A type alias.
pub mod usize {
    use crate::DefaultImpl;

    /// A type alias.
    pub type Z<M> = crate::Z<usize, DefaultImpl<usize>, M>;
}

/// A modular arithmetic integer type which modulus is **a `struct` field**.
pub mod field_param {
    use crate::{Impl, UnsignedPrimitive};

    use std::marker::PhantomData;

    /// A modular arithmetic integer type which modulus is **a `struct` field**.
    ///
    /// # Example
    ///
    /// ```
    /// use num::CheckedDiv as _;
    ///
    /// #[allow(non_snake_case)]
    /// let Z = modtype::field_param::u32::Z::factory(1000);
    ///
    /// assert_eq!(Z(1).checked_div(&Z(777)), Some(Z(713))); // 777 × 713 ≡ 1 (mod 1000)
    /// ```
    #[derive(
        crate::derive::Clone,
        crate::derive::Copy,
        crate::derive::PartialEq,
        crate::derive::Eq,
        crate::derive::PartialOrd,
        crate::derive::Ord,
        crate::derive::Display,
        crate::derive::Debug,
        crate::derive::Deref,
        crate::derive::Neg,
        crate::derive::Add,
        crate::derive::AddAssign,
        crate::derive::Sub,
        crate::derive::SubAssign,
        crate::derive::Mul,
        crate::derive::MulAssign,
        crate::derive::Div,
        crate::derive::DivAssign,
        crate::derive::Rem,
        crate::derive::RemAssign,
        crate::derive::Inv,
        crate::derive::CheckedNeg,
        crate::derive::CheckedAdd,
        crate::derive::CheckedSub,
        crate::derive::CheckedMul,
        crate::derive::CheckedDiv,
        crate::derive::CheckedRem,
        crate::derive::Pow,
    )]
    #[modtype(modulus = "self.modulus", implementation = "I", modtype = "crate")]
    pub struct Z<T: UnsignedPrimitive, I: Impl<Target = T>> {
        #[modtype(value)]
        value: T,
        modulus: T,
        phantom: PhantomData<fn() -> I>,
    }

    impl<T: UnsignedPrimitive, I: Impl<Target = T>> Z<T, I> {
        /// Constructs a new `Z`.
        #[inline]
        pub fn new(value: T, modulus: T) -> Self {
            Self {
                value: I::new(value, modulus),
                modulus,
                phantom: PhantomData,
            }
        }

        /// Constructs a new `Z` without checking the value.
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

    /// A type alias.
    pub mod u8 {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::field_param::Z<u8, DefaultImpl<u8>>;
    }

    /// A type alias.
    pub mod u16 {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::field_param::Z<u16, DefaultImpl<u16>>;
    }

    /// A type alias.
    pub mod u32 {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::field_param::Z<u32, DefaultImpl<u32>>;
    }

    /// A type alias.
    pub mod u64 {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::field_param::Z<u64, DefaultImpl<u64>>;
    }

    /// A type alias.
    pub mod u128 {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::field_param::Z<u128, DefaultImpl<u128>>;
    }

    /// A type alias.
    pub mod usize {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::field_param::Z<usize, DefaultImpl<usize>>;
    }
}

/// A modular arithmetic integer type which modulus is **`thread_local`**.
pub mod thread_local {
    use crate::{Impl, UnsignedPrimitive};

    use std::cell::UnsafeCell;
    use std::marker::PhantomData;
    use std::thread::LocalKey;

    /// A modular arithmetic integer type which modulus is **`thread_local`**.
    ///
    /// # Example
    ///
    /// ```
    /// #[allow(non_snake_case)]
    /// modtype::thread_local::u32::Z::with(57, |Z| {
    ///     assert_eq!(Z(42) + Z(15), Z(0));
    /// });
    /// ```
    #[derive(
        crate::derive::new,
        crate::derive::new_unchecked,
        crate::derive::get,
        crate::derive::Clone,
        crate::derive::Copy,
        crate::derive::Default,
        crate::derive::PartialEq,
        crate::derive::Eq,
        crate::derive::PartialOrd,
        crate::derive::Ord,
        crate::derive::From,
        crate::derive::Display,
        crate::derive::Debug,
        crate::derive::FromStr,
        crate::derive::Deref,
        crate::derive::Neg,
        crate::derive::Add,
        crate::derive::AddAssign,
        crate::derive::Sub,
        crate::derive::SubAssign,
        crate::derive::Mul,
        crate::derive::MulAssign,
        crate::derive::Div,
        crate::derive::DivAssign,
        crate::derive::Rem,
        crate::derive::RemAssign,
        crate::derive::Num,
        crate::derive::Unsigned,
        crate::derive::Bounded,
        crate::derive::Zero,
        crate::derive::One,
        crate::derive::FromPrimitive,
        crate::derive::Inv,
        crate::derive::CheckedNeg,
        crate::derive::CheckedAdd,
        crate::derive::CheckedSub,
        crate::derive::CheckedMul,
        crate::derive::CheckedDiv,
        crate::derive::CheckedRem,
        crate::derive::Pow,
    )]
    #[modtype(
        modulus = "unsafe { T::modulus() }",
        implementation = "I",
        modtype = "crate"
    )]
    pub struct Z<T: HasThreadLocalModulus, I: Impl<Target = T>> {
        #[modtype(value)]
        value: T,
        phantom: PhantomData<fn() -> I>,
    }

    impl<T: HasThreadLocalModulus, I: Impl<Target = T>> Z<T, I> {
        /// Gets the modulus.
        #[inline]
        pub fn modulus() -> T {
            unsafe { T::modulus() }
        }
    }

    impl<T: HasThreadLocalModulus, I: Impl<Target = T>> Z<T, I> {
        /// Sets `modulus` and run `f`.
        ///
        /// The modulus is set to `0` when `f` finished.
        pub fn with<O, C: FnOnce(fn(T) -> Self) -> O>(modulus: T, f: C) -> O {
            unsafe { T::set_modulus(modulus) };
            let ret = f(Self::new);
            unsafe { T::set_modulus(T::zero()) };
            ret
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

    /// A type alias.
    pub mod u8 {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::thread_local::Z<u8, DefaultImpl<u8>>;
    }

    /// A type alias.
    pub mod u16 {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::thread_local::Z<u16, DefaultImpl<u16>>;
    }

    /// A type alias.
    pub mod u32 {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::thread_local::Z<u32, DefaultImpl<u32>>;
    }

    /// A type alias.
    pub mod u64 {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::thread_local::Z<u64, DefaultImpl<u64>>;
    }

    /// A type alias.
    pub mod u128 {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::thread_local::Z<u128, DefaultImpl<u128>>;
    }

    /// A type alias.
    pub mod usize {
        use crate::DefaultImpl;

        /// A type alias.
        pub type Z = crate::thread_local::Z<usize, DefaultImpl<usize>>;
    }
}

pub mod derive {
    //! Derive macros.
    //!
    //! # Attributes
    //!
    //! ## Struct
    //!
    //! | Name             | Format                                                                     | Optional                         |
    //! | :--------------- | :------------------------------------------------------------------------- | :------------------------------- |
    //! | `modulus`        | `modulus = $`[`Lit`] where `$`[`Lit`] is converted/parsed to an [`Expr`]   | No                               |
    //! | `implementation` | `implementation = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`] | No                               |
    //! | `std`            | `std = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]            | Yes (default = `::std`)          |
    //! | `num_traits`     | `num_traits = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]     | Yes (default = `::num::traits`)  |
    //! | `num_integer`    | `num_integer = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]    | Yes (default = `::num::integer`) |
    //! | `num_bigint`     | `num_bigint = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]     | Yes (default = `::num::bigint`)  |
    //! | `modtype`        | `modtype = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]        | Yes (default = `::modtype`)      |
    //!
    //! ## Field
    //!
    //! | Name                 | Format  | Optional |
    //! | :------------------- | :------ | :------- |
    //! | `value`              | `value` | No       |
    //!
    //! # [`ConstValue`]
    //!
    //! ## Struct
    //!
    //! | Name                 | Format                                                       | Optional  |
    //! | :------------------- | :----------------------------------------------------------- | :-------- |
    //! | `const_value`        | `const_value = $`[`LitInt`] where `$`[`LitInt`] has a suffix | No        |
    //!
    //! [`Ident`]: https://docs.rs/syn/0.15/syn/struct.Ident.html
    //! [`Lit`]: https://docs.rs/syn/0.15/syn/enum.Lit.html
    //! [`LitStr`]: https://docs.rs/syn/0.15/syn/struct.LitStr.html
    //! [`LitInt`]: https://docs.rs/syn/0.15/syn/struct.LitInt.html
    //! [`Expr`]: https://docs.rs/syn/0.15/syn/struct.Expr.html
    //! [`Path`]: https://docs.rs/syn/0.15/syn/struct.Path.html
    //! [`ConstValue`]: https://docs.rs/modtype_derive/0.5/modtype_derive/derive.ConstValue.html

    pub use modtype_derive::ConstValue;

    pub use modtype_derive::new;

    pub use modtype_derive::new_unchecked;

    pub use modtype_derive::get;

    pub use modtype_derive::From;

    pub use modtype_derive::Into;

    pub use modtype_derive::ModtypeClone as Clone;

    pub use modtype_derive::ModtypeCopy as Copy;

    pub use modtype_derive::ModtypeDefault as Default;

    pub use modtype_derive::ModtypePartialEq as PartialEq;

    pub use modtype_derive::ModtypeEq as Eq;

    pub use modtype_derive::ModtypePartialOrd as PartialOrd;

    pub use modtype_derive::ModtypeOrd as Ord;

    pub use modtype_derive::Display;

    pub use modtype_derive::ModtypeDebug as Debug;

    pub use modtype_derive::FromStr;

    pub use modtype_derive::Deref;

    pub use modtype_derive::Neg;

    pub use modtype_derive::Add;

    pub use modtype_derive::AddAssign;

    pub use modtype_derive::Sub;

    pub use modtype_derive::SubAssign;

    pub use modtype_derive::Mul;

    pub use modtype_derive::MulAssign;

    pub use modtype_derive::Div;

    pub use modtype_derive::DivAssign;

    pub use modtype_derive::Rem;

    pub use modtype_derive::RemAssign;

    pub use modtype_derive::Num;

    pub use modtype_derive::Unsigned;

    pub use modtype_derive::Bounded;

    pub use modtype_derive::Zero;

    pub use modtype_derive::One;

    pub use modtype_derive::FromPrimitive;

    pub use modtype_derive::Inv;

    pub use modtype_derive::CheckedNeg;

    pub use modtype_derive::CheckedAdd;

    pub use modtype_derive::CheckedSub;

    pub use modtype_derive::CheckedMul;

    pub use modtype_derive::CheckedDiv;

    pub use modtype_derive::CheckedRem;

    pub use modtype_derive::Pow;
}
