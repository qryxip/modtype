//! This crate provides:
//! - Macros that implement modular arithmetic integer types
//! - Preset types
//!     - [`modtype::u64::F`]
//!     - [`modtype::u64::thread_local::F`]
//!
//! # Usage
//!
//! ```
//! #[modtype::use_modtype]
//! type F = modtype::u64::F<1_000_000_007u64>;
//!
//! assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
//! ```
//!
//! To use a customized type, copy the following code via clipboard and edit it.
//!
//! ```
//! #[allow(non_snake_case)]
//! fn F(value: u64) -> F {
//!     F::from(value)
//! }
//!
//! #[derive(
//!     modtype::new,
//!     modtype::get,
//!     Default,
//!     Clone,
//!     Copy,
//!     PartialEq,
//!     Eq,
//!     PartialOrd,
//!     Ord,
//!     modtype::From,
//!     modtype::Into,
//!     modtype::Display,
//!     modtype::Debug,
//!     modtype::FromStr,
//!     modtype::Deref,
//!     modtype::Neg,
//!     modtype::Add,
//!     modtype::AddAssign,
//!     modtype::Sub,
//!     modtype::SubAssign,
//!     modtype::Mul,
//!     modtype::MulAssign,
//!     modtype::Div,
//!     modtype::DivAssign,
//!     modtype::Rem,
//!     modtype::RemAssign,
//!     modtype::Num,
//!     modtype::Unsigned,
//!     modtype::Bounded,
//!     modtype::Zero,
//!     modtype::One,
//!     modtype::FromPrimitive,
//!     modtype::Inv,
//!     modtype::CheckedNeg,
//!     modtype::CheckedAdd,
//!     modtype::CheckedSub,
//!     modtype::CheckedMul,
//!     modtype::CheckedDiv,
//!     modtype::CheckedRem,
//!     modtype::Pow,
//!     modtype::Integer,
//! )]
//! #[modtype(
//!     modulus = "1_000_000_007",
//!     debug(SingleTuple),
//!     neg(for_ref = true),
//!     add(for_ref = true),
//!     add_assign(for_ref = true),
//!     sub(for_ref = true),
//!     sub_assign(for_ref = true),
//!     mul(for_ref = true),
//!     mul_assign(for_ref = true),
//!     div(for_ref = true),
//!     div_assign(for_ref = true),
//!     rem(for_ref = true),
//!     rem_assign(for_ref = true),
//!     inv(for_ref = true),
//!     pow(for_ref = true)
//! )]
//! struct F {
//!     #[modtype(value)]
//!     __value: u64,
//! }
//! ```
//!
//! # Requirements
//!
//! - The inner value is [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or [`usize`].
//! - The inner value and the modulus are of a same type.
//! - The modulus is immutable.
//! - The inner value is always smaller than the modulus.
//!     - If the modular arithmetic type implements [`One`], The modulus is larger than `1`.
//! - If the modular arithmetic type implements [`Div`], the modulus is a prime.
//!
//! # Attributes
//!
//! ## `use_modtype`
//!
//! | Name          | Format                         | Optional                                      |
//! | :------------ | :----------------------------- | :-------------------------------------------- |
//! | `constant`    | `constant($`[`Ident`]`)`       | Yes (default = `concat!(_, $type_uppercase)`) |
//! | `constructor` | `constructor($`[`Ident`]`)`    | Yes (default = the type alias)                |
//!
//! ## Derive Macros
//!
//! ### Struct
//!
//! | Name                 | Format                                                                                                   | Optional                         |
//! | :------------------- | :------------------------------------------------------------------------------------------------------- | :------------------------------- |
//! | `modulus`            | `modulus = $`[`Lit`] where `$`[`Lit`] is converted/parsed to an [`Expr`]                                 | No                               |
//! | `std`                | `std = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]                                          | Yes (default = `::std`)          |
//! | `num_traits`         | `num_traits = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]                                   | Yes (default = `::num::traits`)  |
//! | `num_integer`        | `num_integer = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]                                  | Yes (default = `::num::integer`) |
//! | `num_bigint`         | `num_bigint = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]                                   | Yes (default = `::num::bigint`)  |
//! | `from`               | `from($`[`Ident`]` $(, $`[`Ident`]s`) $(,)?)` where all [`Ident`]s ∈ {`InnerValue`, `BigUint`, `BigInt`} | Yes (default = all)              |
//! | `debug`              | `debug(SingleTuple)` or `debug(Transparent)`                                                             | Yes (default = `SingleTuple`)    |
//! | `neg`                | `neg(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
//! | `add`                | `add(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
//! | `add_assign`         | `add_assign(for_ref = $`[`LitBool`]`)`                                                                   | Yes (default = `true`)           |
//! | `sub`                | `sub(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
//! | `sub_assign`         | `sub_assign(for_ref = $`[`LitBool`]`)`                                                                   | Yes (default = `true`)           |
//! | `mul`                | `mul(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
//! | `mul_assign`         | `mul_assign(for_ref = $`[`LitBool`]`)`                                                                   | Yes (default = `true`)           |
//! | `div`                | `div(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
//! | `div_assign`         | `div_assign(for_ref = $`[`LitBool`]`)`                                                                   | Yes (default = `true`)           |
//! | `rem`                | `rem(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
//! | `rem_assign`         | `rem_assign(for_ref = $`[`LitBool`]`)`                                                                   | Yes (default = `true`)           |
//! | `inv`                | `inv(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
//! | `pow`                | `pow(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
//!
//! ### Field
//!
//! | Name                 | Format  | Optional |
//! | :------------------- | :------ | :------- |
//! | `value`              | `value` | No       |
//!
//! ## [`ConstValue`]
//!
//! ### Struct
//!
//! | Name                 | Format                                                       | Optional  |
//! | :------------------- | :----------------------------------------------------------- | :-------- |
//! | `const_value`        | `const_value = $`[`LitInt`] where `$`[`LitInt`] has a suffix | No        |
//!
//! [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
//! [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
//! [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
//! [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
//! [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
//! [`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
//! [`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
//! [`One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
//! [`Ident`]: https://docs.rs/syn/0.15/syn/struct.Ident.html
//! [`Lit`]: https://docs.rs/syn/0.15/syn/enum.Lit.html
//! [`LitStr`]: https://docs.rs/syn/0.15/syn/struct.LitStr.html
//! [`LitInt`]: https://docs.rs/syn/0.15/syn/struct.LitInt.html
//! [`LitBool`]: https://docs.rs/syn/0.15/syn/struct.LitBool.html
//! [`Expr`]: https://docs.rs/syn/0.15/syn/struct.Expr.html
//! [`Path`]: https://docs.rs/syn/0.15/syn/struct.Path.html
//! [`ConstValue`]: https://docs.rs/modtype_derive/0.3/modtype_derive/derive.ConstValue.html
//! [`modtype::u64::F`]: ./u64/struct.F.html
//! [`modtype::u64::Z`]: ./u64/struct.Z.html
//! [`modtype::u64::thread_local::F`]: ./u64/thread_local/struct.F.html

pub use modtype_derive::use_modtype;

pub use modtype_derive::ConstValue;

pub use modtype_derive::new;

pub use modtype_derive::get;

pub use modtype_derive::From;

pub use modtype_derive::Into;

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

pub use modtype_derive::Integer;

use std::fmt;

/// A trait that has one associated constant value.
///
/// This trait requires [`Copy`]` + `[`Ord`]` + `[`Debug`] because of [`#26925`].
/// To implement this trait, use [the derive macro].
///
/// # Example
///
/// ```
/// use modtype::ConstValue;
///
/// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, ConstValue)]
/// #[modtype(const_value = 17u32)]
/// enum Const17U32 {}
///
/// assert_eq!(Const17U32::VALUE, 17u32);
/// ```
///
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`Ord`]: https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html
/// [`Debug`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html
/// [`#26925`]: https://github.com/rust-lang/rust/issues/26925
/// [the derive macro]: https://docs.rs/modtype_derive/0.3/modtype_derive/derive.ConstValue.html
pub trait ConstValue: Copy + Ord + fmt::Debug {
    type Value: Copy;
    const VALUE: Self::Value;
}

/// Preset tyeps that the inner types are `u64`.
pub mod u64 {
    pub mod thread_local {
        use std::cell::UnsafeCell;

        /// Set a modulus and execute a closure.
        ///
        /// # Example
        ///
        /// ```
        /// use modtype::u64::thread_local::{with_modulus, F};
        ///
        /// with_modulus(7, || {
        ///     assert_eq!(F(6) + F(1), F(0));
        /// });
        /// ```
        pub fn with_modulus<T, F: FnOnce() -> T>(modulus: u64, f: F) -> T {
            unsafe { set_modulus(modulus) };
            f()
        }

        #[allow(non_snake_case)]
        #[inline]
        pub fn F(value: u64) -> F {
            F::new(value)
        }

        #[inline]
        unsafe fn modulus() -> u64 {
            MODULUS.with(|m| *m.get())
        }

        unsafe fn set_modulus(modulus: u64) {
            MODULUS.with(|m| *m.get() = modulus)
        }

        thread_local! {
            static MODULUS: UnsafeCell<u64> = UnsafeCell::new(0);
        }

        /// A modular arithmetic integer type.
        ///
        /// # Example
        ///
        /// ```
        /// use modtype::u64::thread_local::{with_modulus, F};
        ///
        /// with_modulus(7, || {
        ///     assert_eq!(F(6) + F(1), F(0));
        /// });
        /// ```
        #[derive(
            crate::new,
            crate::get,
            Default,
            Clone,
            Copy,
            PartialEq,
            Eq,
            PartialOrd,
            Ord,
            crate::From,
            crate::Into,
            crate::Display,
            crate::Debug,
            crate::FromStr,
            crate::Deref,
            crate::Neg,
            crate::Add,
            crate::AddAssign,
            crate::Sub,
            crate::SubAssign,
            crate::Mul,
            crate::MulAssign,
            crate::Div,
            crate::DivAssign,
            crate::Rem,
            crate::RemAssign,
            crate::Num,
            crate::Unsigned,
            crate::Bounded,
            crate::Zero,
            crate::One,
            crate::FromPrimitive,
            crate::Inv,
            crate::CheckedNeg,
            crate::CheckedAdd,
            crate::CheckedSub,
            crate::CheckedMul,
            crate::CheckedDiv,
            crate::CheckedRem,
            crate::Pow,
            crate::Integer,
        )]
        #[modtype(modulus = "unsafe { modulus() }")]
        pub struct F {
            #[modtype(value)]
            __value: u64,
        }
    }

    use crate::ConstValue;

    use std::marker::PhantomData;

    /// A modular arithmetic integer type.
    ///
    /// # Example
    ///
    /// ```
    /// use modtype::use_modtype;
    /// use num::bigint::{Sign, ToBigInt as _, ToBigUint as _};
    /// use num::pow::Pow as _;
    /// use num::traits::{CheckedNeg as _, CheckedRem as _, Inv as _};
    /// use num::{
    ///     BigInt, BigUint, Bounded as _, CheckedAdd as _, CheckedDiv as _, CheckedMul as _,
    ///     CheckedSub as _, FromPrimitive as _, Integer as _, Num as _, One as _,
    ///     ToPrimitive as _, Unsigned, Zero as _,
    /// };
    ///
    /// #[use_modtype]
    /// type F = modtype::u64::F<7u64>;
    ///
    /// fn static_assert_unsigned<T: Unsigned>() {}
    ///
    /// // Constructor, `new`, `get`
    /// assert_eq!(F(3), F::new(3));
    /// assert_eq!(F(3).get(), 3u64);
    ///
    /// // `From<{u64, BigUint, BigInt}>`, `Into<u64>`
    /// assert_eq!(F::from(3), F(3));
    /// assert_eq!(F::from(BigUint::new(vec![3])), F(3));
    /// assert_eq!(F::from(BigInt::new(Sign::Minus, vec![4])), F(3));
    /// assert_eq!(u64::from(F(3)), 3);
    ///
    /// // `Display`, `Debug`
    /// assert_eq!(F(3).to_string(), "3");
    /// assert_eq!(format!("{:?}", F(3)), "F(3)");
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
    /// assert_eq!(F(6) + F(2), F(1));
    /// assert_eq!(F(0) - F(1), F(6));
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
    /// assert_eq!(F::from_i128(-1), Some(F(0) - F(1)));
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
    /// assert_eq!(num::range_step(F(0), F(6), F(2)).collect::<Vec<_>>(), &[F(0), F(2), F(4)]);
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
    ///
    /// // `Integer`
    /// (0..=6).for_each(|x| (1..=6).for_each(|y| assert!(F(x).is_multiple_of(&F(y)))));
    /// ```
    #[derive(
        crate::new,
        crate::get,
        Default,
        Clone,
        Copy,
        PartialEq,
        Eq,
        PartialOrd,
        Ord,
        crate::From,
        crate::Into,
        crate::Display,
        crate::Debug,
        crate::FromStr,
        crate::Deref,
        crate::Neg,
        crate::Add,
        crate::AddAssign,
        crate::Sub,
        crate::SubAssign,
        crate::Mul,
        crate::MulAssign,
        crate::Div,
        crate::DivAssign,
        crate::Rem,
        crate::RemAssign,
        crate::Num,
        crate::Unsigned,
        crate::Bounded,
        crate::Zero,
        crate::One,
        crate::FromPrimitive,
        crate::Inv,
        crate::CheckedNeg,
        crate::CheckedAdd,
        crate::CheckedSub,
        crate::CheckedMul,
        crate::CheckedDiv,
        crate::CheckedRem,
        crate::Pow,
        crate::Integer,
    )]
    #[modtype(modulus = "M::VALUE")]
    pub struct F<M: ConstValue<Value = u64>> {
        #[modtype(value)]
        __value: u64,
        phantom: PhantomData<fn() -> M>,
    }
}
