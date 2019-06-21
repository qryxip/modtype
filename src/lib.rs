//! This crate provides:
//! - Macros that implement modular arithmetic integer types
//! - Preset types (`modtype::preset::u64{, ::mod1000000007}::{F, Z}`)
//!
//! # Attributes
//!
//! ## Struct
//!
//! | Name                 | Format                                                         | Optional                         |
//! | :------------------- | :------------------------------------------------------------- | -------------------------------- |
//! | `modulus`            | `modulus = #Lit` where `#Lit` is converted/parsed to an `Expr` | No                               |
//! | `std`                | `std = #LitStr` where `#LitStr` is parsed to a `Path`          | Yes (default = `::std`)          |
//! | `num_traits`         | `num_traits = #LitStr` where `#LitStr` is parsed to a `Path`   | Yes (default = `::num::traits`)  |
//! | `num_integer`        | `num_integer = #LitStr` where `#LitStr` is parsed to a `Path`  | Yes (default = `::num::integer`) |
//! | `num_bigint`         | `num_bigint = #LitStr` where `#LitStr` is parsed to a `Path`   | Yes (default = `::num::bigint`)  |
//! | `moving_ops_for_ref` | `moving_ops_for_ref`                                           | Yes                              |
//!
//! ## Field
//!
//! | Name                 | Format  | Optional |
//! | :------------------- | :------ | -------- |
//! | `value`              | `value` | No       |
//!
//! ## `ConstValue`
//!
//! | Name                 | Format                                               | Optional  |
//! | :------------------- | :----------------------------------------------------| --------- |
//! | `const_value`        | `const_value = #LitInt` where `#LitInt` has a suffix | No        |

pub use modtype_derive::ConstValue;

pub use modtype_derive::Into;

pub use modtype_derive::From;

pub use modtype_derive::FromStr;

pub use modtype_derive::Display;

pub use modtype_derive::{DebugTransparent, DebugTransparent as Debug};

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

pub use modtype_derive::Zero;

pub use modtype_derive::One;

pub use modtype_derive::Num;

pub use modtype_derive::Bounded;

pub use modtype_derive::CheckedAdd;

pub use modtype_derive::CheckedSub;

pub use modtype_derive::CheckedMul;

pub use modtype_derive::CheckedDiv;

pub use modtype_derive::CheckedRem;

pub use modtype_derive::CheckedNeg;

pub use modtype_derive::Inv;

pub use modtype_derive::Unsigned;

pub use modtype_derive::FromPrimitive;

pub use modtype_derive::ToPrimitive;

pub use modtype_derive::Pow_u8;

pub use modtype_derive::Pow_u16;

pub use modtype_derive::Pow_u32;

pub use modtype_derive::Pow_usize;

pub use modtype_derive::Integer;

pub use modtype_derive::ToBigUint;

pub use modtype_derive::ToBigInt;

pub use modtype_derive::new;

pub use modtype_derive::get;

use std::fmt;

/// A trait that has one associated constant value.
///
/// # Attribute
///
/// | Name                 | Format                                               | Optional  |
/// | :------------------- | :----------------------------------------------------| --------- |
/// | `const_value`        | `const_value = #LitInt` where `#LitInt` has a suffix | No        |
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
pub trait ConstValue: Copy + Ord + fmt::Debug {
    type Value: Copy;
    const VALUE: Self::Value;
}

/// Preset types.
pub mod preset {
    /// Preset tyeps that the inner types are `u64`.
    pub mod u64 {
        pub mod mod1000000007 {
            use crate::ConstValue;

            /// A `ConstValue` which `VALUE` is `1_000_000_007u64`.
            #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
            pub enum Const1000000007U64 {}

            impl ConstValue for Const1000000007U64 {
                type Value = u64;
                const VALUE: u64 = 1_000_000_007;
            }

            pub type F = crate::preset::u64::F<Const1000000007U64>;
            pub type Z = crate::preset::u64::Z<Const1000000007U64>;
        }

        pub use crate::preset::u64::mod1000000007::Const1000000007U64;

        use crate::ConstValue;

        use std::marker::PhantomData;

        /// A modular arithmetic integer type.
        ///
        /// # Example
        ///
        /// ```
        /// use modtype::ConstValue;
        /// use num::bigint::{ToBigInt as _, ToBigUint as _};
        /// use num::pow::Pow as _;
        /// use num::traits::{CheckedNeg as _, CheckedRem as _};
        /// use num::{Bounded as _, CheckedDiv as _, CheckedMul as _, CheckedSub as _, FromPrimitive as _, Integer as _, Num as _, One as _, ToPrimitive as _, Unsigned, Zero as _};
        ///
        /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, ConstValue)]
        /// #[modtype(const_value = 7u64)]
        /// enum Const7U64 {}
        ///
        /// type F = modtype::preset::u64::F<Const7U64>;
        ///
        /// fn static_assert_unsigned<T: Unsigned>() {}
        ///
        /// assert_eq!(u64::from(F::from(3)), 3);
        /// assert_eq!(F::from(3).to_string(), "3");
        /// assert_eq!(format!("{:?}", F::from(3)), "3");
        /// assert_eq!(*F::from(3), 3);
        /// assert_eq!(-F::from(1), F::from(6));
        /// assert_eq!(F::from(6) + F::from(2), F::from(1));
        /// assert_eq!(F::from(0) - F::from(1), F::from(6));
        /// assert_eq!(F::from(3) * F::from(4), F::from(5));
        /// assert_eq!(F::from(3) / F::from(4), F::from(6));
        /// (0..=6).for_each(|x| (1..=6).for_each(|y| assert_eq!(F::from(x) % F::from(y), F::from(0))));
        /// assert_eq!(F::zero(), F::from(0));
        /// assert_eq!(F::one(), F::from(1));
        /// assert_eq!(F::from_str_radix("111", 2), Ok(F::from(0)));
        /// assert_eq!((F::min_value(), F::max_value()), (F::from(0), F::from(6)));
        /// assert_eq!(num::range_step(F::from(0), F::from(6), F::from(2)).map(|x| *x).collect::<Vec<_>>(), &[0, 2, 4]);
        /// (0..=6).for_each(|x| (0..=6).for_each(|y| assert!(F::from(x).checked_sub(&F::from(y)).is_some())));
        /// (0..=6).for_each(|x| (0..=6).for_each(|y| assert!(F::from(x).checked_mul(&F::from(y)).is_some())));
        /// (0..=6).for_each(|x| assert!(F::from(x).checked_div(&F::from(0)).is_none()));
        /// (0..=6).for_each(|x| assert!(F::from(x).checked_rem(&F::from(0)).is_none()));
        /// (0..=6).for_each(|x| assert!(F::from(x).checked_neg().is_some()));
        /// assert_eq!(F::from_i64(-1), None);
        /// static_assert_unsigned::<F>();
        /// assert_eq!(F::from(3).to_i64(), Some(3i64));
        /// assert_eq!(F::from(3).pow(2u8), F::from(2));
        /// assert_eq!(F::from(3).pow(2u16), F::from(2));
        /// assert_eq!(F::from(3).pow(2u32), F::from(2));
        /// assert_eq!(F::from(3).pow(2usize), F::from(2));
        /// (0..=6).for_each(|x| (1..=6).for_each(|y| assert!(F::from(x).is_multiple_of(&F::from(y)))));
        /// assert_eq!(F::from(3).to_biguint(), 3u64.to_biguint());
        /// assert_eq!(F::from(3).to_bigint(), 3u64.to_bigint());
        /// assert_eq!(F::new(3), F::from(3));
        /// assert_eq!(F::new(3).get(), 3u64);
        /// ```
        #[derive(
            Default,
            Clone,
            Copy,
            PartialEq,
            Eq,
            PartialOrd,
            Ord,
            crate::From,
            crate::Into,
            crate::FromStr,
            crate::Display,
            crate::Debug,
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
            crate::Zero,
            crate::One,
            crate::Num,
            crate::Bounded,
            crate::CheckedAdd,
            crate::CheckedSub,
            crate::CheckedMul,
            crate::CheckedDiv,
            crate::CheckedRem,
            crate::CheckedNeg,
            crate::Inv,
            crate::Unsigned,
            crate::FromPrimitive,
            crate::ToPrimitive,
            crate::Pow_u8,
            crate::Pow_u16,
            crate::Pow_u32,
            crate::Pow_usize,
            crate::Integer,
            crate::ToBigUint,
            crate::ToBigInt,
            crate::new,
            crate::get,
        )]
        #[modtype(
            modulus = "M::VALUE",
            std = "std",
            num_traits = "num::traits",
            num_integer = "num::integer",
            num_bigint = "num::bigint",
            moving_ops_for_ref
        )]
        pub struct F<M: ConstValue<Value = u64>> {
            #[modtype(value)]
            __value: u64,
            phantom: PhantomData<fn() -> M>,
        }

        /// A modular arithmetic integer type.
        ///
        /// # Example
        ///
        /// ```
        /// use modtype::ConstValue;
        /// use num::bigint::{ToBigInt as _, ToBigUint as _};
        /// use num::pow::Pow as _;
        /// use num::traits::{CheckedNeg as _};
        /// use num::{Bounded as _, CheckedMul as _, CheckedSub as _, FromPrimitive as _, One as _, ToPrimitive as _, Zero as _};
        ///
        /// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, ConstValue)]
        /// #[modtype(const_value = 7u64)]
        /// enum Const7U64 {}
        ///
        /// type Z = modtype::preset::u64::Z<Const7U64>;
        ///
        /// assert_eq!(u64::from(Z::from(3)), 3);
        /// assert_eq!(Z::from(3).to_string(), "3");
        /// assert_eq!(format!("{:?}", Z::from(3)), "3");
        /// assert_eq!(*Z::from(3), 3);
        /// assert_eq!(-Z::from(1), Z::from(6));
        /// assert_eq!(Z::from(6) + Z::from(2), Z::from(1));
        /// assert_eq!(Z::from(0) - Z::from(1), Z::from(6));
        /// assert_eq!(Z::from(3) * Z::from(4), Z::from(5));
        /// assert_eq!(Z::zero(), Z::from(0));
        /// assert_eq!(Z::one(), Z::from(1));
        /// assert_eq!((Z::min_value(), Z::max_value()), (Z::from(0), Z::from(6)));
        /// assert_eq!(num::range_step(Z::from(0), Z::from(6), Z::from(2)).map(|x| *x).collect::<Vec<_>>(), &[0, 2, 4]);
        /// (0..=6).for_each(|x| (0..=6).for_each(|y| assert!(Z::from(x).checked_sub(&Z::from(y)).is_some())));
        /// (0..=6).for_each(|x| (0..=6).for_each(|y| assert!(Z::from(x).checked_mul(&Z::from(y)).is_some())));
        /// (0..=6).for_each(|x| assert!(Z::from(x).checked_neg().is_some()));
        /// assert_eq!(Z::from_i64(-1), None);
        /// assert_eq!(Z::from(3).to_i64(), Some(3i64));
        /// assert_eq!(Z::from(3).pow(2u8), Z::from(2));
        /// assert_eq!(Z::from(3).pow(2u16), Z::from(2));
        /// assert_eq!(Z::from(3).pow(2u32), Z::from(2));
        /// assert_eq!(Z::from(3).pow(2usize), Z::from(2));
        /// assert_eq!(Z::from(3).to_biguint(), 3u64.to_biguint());
        /// assert_eq!(Z::from(3).to_bigint(), 3u64.to_bigint());
        /// assert_eq!(Z::new(3), Z::from(3));
        /// assert_eq!(Z::new(3).get(), 3u64);
        /// ```
        #[derive(
            Default,
            Clone,
            Copy,
            PartialEq,
            Eq,
            PartialOrd,
            Ord,
            crate::From,
            crate::Into,
            crate::FromStr,
            crate::Display,
            crate::Debug,
            crate::Deref,
            crate::Neg,
            crate::Add,
            crate::AddAssign,
            crate::Sub,
            crate::SubAssign,
            crate::Mul,
            crate::MulAssign,
            crate::Zero,
            crate::One,
            crate::Bounded,
            crate::CheckedAdd,
            crate::CheckedSub,
            crate::CheckedMul,
            crate::CheckedNeg,
            crate::FromPrimitive,
            crate::ToPrimitive,
            crate::Pow_u8,
            crate::Pow_u16,
            crate::Pow_u32,
            crate::Pow_usize,
            crate::ToBigUint,
            crate::ToBigInt,
            crate::new,
            crate::get,
        )]
        #[modtype(
            modulus = "M::VALUE",
            std = "std",
            num_traits = "num::traits",
            num_integer = "num::integer",
            num_bigint = "num::bigint",
            moving_ops_for_ref
        )]
        pub struct Z<M: ConstValue<Value = u64>> {
            #[modtype(value)]
            __value: u64,
            phantom: PhantomData<fn() -> M>,
        }
    }
}
