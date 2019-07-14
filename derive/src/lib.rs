#![recursion_limit = "256"]

macro_rules! bail {
    ($span:expr, $fmt:literal $(, $arg:expr)* $(,)?) => {
        return Err(syn::Error::new($span, format!($fmt $(, $arg)*)))
    }
}

macro_rules! try_syn {
    ($expr:expr) => {
        match $expr {
            Ok(expr) => expr,
            Err::<_, syn::Error>(err) => return err.to_compile_error().into(),
        }
    };
}

extern crate proc_macro;

mod const_value;
mod context;
mod use_modtype;

use crate::context::Context;

use quote::quote;
use syn::{parse_macro_input, DeriveInput};

use std::convert::TryFrom as _;

/// An attribute macro to use a modular arithmetic type with a [`ConstValue`] argument.
///
/// This macro:
/// 1. Confirms that the type contains 1 const argument.
/// 2. Creates a bottom type that represents the const value.
/// 3. Implements [`ConstValue`] for the bottom type.
/// 4. Replaces the const argument with the bottom type.
/// 5. Creates a pseudo constructor.
///
/// # Usage
///
/// ```
/// // #[modtype::use_modtype(constant(_1000000007U64), constructor(F))]
/// #[modtype::use_modtype]
/// type F = modtype::F<1_000_000_007u64>;
///
/// assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
/// ```
///
/// ↓
///
/// ```
/// type F = modtype::F<_1000000007U64>;
///
/// enum _1000000007U64 {}
///
/// impl ::modtype::ConstValue for _1000000007U64 {
///     type Value = u64;
///     const VALUE: u64 = 1_000_000_007u64;
/// }
///
/// #[allow(non_snake_case)]
/// #[inline]
/// fn F(value: u64) -> F {
///     F::new(value)
/// }
///
/// assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
/// ```
///
/// # Attributes
///
/// | Name          | Format                         | Optional                                                |
/// | :------------ | :----------------------------- | :------------------------------------------------------ |
/// | `constant`    | `constant($`[`Ident`]`)`       | Yes (default = `concat!(_, $value, $type_pascal_case)`) |
/// | `constructor` | `constructor($`[`Ident`]`)`    | Yes (default = the type alias)                          |
///
/// [`ConstValue`]: https://docs.rs/modtype/0.7/modtype/trait.ConstValue.html
/// [`Ident`]: https://docs.rs/syn/0.15/syn/struct.Ident.html
#[proc_macro_attribute]
pub fn use_modtype(
    args: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    crate::use_modtype::use_modtype(args, item)
}

/// Derives [`ConstValue`].
///
/// # Attributes
///
/// ## Struct
///
/// | Name                 | Format                                                       | Optional  |
/// | :------------------- | :----------------------------------------------------------- | :-------- |
/// | `const_value`        | `const_value = #`[`LitInt`] where `#`[`LitInt`] has a suffix | No        |
///
/// [`ConstValue`]: https://docs.rs/modtype/0.7/modtype/trait.ConstValue.html
/// [`LitInt`]: https://docs.rs/syn/0.15/syn/struct.LitInt.html
#[proc_macro_derive(ConstValue, attributes(modtype))]
pub fn const_value(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    crate::const_value::const_value(input)
}

/// Derives following traits.
///
/// - [`std::convert::From`]`<`[`u8`]`>`
/// - [`std::convert::From`]`<`[`u16`]`>`
/// - [`std::convert::From`]`<`[`u32`]`>`
/// - [`std::convert::From`]`<`[`u64`]`>`
/// - [`std::convert::From`]`<`[`u128`]`>`
/// - [`std::convert::From`]`<`[`usize`]`>`
/// - [`std::convert::From`]`<`[`i8`]`>`
/// - [`std::convert::From`]`<`[`i16`]`>`
/// - [`std::convert::From`]`<`[`i32`]`>`
/// - [`std::convert::From`]`<`[`i64`]`>`
/// - [`std::convert::From`]`<`[`i128`]`>`
/// - [`std::convert::From`]`<`[`isize`]`>`
/// - [`std::convert::From`]`<`[`f32`]`>`
/// - [`std::convert::From`]`<`[`f64`]`>`
/// - [`std::convert::From`]`<`[`num::bigint::BigUint`]`>`
/// - [`std::convert::From`]`<`[`num::bigint::BigInt`]`>`
/// - [`std::clone::Clone`]
/// - [`std::marker::Copy`]
/// - [`std::default::Default`]
/// - [`std::cmp::PartialEq`]
/// - [`std::cmp::Eq`]
/// - [`std::cmp::PartialOrd`]
/// - [`std::cmp::Ord`]
/// - [`std::fmt::Display`]
/// - [`std::fmt::Debug`]
/// - [`std::str::FromStr`]
/// - [`std::ops::Deref`]
/// - [`std::ops::Neg`]
/// - [`std::ops::Add`]
/// - [`std::ops::AddAssign`]
/// - [`std::ops::Sub`]
/// - [`std::ops::SubAssign`]
/// - [`std::ops::Mul`]
/// - [`std::ops::MulAssign`]
/// - [`std::ops::Div`]
/// - [`std::ops::DivAssign`]
/// - [`std::ops::Rem`]
/// - [`std::ops::RemAssign`]
/// - [`num::traits::Num`]
/// - [`num::traits::Zero`]
/// - [`num::traits::One`]
/// - [`num::traits::FromPrimitive`]
/// - [`num::traits::Inv`]
/// - [`num::traits::CheckedNeg`]
/// - [`num::traits::CheckedAdd`]
/// - [`num::traits::CheckedSub`]
/// - [`num::traits::CheckedMul`]
/// - [`num::traits::CheckedDiv`]
/// - [`num::traits::CheckedRem`]
/// - [`num::traits::Pow`]
///
/// # Attributes
///
/// ## Struct
///
/// | Name                 | Format                                                                   | Optional                          |
/// | :------------------- | :----------------------------------------------------------------------- | :-------------------------------- |
/// | `modulus`            | `modulus = $`[`Lit`] where `$`[`Lit`] is converted/parsed to an [`Expr`] | No                                |
/// | `cartridge`          | `cartridge = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]    | No                                |
/// | `std`                | `std = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]          | Yes (default = `::std`)           |
/// | `num_traits`         | `num_traits = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]   | Yes (default = `::num::traits`)   |
/// | `num_integer`        | `num_integer = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]  | Yes (default = `::num::integer`)  |
/// | `num_bigint`         | `num_bigint = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]   | Yes (default = `::num::bigint`)   |
/// | `num_rational`       | `num_rational = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`] | Yes (default = `::num::rational`) |
/// | `modtype`            | `modtype = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]      | Yes (default = `::modtype`)       |
/// | `non_static_modulus` | `non_static_modulus`                                                     | Yes                               |
///
/// ## Field
///
/// | Name    | Format  | Optional |
/// | :------ | :------ | :------- |
/// | `value` | `value` | No       |
///
/// # Requirements
///
/// - The `#[modtype(value)]` field is a [`UnsignedPrimitive`].
/// - All fields are [`Default`][`std::default::Default`].
/// - All fields are [`Copy`][`std::marker::Copy`].
/// - All fields are [`PartialEq`][`std::cmp::PartialEq`].
/// - All fields are [`Ord`][`std::cmp::Ord`].
///
/// [`std::convert::From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
/// [`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
/// [`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
/// [`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
/// [`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
/// [`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
/// [`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
/// [`i8`]: https://doc.rust-lang.org/nightly/std/primitive.i8.html
/// [`i16`]: https://doc.rust-lang.org/nightly/std/primitive.i16.html
/// [`i32`]: https://doc.rust-lang.org/nightly/std/primitive.i32.html
/// [`i64`]: https://doc.rust-lang.org/nightly/std/primitive.i64.html
/// [`i128`]: https://doc.rust-lang.org/nightly/std/primitive.i128.html
/// [`isize`]: https://doc.rust-lang.org/nightly/std/primitive.isize.html
/// [`f32`]: https://doc.rust-lang.org/nightly/std/primitive.f32.html
/// [`f64`]: https://doc.rust-lang.org/nightly/std/primitive.f64.html
/// [`num::bigint::BigUint`]: https://docs.rs/num-bigint/0.2/num_bigint/struct.BigUint.html
/// [`num::bigint::BigInt`]: https://docs.rs/num-bigint/0.2/num_bigint/struct.BigInt.html
/// [`std::default::Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
/// [`std::clone::Clone`]: https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html
/// [`std::marker::Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`std::cmp::PartialEq`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html
/// [`std::cmp::Eq`]: https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html
/// [`std::cmp::PartialOrd`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html
/// [`std::cmp::Ord`]: https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html
/// [`std::fmt::Display`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html
/// [`std::fmt::Debug`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html
/// [`std::str::FromStr`]: https://doc.rust-lang.org/nightly/core/str/trait.FromStr.html
/// [`std::ops::Deref`]: https://doc.rust-lang.org/nightly/core/ops/deref/trait.Deref.html
/// [`std::ops::Neg`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Neg.html
/// [`std::ops::Add`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Add.html
/// [`std::ops::AddAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.AddAssign.html
/// [`std::ops::Sub`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Sub.html
/// [`std::ops::SubAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.SubAssign.html
/// [`std::ops::Mul`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Mul.html
/// [`std::ops::MulAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.MulAssign.html
/// [`std::ops::Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
/// [`std::ops::DivAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.DivAssign.html
/// [`std::ops::Rem`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Rem.html
/// [`std::ops::RemAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.RemAssign.html
/// [`num::traits::Num`]: https://docs.rs/num-traits/0.2/num_traits/trait.Num.html
/// [`num::traits::Zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html
/// [`num::traits::One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
/// [`num::traits::FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
/// [`num::traits::Inv`]: https://docs.rs/num-traits/0.2/num_traits/ops/inv/trait.Inv.html
/// [`num::traits::CheckedNeg`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedNeg.html
/// [`num::traits::CheckedAdd`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedAdd.html
/// [`num::traits::CheckedSub`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedSub.html
/// [`num::traits::CheckedMul`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedMul.html
/// [`num::traits::CheckedDiv`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedDiv.html
/// [`num::traits::CheckedRem`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedRem.html
/// [`num::traits::Pow`]: https://docs.rs/num-traits/0.2/num_traits/pow/trait.Pow.html
/// [`Ident`]: https://docs.rs/syn/0.15/syn/struct.Ident.html
/// [`Lit`]: https://docs.rs/syn/0.15/syn/enum.Lit.html
/// [`LitStr`]: https://docs.rs/syn/0.15/syn/struct.LitStr.html
/// [`LitInt`]: https://docs.rs/syn/0.15/syn/struct.LitInt.html
/// [`Expr`]: https://docs.rs/syn/0.15/syn/struct.Expr.html
/// [`Path`]: https://docs.rs/syn/0.15/syn/struct.Path.html
/// [`UnsignedPrimitive`]: https://docs.rs/modtype/0.7/modtype/trait.UnsignedPrimitive.html
#[proc_macro_derive(ModType, attributes(modtype))]
pub fn mod_type(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let ctx = try_syn!(Context::try_from(parse_macro_input!(input as DeriveInput)));
    let mut acc = quote!();
    acc.extend(ctx.derive_from());
    acc.extend(ctx.derive_clone());
    acc.extend(ctx.derive_copy());
    acc.extend(ctx.derive_default());
    acc.extend(ctx.derive_partial_eq());
    acc.extend(ctx.derive_eq());
    acc.extend(ctx.derive_partial_ord());
    acc.extend(ctx.derive_ord());
    acc.extend(ctx.derive_display());
    acc.extend(ctx.derive_debug());
    acc.extend(ctx.derive_from_str());
    acc.extend(ctx.derive_deref());
    acc.extend(ctx.derive_neg());
    acc.extend(ctx.derive_add());
    acc.extend(ctx.derive_add_assign());
    acc.extend(ctx.derive_sub());
    acc.extend(ctx.derive_sub_assign());
    acc.extend(ctx.derive_mul());
    acc.extend(ctx.derive_mul_assign());
    acc.extend(ctx.derive_div());
    acc.extend(ctx.derive_div_assign());
    acc.extend(ctx.derive_rem());
    acc.extend(ctx.derive_rem_assign());
    acc.extend(ctx.derive_num());
    acc.extend(ctx.derive_zero());
    acc.extend(ctx.derive_one());
    acc.extend(ctx.derive_from_primitive());
    acc.extend(ctx.derive_inv());
    acc.extend(ctx.derive_checked_neg());
    acc.extend(ctx.derive_checked_add());
    acc.extend(ctx.derive_checked_sub());
    acc.extend(ctx.derive_checked_mul());
    acc.extend(ctx.derive_checked_div());
    acc.extend(ctx.derive_checked_rem());
    acc.extend(ctx.derive_pow());
    acc.into()
}
