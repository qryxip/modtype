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
/// use modtype::use_modtype;
///
/// // #[use_modtype(constant(_1000000007U64), constructor(F))]
/// #[use_modtype]
/// type F = modtype::u64::Z<1_000_000_007u64>;
///
/// assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
/// ```
///
/// ↓
///
/// ```
/// type F = modtype::u64::Z<_1000000007U64>;
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
///     <F as ::std::convert::From<u64>>::from(value)
/// }
///
/// assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
/// ```
///
/// # Attributes
///
/// | Name          | Format                         | Optional                                      |
/// | :------------ | :----------------------------- | :-------------------------------------------- |
/// | `constant`    | `constant($`[`Ident`]`)`       | Yes (default = `concat!(_, $type_uppercase)`) |
/// | `constructor` | `constructor($`[`Ident`]`)`    | Yes (default = the type alias)                |
///
/// [`ConstValue`]: https://docs.rs/modtype/0.5/modtype/trait.ConstValue.html
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
/// [`ConstValue`]: https://docs.rs/modtype/0.5/modtype/trait.ConstValue.html
/// [`LitInt`]: https://docs.rs/syn/0.15/syn/struct.LitInt.html
#[proc_macro_derive(ConstValue, attributes(modtype))]
pub fn const_value(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    crate::const_value::const_value(input)
}

/// Implement `new` with `#implementation::new`.
#[proc_macro_derive(new, attributes(modtype))]
pub fn new(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_new)
}

/// Implement `new_unchecked`.
#[proc_macro_derive(new_unchecked, attributes(modtype))]
pub fn new_unchecked(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_new_unchecked)
}

/// Derives `get` with `#implementation::get`.
#[proc_macro_derive(get, attributes(modtype))]
pub fn get(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_get)
}

/// Derives [`From`]`<{#InnerValue, `[`BigUint`]`, `[`BigInt`]`}>` with `#implementation::{new, from_biguint, from_bigint}`.
///
/// # Requirements
///
/// - The fields are [`Default`] except `#InnerValue`.
///
/// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
/// [`BigUint`]: https://docs.rs/num-bigint/0.2/num_bigint/struct.BigUint.html
/// [`BigInt`]: https://docs.rs/num-bigint/0.2/num_bigint/struct.BigInt.html
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
#[proc_macro_derive(From, attributes(modtype))]
pub fn from(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_from)
}

/// Derives [`From`]`<Self> for #InnerValue`.
///
/// # Requirements
///
/// - `#InnerValue` is not a type parameter.
///
/// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
#[proc_macro_derive(Into, attributes(modtype))]
pub fn into(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_into)
}

/// Derives [`Clone`] without extra trait bound.
///
/// # Requirements
///
/// - All fields are [`Copy`].
///
/// [`Clone`]: https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(ModtypeClone, attributes(modtype))]
pub fn clone(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_clone)
}

/// Derives [`Copy`] without extra trait bound.
///
/// # Requirements
///
/// - `Self: `[`Clone`]. (required by [`Copy`] itself)
///
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`Clone`]: https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html
#[proc_macro_derive(ModtypeCopy, attributes(modtype))]
pub fn copy(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_copy)
}

/// Derives [`Default`] without extra trait bound.
///
/// # Requirements
///
/// - All fields are [`Default`].
///
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
#[proc_macro_derive(ModtypeDefault, attributes(modtype))]
pub fn default(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_default)
}

/// Derives [`PartialEq`] without extra trait bound.
///
/// # Requirements
///
/// - All fields are [`PartialEq`].
///
/// [`PartialEq`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html
#[proc_macro_derive(ModtypePartialEq, attributes(modtype))]
pub fn partial_eq(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_partial_eq)
}

/// Derives [`Eq`] without extra trait bound.
///
/// # Requirements
///
/// - `Self: `[`PartialEq`]. (required by [`Eq`] itself)
///
/// [`Eq`]: https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html
/// [`PartialEq`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html
#[proc_macro_derive(ModtypeEq, attributes(modtype))]
pub fn eq(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_eq)
}

/// Derives [`PartialOrd`] without extra trait bound.
///
/// # Requirements
///
/// - `Self: `[`Ord`].
/// - All fields are [`Ord`].
///
/// [`PartialOrd`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html
/// [`Ord`]: https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html
#[proc_macro_derive(ModtypePartialOrd, attributes(modtype))]
pub fn partial_ord(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_partial_ord)
}

/// Derives [`Ord`] without extra trait bound.
///
/// # Requirements
///
/// - `Self: `[`PartialOrd`]. (required by [`Ord`] itself)
/// - All fields are [`Ord`].
///
/// [`Ord`]: https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html
/// [`PartialOrd`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html
#[proc_macro_derive(ModtypeOrd, attributes(modtype))]
pub fn ord(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_ord)
}

/// Derives [`Display`] with `#implementation::fmt_display`.
///
/// [`Display`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html
#[proc_macro_derive(Display, attributes(modtype))]
pub fn display(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_display)
}

/// Derives [`Debug`] with `#implementation::fmt_debug`.
///
/// [`Debug`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html
#[proc_macro_derive(ModtypeDebug, attributes(modtype))]
pub fn debug(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_debug)
}

/// Derives [`FromStr`] with `#implementation::from_str`.
///
/// [`FromStr`]: https://doc.rust-lang.org/nightly/core/str/trait.FromStr.html
#[proc_macro_derive(FromStr, attributes(modtype))]
pub fn from_str(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_from_str)
}

/// Derives [`Deref`]`<Target = #InnerValue>`.
///
/// [`Deref`]: https://doc.rust-lang.org/nightly/core/ops/deref/trait.Deref.html
#[proc_macro_derive(Deref, attributes(modtype))]
pub fn deref(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_deref)
}

/// Derives [`Neg`] with `#implementation::neg`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
///
/// [`Neg`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Neg.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(Neg, attributes(modtype))]
pub fn neg(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_neg)
}

/// Derives [`Add`] with `#implementation::add`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
///
/// [`Add`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Add.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(Add, attributes(modtype))]
pub fn add(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_add)
}

/// Derives [`AddAssign`] with `#implementation::add`.
///
/// # Requirements
///
/// - `Self: Copy`.
///
/// [`AddAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.AddAssign.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(AddAssign, attributes(modtype))]
pub fn add_assign(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_add_assign)
}

/// Derives [`Sub`] with `#implementation::sub`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
///
/// [`Sub`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Sub.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(Sub, attributes(modtype))]
pub fn sub(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_sub)
}

/// Derives [`SubAssign`] with `#implementation::sub`.
///
/// # Requirements
///
/// - `Self: `[`Copy`]
///
/// [`SubAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.SubAssign.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(SubAssign, attributes(modtype))]
pub fn sub_assign(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_sub_assign)
}

/// Derives [`Mul`] with `#implementation::mul`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
///
/// [`Mul`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Mul.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(Mul, attributes(modtype))]
pub fn mul(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_mul)
}

/// Derives [`MulAssign`] with `#implementation::mul`.
///
/// # Requirements
///
/// - `Self: `[`Mul`]`<Self, Output = Self>`.
/// - `Self: `[`Copy`].
///
/// [`MulAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.MulAssign.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(MulAssign, attributes(modtype))]
pub fn mul_assign(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_mul_assign)
}

/// Derives [`Div`] with `#implementation::div`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
///
/// [`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(Div, attributes(modtype))]
pub fn div(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_div)
}

/// Derives [`DivAssign`] with `#implementation::div`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
///
/// [`DivAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.DivAssign.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(DivAssign, attributes(modtype))]
pub fn div_assign(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_div_assign)
}

/// Derives [`Rem`] with `#implementation::rem`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
///
/// [`Rem`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Rem.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(Rem, attributes(modtype))]
pub fn rem(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_rem)
}

/// Derives [`RemAssign`] with `#implementation::rem`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
///
/// [`RemAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.RemAssign.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(RemAssign, attributes(modtype))]
pub fn rem_assign(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_rem_assign)
}

/// Derives [`Num`] with `#implementation::from_str_radix`.
///
/// # Requirements
///
/// - The fields are [`Default`] except `#InnerValue`.
///
/// [`Num`]: https://docs.rs/num-traits/0.2/num_traits/trait.Num.html
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
#[proc_macro_derive(Num, attributes(modtype))]
pub fn num(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_num)
}

/// Derives [`Unsigned`].
///
/// # Requirements
///
/// - `Self: `[`Num`]. (required by [`Unsigned`] itself)
///
/// [`Unsigned`]: https://docs.rs/num-traits/0.2/num_traits/sign/trait.Unsigned.html
/// [`Num`]: https://docs.rs/num-traits/0.2/num_traits/trait.Num.html
#[proc_macro_derive(Unsigned, attributes(modtype))]
pub fn unsigned(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_unsigned)
}

/// Derives [`Bounded`] with `#implementation::{min_value, max_value}`.
///
/// [`Bounded`]: https://docs.rs/num-traits/0.2/num_traits/bounds/trait.Bounded.html
#[proc_macro_derive(Bounded, attributes(modtype))]
pub fn bounded(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_bounded)
}

/// Derives [`Zero`] with `#implementation::{zero, is_zero}`.
///
/// # Requirements
///
/// - The fields are [`Default`] except `#InnerValue`.
/// - `Self: `[`Add`]`<Self, Output = Self>`. (required by [`Zero`] itself)
///
/// [`Zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
/// [`Add`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Add.html
#[proc_macro_derive(Zero, attributes(modtype))]
pub fn zero(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_zero)
}

/// Derives [`One`] with `#implementation::{one, is_one}`.
///
/// # Requirements
///
/// - The fields are [`Default`] except `#InnerValue`.
/// - `Self: `[`Mul`]`<Self, Output = Self>`. (required by [`One`] itself)
///
/// [`One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
/// [`Mul`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Mul.html
#[proc_macro_derive(One, attributes(modtype))]
pub fn one(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_one)
}

/// Derives [`FromPrimitive`] with `#implementation::from_{..}`.
///
/// # Requirements
///
/// - The fields are [`Default`] except `#InnerValue`.
///
/// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
#[proc_macro_derive(FromPrimitive, attributes(modtype))]
pub fn from_primitive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_from_primitive)
}

/// Derives [`Inv`] with `#implementation::inv`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
///
/// [`Inv`]: https://docs.rs/num-traits/0.2/num_traits/ops/inv/trait.Inv.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(Inv, attributes(modtype))]
pub fn inv(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_inv)
}

/// Derives [`CheckedNeg`].
///
/// # Requirements
///
/// - `Self: `[`Copy`].
/// - `Self: `[`Neg`]`<Output = Self>`.
///
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`Neg`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Neg.html
/// [`CheckedNeg`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedNeg.html
#[proc_macro_derive(CheckedNeg, attributes(modtype))]
pub fn checked_neg(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_checked_neg)
}

/// Derives [`CheckedAdd`] with `#implementation::checked_add`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
/// - `Self: `[`Add`]`<Self, Output = Self>`. (required by [`CheckedAdd`] itself)
///
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`Add`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Add.html
/// [`CheckedAdd`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedAdd.html
#[proc_macro_derive(CheckedAdd, attributes(modtype))]
pub fn checked_add(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_checked_add)
}

/// Derives `CheckedSub` with `#implementation::checked_sub`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
/// - `Self: `[`Sub`]`<Self, Output = Self>`. (required by [`CheckedSub`] itself)
///
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`Sub`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Sub.html
/// [`CheckedAdd`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedAdd.html
#[proc_macro_derive(CheckedSub, attributes(modtype))]
pub fn checked_sub(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_checked_sub)
}

/// Derives [`CheckedMul`] with `#implementation::checked_mul`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
/// - `Self: `[`Mul`]`<Self, Output = Self>`. (required by [`CheckedMul`] itself)
///
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`Mul`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Mul.html
/// [`CheckedMul`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedMul.html
#[proc_macro_derive(CheckedMul, attributes(modtype))]
pub fn checked_mul(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_checked_mul)
}

/// Derives [`CheckedDiv`] with `#implementation::checked_div`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
/// - `Self: `[`Div`]`<Self, Output = Self>`. (required by [`CheckedDiv`] itself)
///
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
/// [`CheckedDiv`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedDiv.html
#[proc_macro_derive(CheckedDiv, attributes(modtype))]
pub fn checked_div(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_checked_div)
}

/// Derives [`CheckedRem`] with `#implementation::checked_rem`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
/// - `Self: `[`Rem`]`<Self, Output = Self>`. (required by [`CheckedRem`] itself)
///
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`Rem`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Rem.html
/// [`CheckedRem`]: https://docs.rs/num-traits/0.2/num_traits/ops/checked/trait.CheckedRem.html
#[proc_macro_derive(CheckedRem, attributes(modtype))]
pub fn checked_rem(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_checked_rem)
}

/// Derives [`Pow`] with `#implementation::{pow_unsigned, pow_signed}`.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
///
/// [`Pow`]: https://docs.rs/num-traits/0.2/num_traits/pow/trait.Pow.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(Pow, attributes(modtype))]
pub fn pow(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_pow)
}

fn derive(
    input: proc_macro::TokenStream,
    derive: fn(&Context) -> proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let ctx = try_syn!(Context::try_from(parse_macro_input!(input as DeriveInput)));
    derive(&ctx)
}
