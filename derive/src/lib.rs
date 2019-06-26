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
/// # Usage
///
/// ```ignore
/// use modtype::use_modtype;
///
/// // #[use_modtype(constant(_1000000007U64), constructor(F))]
/// #[use_modtype]
/// type F = modtype::u64::F<1_000_000_007u64>;
///
/// assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
/// ```
///
/// ↓
///
/// ```ignore
/// type F = modtype::u64::F<_1000000007u64>;
///
/// #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
/// enum _1000000007u64 {}
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
/// [`ConstValue`]: https://docs.rs/modtype/0.3/modtype/trait.ConstValue.html
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
/// [`ConstValue`]: https://docs.rs/modtype/0.3/modtype/trait.ConstValue.html
/// [`LitInt`]: https://docs.rs/syn/0.15/syn/struct.LitInt.html
#[proc_macro_derive(ConstValue, attributes(modtype))]
pub fn const_value(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    crate::const_value::const_value(input)
}

/// Implement `Self::new: fn(#InnerValue) -> Self`.
///
/// # Requirements
///
/// - `Self: `[`From`]`<#InnerValue>`.
///
/// # Generated Code
///
/// ```ignore
/// impl #Self {
///     /// Constructs a new `#Self`.
///     #[inline]
///     #vis fn new(value: #InnerValue) -> Self {
///         <Self as #std::convert::From<#InnerValue>>(value)
///     }
/// }
/// ```
///
/// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
#[proc_macro_derive(new, attributes(modtype))]
pub fn new(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_new)
}

/// Derives `Self::get: fn(Self) -> #InnerValue`.
///
/// # Requirements
///
/// Nothing.
///
/// # Generated Code
///
/// ```ignore
/// impl #Self {
///     /// Gets the inner value.
///     #[inline]
///     #vis fn get(self) -> #InnerValue {
///         self.#inner_value
///     }
/// }
/// ```
#[proc_macro_derive(get, attributes(modtype))]
pub fn get(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_get)
}

/// Derives [`From`]`<#InnerValue>`, [`From`]`<`[`BigUint`]`>`, and [`From`]`<`[`BigInt`]`>`.
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

/// Derives [`Display`].
///
/// # Requirements
///
/// - `#InnerValue: `[`Display`].
///
/// [`Display`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html
#[proc_macro_derive(Display, attributes(modtype))]
pub fn display(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_display)
}

/// Derives [`Debug`].
///
/// # Requirements
///
/// - `#InnerValue: `[`Debug`].
///
/// [`Debug`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html
#[proc_macro_derive(ModtypeDebug, attributes(modtype))]
pub fn debug(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_debug)
}

/// Derives [`FromStr`]`<Err = #InnerValue::Err>`.
///
/// # Requirements
///
/// - `Self: `[`From`]`<#InnerValue>`.
///
/// [`FromStr`]: https://doc.rust-lang.org/nightly/core/str/trait.FromStr.html
/// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
#[proc_macro_derive(FromStr, attributes(modtype))]
pub fn from_str(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_from_str)
}

/// Derives [`Deref`]`<Target = #InnerValue>`.
///
/// # Requirements
///
/// Nothing.
///
/// [`Deref`]: https://doc.rust-lang.org/nightly/core/ops/deref/trait.Deref.html
#[proc_macro_derive(Deref, attributes(modtype))]
pub fn deref(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_deref)
}

/// Derives [`Neg`].
///
/// # Requirements
///
/// - `Self: `[`Add`]`<Self, Output = Self>`
/// - `Self: `[`Sub`]`<Self, Output = Self>`
/// - The fields are [`Default`] except `#InnerValue`.
///
/// [`Neg`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Neg.html
/// [`Add`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Add.html
/// [`Sub`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Sub.html
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
#[proc_macro_derive(Neg, attributes(modtype))]
pub fn neg(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_neg)
}

/// Derives [`Add`].
///
/// # Requirements
///
/// - The fields are [`Default`] except `#InnerValue`.
///
/// [`Add`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Add.html
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
#[proc_macro_derive(Add, attributes(modtype))]
pub fn add(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_add)
}

/// Derives [`AddAssign`].
///
/// # Requirements
///
/// - `Self: `[`Add`]`<Self, Output = Self>`.
/// - `Self: Copy`.
///
/// [`AddAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.AddAssign.html
/// [`Add`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Add.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(AddAssign, attributes(modtype))]
pub fn add_assign(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_add_assign)
}

/// Derives [`Sub`].
///
/// # Requirements
///
/// - The fields are [`Default`] except `#InnerValue`.
///
/// [`Sub`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Sub.html
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
#[proc_macro_derive(Sub, attributes(modtype))]
pub fn sub(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_sub)
}

/// Derives [`SubAssign`].
///
/// # Requirements
///
/// - `Self: `[`Sub`]`<Self, Output = Self>`
/// - `Self: `[`Copy`]
///
/// [`SubAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.SubAssign.html
/// [`Sub`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Sub.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(SubAssign, attributes(modtype))]
pub fn sub_assign(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_sub_assign)
}

/// Derives [`Mul`].
///
/// # Requirements
///
/// - The fields are [`Default`] except `#InnerValue`.
///
/// [`Mul`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Mul.html
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
#[proc_macro_derive(Mul, attributes(modtype))]
pub fn mul(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_mul)
}

/// Derives [`MulAssign`].
///
/// # Requirements
///
/// - `Self: `[`Mul`]`<Self, Output = Self>`.
/// - `Self: `[`Copy`].
///
/// [`MulAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.MulAssign.html
/// [`Mul`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Mul.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(MulAssign, attributes(modtype))]
pub fn mul_assign(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_mul_assign)
}

/// Derives [`Div`].
///
/// # Requirements
///
/// - `<#InnerValue as `[`ToPrimitive`]`>::`[`to_i128`] always return [`Some`] for values in [0, `#modulus`).
/// - `#modulus` is a prime.
/// - The fields are [`Default`] except `#InnerValue`.
///
/// [`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
/// [`ToPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.ToPrimitive.html
/// [`to_i128`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.ToPrimitive.html#method.to_i128
/// [`Some`]: https://doc.rust-lang.org/nightly/core/option/enum.Option.html#variant.Some
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
#[proc_macro_derive(Div, attributes(modtype))]
pub fn div(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_div)
}

/// Derives [`DivAssign`].
///
/// # Requirements
///
/// - `Self: `[`Div`]`<Self, Output = Self>`.
/// - `Self: `[`Copy`].
///
/// [`DivAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.DivAssign.html
/// [`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(DivAssign, attributes(modtype))]
pub fn div_assign(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_div_assign)
}

/// Derives [`Rem`].
///
/// # Requirements
///
/// - `Self: `[`Div`]`<Self, Output = Self>`.
/// - `Self: `[`Zero`].
///
/// [`Rem`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Rem.html
/// [`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
/// [`Zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html
#[proc_macro_derive(Rem, attributes(modtype))]
pub fn rem(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_rem)
}

/// Derives [`RemAssign`].
///
/// # Requirements
///
/// - `Self: `[`Rem`]`<Self, Output = Self>`.
/// - `Self: `[`Copy`].
///
/// [`RemAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.RemAssign.html
/// [`Rem`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Rem.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
#[proc_macro_derive(RemAssign, attributes(modtype))]
pub fn rem_assign(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_rem_assign)
}

/// Derives [`Num`].
///
/// # Requirements
///
/// - `Self: `[`From`]`<#InnerValue>`.
/// - `Self: `[`Zero`]. (required by [`Num`] itself)
/// - `Self: `[`One`]. (required by [`Num`] itself)
/// - `Self: `[`NumOps`]`<Self, Self>`. (required by [`Num`] itself)
/// - `Self: `[`PartialEq`]`<Self>`. (required by [`Num`] itself)
///
/// [`Num`]: https://docs.rs/num-traits/0.2/num_traits/trait.Num.html
/// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
/// [`Zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html
/// [`One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
/// [`NumOps`]: https://docs.rs/num-traits/0.2/num_traits/trait.NumOps.html
/// [`PartialEq`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html
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

/// Derives [`Bounded`].
///
/// # Requirements
///
/// - `Self: `[`From`]`<#InnerValue>`.
///
/// [`Bounded`]: https://docs.rs/num-traits/0.2/num_traits/bounds/trait.Bounded.html
/// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
#[proc_macro_derive(Bounded, attributes(modtype))]
pub fn bounded(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_bounded)
}

/// Derives [`Zero`].
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

/// Derives [`One`].
///
/// # Requirements
///
/// - The fields are [`Default`] except `#InnerValue`.
/// - `Self: `[`Mul`]`<Self, Output = Self>`. (required by [`One`] itself)
/// - `Self: `[`PartialEq`]`<Self>`. (required by `One::is_one`)
///
/// [`One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
/// [`Default`]: https://doc.rust-lang.org/nightly/core/default/trait.Default.html
/// [`Mul`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Mul.html
/// [`PartialEq`]: https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html
#[proc_macro_derive(One, attributes(modtype))]
pub fn one(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_one)
}

/// Derives [`FromPrimitive`].
///
/// # Requirements
///
/// - `Self: `[`From`]`<#InnerValue>`.
///
/// [`FromPrimitive`]: https://docs.rs/num-traits/0.2/num_traits/cast/trait.FromPrimitive.html
/// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
#[proc_macro_derive(FromPrimitive, attributes(modtype))]
pub fn from_primitive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_from_primitive)
}

/// Derives [`Inv`].
///
/// # Requirements
///
/// - `Self: `[`One`].
/// - `Self: `[`Div`]`<Self, Output = Self>`.
///
/// [`Inv`]: https://docs.rs/num-traits/0.2/num_traits/ops/inv/trait.Inv.html
/// [`One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
/// [`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
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

/// Derives [`CheckedAdd`].
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

/// Derives `CheckedSub`.
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

/// Derives [`CheckedMul`].
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

/// Derives [`CheckedDiv`].
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

/// Derives [`CheckedRem`].
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

/// Derives [`Pow`] for primitive integer types.
///
/// # Requirements
///
/// - `Self: `[`Copy`].
/// - `Self: `[`MulAssign`]`<Self>`.
/// - `Self: `[`Inv`]`<Self>`.
/// - `#modulus * #modulus` does not overflow.
///
/// # Generated Code
///
/// ```ignore
/// // part
///
/// impl ::num::traits::Pow<u128> for F {
///     type Output = F;
///
///     #[inline]
///     fn pow(self, exp: u128) -> F {
///         fn static_assert_copy<T: ::std::marker::Copy>() {}
///         static_assert_copy::<F>();
///
///         let mut base = self;
///         let mut exp = exp;
///         let mut acc = self;
///         acc.__value = <u32 as ::num::traits::One>::one();
///
///         while exp > 0 {
///             if (exp & 0x1) == 0x1 {
///                 acc *= base;
///             }
///             exp /= 2;
///             base *= base;
///         }
///         acc
///     }
/// }
///
/// impl ::num::traits::Pow<i128> for F {
///     type Output = F;
///
///     #[inline]
///     fn pow(self, exp: i128) -> F {
///         fn static_assert_copy<T: ::std::marker::Copy>() {}
///         static_assert_copy::<F>();
///
///         let mut base = self;
///         let mut exp = exp;
///         let mut acc = self;
///         acc.__value = <u32 as ::num::traits::One>::one();
///
///         let neg = exp < 0;
///         if neg {
///             exp = -exp;
///         }
///
///         while exp > 0 {
///             if (exp & 0x1) == 0x1 {
///                 acc *= base;
///             }
///             exp /= 2;
///             base *= base;
///         }
///
///         if neg {
///             acc = <F as ::num::traits::Inv>::inv(acc);
///         }
///
///         acc
///     }
/// }
/// ```
///
/// [`Pow`]: https://docs.rs/num-traits/0.2/num_traits/pow/trait.Pow.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`MulAssign`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.MulAssign.html
/// [`Inv`]: https://docs.rs/num-traits/0.2/num_traits/ops/inv/trait.Inv.html
#[proc_macro_derive(Pow, attributes(modtype))]
pub fn pow(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_pow)
}

/// Derives [`Integer`].
///
/// # Requirements
///
/// - `Self: `[`From`]`<#InnerValue>`.
/// - `Self: `[`Copy`].
/// - `Self: `[`Zero`].
/// - `Self: `[`Ord`]. (required by [`Integer`] itself)
/// - `Self: `[`Num`]. (required by [`Integer`] itself)
///
/// [`Integer`]: https://docs.rs/num-integer/0.1/num_integer/trait.Integer.html
/// [`From`]: https://doc.rust-lang.org/nightly/core/convert/trait.From.html
/// [`Copy`]: https://doc.rust-lang.org/nightly/core/marker/trait.Copy.html
/// [`Zero`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.Zero.html
/// [`Ord`]: https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html
/// [`Num`]: https://docs.rs/num-traits/0.2/num_traits/trait.Num.html
#[proc_macro_derive(Integer, attributes(modtype))]
pub fn integer(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    derive(input, Context::derive_integer)
}

fn derive(
    input: proc_macro::TokenStream,
    derive: fn(&Context) -> proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let ctx = try_syn!(Context::try_from(parse_macro_input!(input as DeriveInput)));
    derive(&ctx)
}
