# modtype

[![Build Status](https://img.shields.io/travis/com/qryxip/modtype/master.svg?label=windows%20%26%20macos%20%26%20linux)](https://travis-ci.com/qryxip/modtype)
[![codecov](https://codecov.io/gh/qryxip/modtype/branch/master/graph/badge.svg)](https://codecov.io/gh/qryxip/modtype)
[![Crates.io](https://img.shields.io/crates/v/modtype.svg)](https://crates.io/crates/modtype)

This crate provides:
- Macros that implement modular arithmetic integer types
- Preset types
    - `modtype::u64::F`
    - `modtype::u64::Z`
    - `modtype::u64::thread_local::F`

## Usage

```rust
use modtype::ConstValue;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, ConstValue)]
#[modtype(const_value = 1_000_000_007u64)]
enum M {}

type F = modtype::u64::F<M>;

#[allow(non_snake_case)]
fn F(value: u64) -> F {
    F::new(value)
}

assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
```

To use a customized type, copy the following code via clipboard and edit it.

```rust
#[allow(non_snake_case)]
fn F(value: u64) -> F {
    F::from(value)
}

#[derive(
    modtype::new,
    modtype::get,
    Default,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    modtype::From,
    modtype::Into,
    modtype::Display,
    modtype::Debug,
    modtype::FromStr,
    modtype::Deref,
    modtype::Neg,
    modtype::Add,
    modtype::AddAssign,
    modtype::Sub,
    modtype::SubAssign,
    modtype::Mul,
    modtype::MulAssign,
    modtype::Div,
    modtype::DivAssign,
    modtype::Rem,
    modtype::RemAssign,
    modtype::Num,
    modtype::Unsigned,
    modtype::Bounded,
    modtype::Zero,
    modtype::One,
    modtype::FromPrimitive,
    modtype::Inv,
    modtype::CheckedNeg,
    modtype::CheckedAdd,
    modtype::CheckedSub,
    modtype::CheckedMul,
    modtype::CheckedDiv,
    modtype::CheckedRem,
    modtype::Pow,
    modtype::Integer,
)]
#[modtype(
    modulus = "1_000_000_007",
    std = "std",
    num_traits = "num::traits",
    num_integer = "num::integer",
    num_bigint = "num::bigint",
    from(InnerValue, BigUint, BigInt),
    debug(SingleTuple),
    neg(for_ref = true),
    add(for_ref = true),
    add_assign(for_ref = true),
    sub(for_ref = true),
    sub_assign(for_ref = true),
    mul(for_ref = true),
    mul_assign(for_ref = true),
    div(for_ref = true),
    div_assign(for_ref = true),
    rem(for_ref = true),
    rem_assign(for_ref = true),
    inv(for_ref = true),
    pow(for_ref = true)
)]
struct F {
    #[modtype(value)]
    __value: u64,
}
```

## Requirements

- The inner value is [`u8`], [`u16`], [`u32`], [`u64`], [`u128`], or [`usize`].
- The inner value and the modulus are of a same type.
- The modulus is immutable.
- The inner value is always smaller than the modulus.
    - If the modular arithmetic type implements [`One`], The modulus is larger than `1`.
- If the modular arithmetic type implements [`Div`], the modulus is a prime.

## Attributes

### Struct

| Name                 | Format                                                                                                   | Optional                         |
| :------------------- | :------------------------------------------------------------------------------------------------------- | :------------------------------- |
| `modulus`            | `modulus = $`[`Lit`] where `$`[`Lit`] is converted/parsed to an [`Expr`]                                 | No                               |
| `std`                | `std = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]                                          | Yes (default = `::std`)          |
| `num_traits`         | `num_traits = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]                                   | Yes (default = `::num::traits`)  |
| `num_integer`        | `num_integer = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]                                  | Yes (default = `::num::integer`) |
| `num_bigint`         | `num_bigint = $`[`LitStr`] where `$`[`LitStr`] is parsed to a [`Path`]                                   | Yes (default = `::num::bigint`)  |
| `from`               | `from($`[`Ident`]` $(, $`[`Ident`]s`) $(,)?)` where all [`Ident`]s ∈ {`InnerValue`, `BigUint`, `BigInt`} | Yes (default = all)              |
| `debug`              | `debug(SingleTuple)` or `debug(Transparent)`                                                             | Yes (default = `SingleTuple`)    |
| `neg`                | `neg(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
| `add`                | `add(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
| `add_assign`         | `add_assign(for_ref = $`[`LitBool`]`)`                                                                   | Yes (default = `true`)           |
| `sub`                | `sub(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
| `sub_assign`         | `sub_assign(for_ref = $`[`LitBool`]`)`                                                                   | Yes (default = `true`)           |
| `mul`                | `mul(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
| `mul_assign`         | `mul_assign(for_ref = $`[`LitBool`]`)`                                                                   | Yes (default = `true`)           |
| `div`                | `div(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
| `div_assign`         | `div_assign(for_ref = $`[`LitBool`]`)`                                                                   | Yes (default = `true`)           |
| `rem`                | `rem(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
| `rem_assign`         | `rem_assign(for_ref = $`[`LitBool`]`)`                                                                   | Yes (default = `true`)           |
| `inv`                | `inv(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |
| `pow`                | `pow(for_ref = $`[`LitBool`]`)`                                                                          | Yes (default = `true`)           |

### Field

| Name                 | Format  | Optional |
| :------------------- | :------ | :------- |
| `value`              | `value` | No       |

### [`ConstValue`]

#### Struct

| Name                 | Format                                                       | Optional  |
| :------------------- | :----------------------------------------------------------- | :-------- |
| `const_value`        | `const_value = $`[`LitInt`] where `$`[`LitInt`] has a suffix | No        |

[`u8`]: https://doc.rust-lang.org/nightly/std/primitive.u8.html
[`u16`]: https://doc.rust-lang.org/nightly/std/primitive.u16.html
[`u32`]: https://doc.rust-lang.org/nightly/std/primitive.u32.html
[`u64`]: https://doc.rust-lang.org/nightly/std/primitive.u64.html
[`u128`]: https://doc.rust-lang.org/nightly/std/primitive.u128.html
[`usize`]: https://doc.rust-lang.org/nightly/std/primitive.usize.html
[`Div`]: https://doc.rust-lang.org/nightly/core/ops/arith/trait.Div.html
[`One`]: https://docs.rs/num-traits/0.2/num_traits/identities/trait.One.html
[`Ident`]: https://docs.rs/syn/0.15/syn/struct.Ident.html
[`Lit`]: https://docs.rs/syn/0.15/syn/enum.Lit.html
[`LitStr`]: https://docs.rs/syn/0.15/syn/struct.LitStr.html
[`LitInt`]: https://docs.rs/syn/0.15/syn/struct.LitInt.html
[`LitBool`]: https://docs.rs/syn/0.15/syn/struct.LitBool.html
[`Expr`]: https://docs.rs/syn/0.15/syn/struct.Expr.html
[`Path`]: https://docs.rs/syn/0.15/syn/struct.Path.html
[`ConstValue`]: https://docs.rs/modtype_derive/0.3/modtype_derive/derive.ConstValue.html
