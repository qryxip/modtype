# modtype

[![Build Status](https://img.shields.io/travis/qryxip/modtype.svg?branch=master&label=windows%20%26%20macos%20%26%20linux)](https://travis-ci.com/qryxip/modtype)
[![codecov](https://codecov.io/gh/qryxip/modtype/branch/master/graph/badge.svg)](https://codecov.io/gh/qryxip/modtype)
[![Crates.io](https://img.shields.io/crates/v/modtype.svg)](https://crates.io/crates/modtype)

This crate provides:
- Macros that implement modular arithmetic integer types
- Preset types (`modtype::preset::u64{, ::mod1000000007}::{F, Z}`)

## Usage

```rust
type F = F_<Const17U32>;

#[derive(
    Default,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    modtype::From,
    modtype::Into,
    modtype::FromStr,
    modtype::Display,
    modtype::Debug,
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
    modtype::Zero,
    modtype::One,
    modtype::Num,
    modtype::Bounded,
    modtype::CheckedAdd,
    modtype::CheckedSub,
    modtype::CheckedMul,
    modtype::CheckedDiv,
    modtype::CheckedRem,
    modtype::CheckedNeg,
    modtype::Inv,
    modtype::Unsigned,
    modtype::FromPrimitive,
    modtype::ToPrimitive,
    modtype::Pow_u8,
    modtype::Pow_u16,
    modtype::Pow_u32,
    modtype::Pow_usize,
    modtype::Integer,
    modtype::ToBigInt,
    modtype::ToBigUint,
    modtype::new,
    modtype::get,
)]
#[modtype(
    modulus = "M::VALUE",
    std = "std",
    num_traits = "num::traits",
    num_integer = "num::integer",
    num_bigint = "num::bigint",
    moving_ops_for_ref
)]
struct F_<M: ConstValue<Value = u32>> {
    #[modtype(value)]
    __value: u32,
    phantom: PhantomData<fn() -> M>,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, ConstValue)]
#[modtype(const_value = 17u32)]
enum Const17U32 {}
```

```rust
use modtype::preset::u64::mod1000000007::{F, Z};
```

## Attributes

### Struct

| Name                 | Format                                                         | Optional                         |
| :------------------- | :------------------------------------------------------------- | -------------------------------- |
| `modulus`            | `modulus = #Lit` where `#Lit` is converted/parsed to an `Expr` | No                               |
| `std`                | `std = #LitStr` where `#LitStr` is parsed to a `Path`          | Yes (default = `::std`)          |
| `num_traits`         | `num_traits = #LitStr` where `#LitStr` is parsed to a `Path`   | Yes (default = `::num::traits`)  |
| `num_integer`        | `num_integer = #LitStr` where `#LitStr` is parsed to a `Path`  | Yes (default = `::num::integer`) |
| `num_bigint`         | `num_bigint = #LitStr` where `#LitStr` is parsed to a `Path`   | Yes (default = `::num::bigint`)  |
| `moving_ops_for_ref` | `moving_ops_for_ref`                                           | Yes                              |

### Field

| Name                 | Format  | Optional |
| :------------------- | :------ | -------- |
| `value`              | `value` | No       |


### `ConstValue`

| Name                 | Format                                               | Optional  |
| :------------------- | :----------------------------------------------------| --------- |
| `const_value`        | `const_value = #LitInt` where `#LitInt` has a suffix | No        |
