# modtype

[![Build Status](https://img.shields.io/travis/com/qryxip/modtype/master.svg?label=windows%20%26%20macos%20%26%20linux)](https://travis-ci.com/qryxip/modtype)
[![codecov](https://codecov.io/gh/qryxip/modtype/branch/master/graph/badge.svg)](https://codecov.io/gh/qryxip/modtype)
[![Crates.io](https://img.shields.io/crates/v/modtype.svg)](https://crates.io/crates/modtype)

This crate provides modular arithmetic integer types.

## Usage

### [`modtype::ModType`]

```
#[modtype::use_modtype]
type F = modtype::F<1_000_000_007u64>;

assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
```

### [`modtype::thread_local::ModType`]

```
#[allow(non_snake_case)]
modtype::thread_local::F::with(1_000_000_007u64, |F| {
    assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
});
```

### [`modtype::non_static::ModType`]

```
#[allow(non_snake_case)]
let F = modtype::non_static::F::factory(1_000_000_007u64);

assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
```

## Customization

`ModType`s can be customized via [`modtype::Cartridge`].

### [`modtype::cartridges::Multiplicative`]

```
use num::CheckedDiv as _;

#[modtype::use_modtype]
type Z = modtype::ModType<modtype::cartridges::Multiplicative<u32>, 57u32>;

assert_eq!(Z(56) * Z(56), Z(1));
assert_eq!(Z(1).checked_div(&Z(13)), Some(Z(22))); // 13・22 ≡ 1 (mod 57)
```

### [`modtype::cartridges::Additive`]

```
use num::CheckedAdd as _;

#[modtype::use_modtype]
type Z = modtype::ModType<modtype::cartridges::Additive<u64>, 1_000_000_007u64>;

let mut x = Z(1_000_000_006);

x += Z(1);
assert_eq!(*x.get_mut_unchecked(), 1_000_000_007);

x += Z(u64::max_value() / 2 - 1_000_000_007);
assert_eq!(*x.get_mut_unchecked(), u64::max_value() / 2);

x += Z(1);
assert_eq!(*x.get_mut_unchecked(), (u64::max_value() / 2 + 1) % 1_000_000_007);
```

### [`modtype::cartridges::ManuallyAdjust`]

```
use num::CheckedAdd as _;

#[modtype::use_modtype]
type Z = modtype::ModType<modtype::cartridges::ManuallyAdjust<u64>, 1_000_000_007u64>;

let mut x = Z(1_000_000_006);

x += Z(u64::max_value() - 1_000_000_006);
assert_eq!(*x.get_mut_unchecked(), u64::max_value());

x.adjust();
assert_eq!(*x.get_mut_unchecked(), u64::max_value() % 1_000_000_007);
```

[`modtype::ModType`]: https://docs.rs/modtype/0.6/modtype/struct.ModType.html
[`modtype::thread_local::ModType`]: https://docs.rs/modtype/0.6/modtype/thread_local/struct.ModType.html
[`modtype::non_static::ModType`]: https://docs.rs/modtype/0.7/modtype/non_static/struct.ModType.html
[`modtype::Cartridge`]: https://docs.rs/modtype/0.6/modtype/trait.Cartridge.html
[`modtype::cartridges::Multiplicative`]: https://docs.rs/modtype/0.7/modtype/cartridges/enum.Multiplicative.html
[`modtype::cartridges::Additive`]: https://docs.rs/modtype/0.7/modtype/cartridges/enum.Additive.html
[`modtype::cartridges::ManuallyAdjust`]: https://docs.rs/modtype/0.7/modtype/cartridges/enum.ManuallyAdjust.html
