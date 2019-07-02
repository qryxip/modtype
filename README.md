# modtype

[![Build Status](https://img.shields.io/travis/com/qryxip/modtype/master.svg?label=windows%20%26%20macos%20%26%20linux)](https://travis-ci.com/qryxip/modtype)
[![codecov](https://codecov.io/gh/qryxip/modtype/branch/master/graph/badge.svg)](https://codecov.io/gh/qryxip/modtype)
[![Crates.io](https://img.shields.io/crates/v/modtype.svg)](https://crates.io/crates/modtype)

This crate provides modular arithmetic integer types.

# Usage

## [`modtype::ModType`]

```
#[modtype::use_modtype]
type F = modtype::DefaultModType<1_000_000_007u64>;

assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
```

## [`modtype::thread_local::ModType`]

```
#[allow(non_snake_case)]
modtype::thread_local::DefaultModType::with(57u32, |Z| {
    assert_eq!(Z(42) + Z(15), Z(0));
});
```

## [`modtype::field_param::ModType`]

```
use num::CheckedDiv as _;

#[allow(non_snake_case)]
let Z = modtype::field_param::DefaultModType::factory(1000u32);

assert_eq!(Z(1).checked_div(&Z(777)), Some(Z(713))); // 777 × 713 ≡ 1 (mod 1000)
```

# Customization

`ModType`s can be customized via [`modtype::Cartridge`].

```
#[modtype::use_modtype]
type F = modtype::ModType<u64, Cartridge, 1_000_000_007u64>;

enum Cartridge {}

impl modtype::Cartridge for Cartridge {
    type Target = u64;
    type Features = modtype::DefaultFeatures;

    // your implementation here
}
```

[`modtype::ModType`]: https://docs.rs/modtype/0.6/modtype/struct.ModType.html
[`modtype::thread_local::ModType`]: https://docs.rs/modtype/0.6/modtype/thread_local/struct.ModType.html
[`modtype::field_param::ModType`]: https://docs.rs/modtype/0.6/modtype/field_param/struct.ModType.html
[`modtype::Cartridge`]: https://docs.rs/modtype/0.6/modtype/trait.Cartridge.html
