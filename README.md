# modtype

[![Build Status](https://img.shields.io/travis/com/qryxip/modtype/master.svg?label=windows%20%26%20macos%20%26%20linux)](https://travis-ci.com/qryxip/modtype)
[![codecov](https://codecov.io/gh/qryxip/modtype/branch/master/graph/badge.svg)](https://codecov.io/gh/qryxip/modtype)
[![Crates.io](https://img.shields.io/crates/v/modtype.svg)](https://crates.io/crates/modtype)

This crate provides modular arithmetic integer types.

## Usage

### [`modtype::Z`]

```
#[modtype::use_modtype]
type F = modtype::u64::Z<1_000_000_007u64>;

assert_eq!((F(1_000_000_006) + F(2)).to_string(), "1");
```

### [`modtype::thread_local::Z`]

```
#[allow(non_snake_case)]
modtype::thread_local::u32::Z::with(7, |F| {
    assert_eq!(F(6) + F(1), F(0));
});
```

### [`modtype::field_param::Z`]

```
use modtype::field_param::u32::Z;
use num::CheckedDiv as _;

#[allow(non_snake_case)]
let Z = Z::factory(1000);

assert_eq!(Z(1).checked_div(&Z(777)), Some(Z(713))); // 777 × 713 ≡ 1 (mod 1000)
```

## Customization

`Z`s can be customized via [`modtype::Impl`].

```
#[modtype::use_modtype]
type F = modtype::Z<u64, Impl, 1_000_000_007u64>;

enum Impl {}

impl modtype::Impl for Impl {
    type Uint = u64;

    // your implementation here
}
```

## Attributes for [`use_modtype`]

| Name          | Format                         | Optional                                                |
| :------------ | :----------------------------- | :------------------------------------------------------ |
| `constant`    | `constant($`[`Ident`]`)`       | Yes (default = `concat!(_, $value, $type_pascal_case)`) |
| `constructor` | `constructor($`[`Ident`]`)`    | Yes (default = the type alias)                          |

[`Ident`]: https://docs.rs/syn/0.15/syn/struct.Ident.html
[`modtype::Z`]: https://docs.rs/modtype/0.5/modtype/struct.Z.html
[`modtype::thread_local::Z`]: https://docs.rs/modtype/0.5/modtype/thread_local/struct.Z.html
[`modtype::field_param::Z`]: https://docs.rs/modtype/0.5/modtype/field_param/struct.Z.html
[`modtype::Impl`]: https://docs.rs/modtype/0.5/modtype/trait.Impl.html
[`use_modtype`]: https://docs.rs/modtype_derive/0.5/modtype_derive/attr.use_modtype.html
