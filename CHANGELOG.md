# Changelog

## [Unreleased]

### Added

- `sqrt` methods.
- `adjust` methods.
- `adjusted` methods.
- `Cartridge::{sqrt, adjust, adjusted, eq, cmp}`.
- `modtype::cartridges::{AllowFlexibleRhs, Field, Multiplicative, Additive, ManuallyAdjust}`.
- `From<{integer}, {float}, Ratio<BigUint>, Ratio<BigInt>>`

### Removed

- `modtype::util`.
- `Bounded` implementation.
- `Unsigned` implementation.
- `modtype::DefaultCartridge`.

### Changed

- Add `Features::{AssumePrimeModulus, AssumeAlwaysAdjusted, Equality, Order, Deref, FlexibleRhs}`.
- Rename `Features::{Addition, Subtraction, Multiplication, Division}` to `Partial{..}`.
- Modify the implementation of divisions.
- Hide `HasThreadLocalModulus`.
- `DefaultCartridge` takes a `Features` argument.
- Rename `modytpe::field_param` to `modtype::non_static`.
- Rename `{modtype, modtype::field_param, modtype::non_static}::DefaultModType` to `F` again.
- `Cartridge::from_*` no longer return `Option`.
- Remove type arguments from `ModType`s.
- Unify `Features` and `Cartridges`.

### Fixed

- `#[derive(ModType)]` no longer fails when the target has a non meta attribute such as `#[rustfmt::skip]`.

## [0.6.0] - 2019-07-02Z

### Added

- `{modtype, modtype::thread_local, modtype::field_param}::ModType::modulus`

### Changed

- Introduce `Features`.
- Rename `Impl` to `Cartridge`.
- Rename `Z`s to `ModType`.
- Unify derive macros.
- Modify the default `Cartridge::rem`.
- Rename `Cartridge::Uint` to `Target`.

### Removed

- `modtype::{..}::{u8, u16, u32, u64, u128, usize}::Z` aliases
- Method macros

## [0.5.0] - 2019-06-30Z

### Added

- `Clone`, `Copy`, `PartialEq`, `Eq`, `PartialOrd`, `Ord` derive macros.
- `UnsignedPrimitive`, `SignedPrimitive`, `FloatPrimitive`.
- Documents.

### Changed

- Almost everything.
    - The types have 2 or 3 type arguments.
    - Use generic unsigned types.
    - Move derive macros to `derive` module.
    - The derive macros just calls the methods of `Impl`.

### Removed

- `Integer` implementations (for now).
- `Into` implementations for preset types.
- Some derive macro attributes.

## [0.4.0] - 2019-06-26Z

### Added

- `#[use_modtype]` attribute macro.
- Trait specific attributes.
- `modtype::Pow` for `{u64, u128, i8, i16, i32, i64, i128, isize}`
- `modtype::new_unchecked`.
- `modtype::u64::field::Z`.

### Changed

- Move `modtype::preset::u64::F` to `modtype::u64::F`.
- Move `modtype::preset::u64::thread_local::F` to `modtype::u64::thread_local::Z`.
- Unify `modtype::Pow_*` macros.

### Removed

- `modtype::preset::u64::Z`.
- `modtype::preset::u64::mod1000000007::{F, Z}`.
- `modtype::DebugTransparent` alias.
- `no_impl_for_ref`.
- `modtype::ToPrimitive`
- `modtype::BigUint`
- `modtype::BigInt`

### Fixed

- `modtype::Pow`.
- `modtype::FromPrimitive`.

## [0.3.0] - 2019-06-22Z

### Added

- `modtype::preset::u64::thread_local::{with_modulus, F}`.

### Changed

- `moving_ops_for_ref` to `no_impl_for_ref`.

### Fixed

- `modtype` implementes `Neg for &'_ _`.
- `modtype::Pow_{..}` produces appropriate code.

## [0.2.0] - 2019-06-20Z

### Added

- `modtype::{CheckedAdd, CheckedSub, CheckedMul, CheckedDiv, CheckedRem, CheckedNeg}`.

### Changed

- `modtype::AddAssign` requires `Add<Self, Output = Self> + Copy`.
- `modtype::SubAssign` requires `Sub<Self, Output = Self> + Copy`.
- `modtype::MulAssign` requires `Mul<Self, Output = Self> + Copy`.
- `modtype::RemAssign` requires `Rem<Self, Output = Self> + Copy`.
- `modtype::BitAndAssign` requires `BigAnd<Self, Output = Self> + Copy`.
- `modtype::BitOrAssign` requires `BigOr<Self, Output = Self> + Copy`.
- `modtype::BitXorAssign` requires `BigXor<Self, Output = Self> + Copy`.

### Removed

- `modtype::{BitAnd, BitAndassign, BitOr, BitOrassign, BitXor, BitXorassign}`.

## [0.1.1] - 2019-06-20Z

### Added

- `modtype::Neg`
