# Changelog

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
