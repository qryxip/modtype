# Changelog

## [Unreleased]

### Added

- `modtype::{Pow_u64, Pow_u128}`.

### Changed

- Move `modtype::preset::u64::F` to `modtype::u64::F`.
- Move `modtype::preset::u64::Z` to `modtype::u64::Z`.
- Move `modtype::preset::u64::thread_local::F` to `modtype::u64::thread_local::Z`.

### Removed

- `modtype::preset::u64::mod1000000007::{F, Z}`.

### Fixed

- `modtype::Pow_{u8, u16, u32, usize}`.

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
