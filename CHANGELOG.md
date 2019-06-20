# Changelog

## [Unreleased]

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
