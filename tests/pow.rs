use num::pow::Pow as _;
use num::BigUint;
use once_cell::sync::Lazy;

#[modtype::use_modtype]
type F = modtype::F<1_000_000_007u64>;

#[test]
fn unsigned() {
    const BASE: u64 = 123_456_789;
    const EXP: u32 = 123;

    static EXPECTED: Lazy<BigUint> = Lazy::new(|| {
        let mut expected = BigUint::from(1u64);
        (0..EXP).for_each(|_| expected *= BASE);
        expected % 1_000_000_007u64
    });

    assert_eq!((*F(BASE).pow(EXP)).to_string(), EXPECTED.to_string());
}

#[test]
fn signed() {
    const MANTISSA: u64 = 0x10_000_000_000_000;
    const EXP: i16 = -53;

    assert_eq!(F(MANTISSA) * F(2).pow(EXP), F(1) / F(2));
}
