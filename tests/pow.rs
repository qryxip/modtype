use modtype::ConstValue;

use num::pow::Pow as _;
use num::BigUint;
use once_cell::sync::Lazy;

#[test]
fn it_works() {
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, ConstValue)]
    #[modtype(const_value = 1_000_000_007u64)]
    enum M {}

    type F = modtype::u64::F<M>;

    #[allow(non_snake_case)]
    fn F(value: u64) -> F {
        F::new(value)
    }

    const BASE: u64 = 123_456_789;
    const EXP: u32 = 123;

    static EXPECTED: Lazy<BigUint> = Lazy::new(|| {
        let mut expected = BigUint::from(1u64);
        (0..EXP).for_each(|_| expected *= BASE);
        expected % 1_000_000_007u64
    });

    assert_eq!(F(BASE).pow(EXP).to_string(), EXPECTED.to_string());
}
