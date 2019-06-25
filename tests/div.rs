use modtype::ConstValue;

use num::traits::Inv as _;

#[test]
fn test_div_for_mod17() {
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, ConstValue)]
    #[modtype(const_value = 17u64)]
    enum M {}

    type F = modtype::u64::F<M>;

    #[allow(non_snake_case)]
    fn F(value: u64) -> F {
        F::new(value)
    }

    for a in 0..=16 {
        for b in 1..=16 {
            assert_eq!(*(F(a) / F(b) * F(b)), a);
        }
    }
}

#[test]
fn test_div_for_mod1000000007() {
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, ConstValue)]
    #[modtype(const_value = 1_000_000_007u64)]
    enum M {}

    type F = modtype::u64::F<M>;

    #[allow(non_snake_case)]
    fn F(value: u64) -> F {
        F::new(value)
    }

    assert_eq!(F(13).inv(), F(153_846_155));
}
