use modtype::use_modtype;

use num::traits::Inv as _;

#[test]
fn test_div_for_mod17() {
    #[use_modtype]
    type F = modtype::u64::F<17u64>;

    for a in 0..=16 {
        for b in 1..=16 {
            assert_eq!(*(F(a) / F(b) * F(b)), a);
        }
    }
}

#[test]
fn test_div_for_mod1000000007() {
    #[use_modtype]
    type F = modtype::u64::F<1_000_000_007u64>;

    assert_eq!(F(13).inv(), F(153_846_155));
}
