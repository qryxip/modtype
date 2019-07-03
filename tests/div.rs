use modtype::use_modtype;

use num::traits::Inv as _;

#[test]
fn mod17() {
    #[use_modtype]
    type F = modtype::DefaultModType<17u32>;

    for a in 0..=16 {
        for b in 1..=16 {
            assert_eq!(*(F(a) / F(b) * F(b)), a);
        }
    }
}

#[test]
fn mod1009() {
    #[use_modtype]
    type F = modtype::DefaultModType<1009u32>;
    for x in 1..=1008 {
        assert_eq!(F(x) * F(x).inv(), F(1));
    }
}

#[test]
fn mod1000000007() {
    #[use_modtype]
    type F = modtype::DefaultModType<1_000_000_007u64>;

    assert_eq!(F(13).inv(), F(153_846_155));
}
