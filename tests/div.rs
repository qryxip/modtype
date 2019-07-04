use modtype::use_modtype;

use num::traits::Inv as _;
use num::{integer, CheckedDiv as _};

#[test]
fn mod17() {
    #[use_modtype]
    type F = modtype::DefaultModType<17u32>;

    for a in 0..=16 {
        for b in 1..=16 {
            let div = F(a) / F(b);
            let div_checked = F(a).checked_div(&F(b));
            assert_eq!(Some(div), div_checked);
            assert_eq!(div * F(b), F(a));
        }
    }
}

#[test]
fn mod57() {
    #[use_modtype]
    type F = modtype::DefaultModType<57u32>;

    for a in 0..=56 {
        let a_inv_checked = F(1).checked_div(&F(a));
        if integer::gcd(a, 57) == 1 {
            assert_eq!(a_inv_checked.map(|a_inv| F(a) * a_inv), Some(F(1)));
            assert_eq!(F(a) * F(a).inv(), F(1));
        } else {
            assert_eq!(a_inv_checked, None);
        }
    }
}

#[test]
fn mod1009() {
    #[use_modtype]
    type F = modtype::DefaultModType<1009u32>;

    for x in 1..=1008 {
        let inv = F(x).inv();
        let inv_checked = F(1).checked_div(&F(x));
        assert_eq!(Some(inv), inv_checked);
        assert_eq!(inv * F(x), F(1));
    }
}

#[test]
fn mod1000000007() {
    #[use_modtype]
    type F = modtype::DefaultModType<1_000_000_007u64>;

    for &x in &[1, 13, 42, 57, 1024, 100_000_000] {
        let inv = F(x).inv();
        let inv_checked = F(1).checked_div(&F(x));
        assert_eq!(Some(inv), inv_checked);
        assert_eq!(inv * F(x), F(1));
    }
}
