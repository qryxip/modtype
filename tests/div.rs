use num::traits::Inv as _;
use num::{integer, CheckedDiv as _, One as _};
use rayon::iter::{IntoParallelIterator as _, ParallelIterator};

#[test]
fn mod17() {
    #[modtype::use_modtype(constant(M))]
    type F = modtype::F<17u32>;

    #[modtype::use_modtype(constant(M_))]
    type Z = modtype::ModType<modtype::cartridges::Multiplicative<u32>, 17u32>;

    for a in 0..=16 {
        for b in 1..=16 {
            assert_eq!(F(a) / F(b) * F(b), F(a));
        }
    }

    for a in 0..=16 {
        for b in 1..=16 {
            assert_eq!(Z(a).checked_div(&Z(b)).map(|x| x * Z(b)), Some(Z(a)));
        }
    }
}

#[test]
fn mod57() {
    #[modtype::use_modtype]
    type Z = modtype::ModType<modtype::cartridges::Multiplicative<u32>, 57u32>;

    for a in 0..=56 {
        let a_inv_checked = Z(1).checked_div(&Z(a));
        if integer::gcd(a, 57) == 1 {
            assert_eq!(a_inv_checked.map(|a_inv| Z(a) * a_inv), Some(Z(1)));
        } else {
            assert_eq!(a_inv_checked, None);
        }
    }
}

#[test]
fn mod1009() {
    #[modtype::use_modtype(constant(M))]
    type F = modtype::F<1009u32>;

    #[modtype::use_modtype(constant(M_))]
    type Z = modtype::ModType<modtype::cartridges::Multiplicative<u32>, 1009u32>;

    for x in 1..=1008 {
        assert_eq!(F(x).inv() * F(x), F(1));
    }

    for x in 1..=1008 {
        assert_eq!(Z(1).checked_div(&Z(x)).map(|i| i * Z(x)), Some(Z(1)));
    }
}

#[test]
fn mod1000000007() {
    #[modtype::use_modtype]
    type F = modtype::F<1_000_000_007u64>;

    for &x in &[1, 13, 42, 57, 1024, 100_000_000] {
        let inv = F(x).inv();
        let inv_checked = F(1).checked_div(&F(x));
        assert_eq!(Some(inv), inv_checked);
        assert_eq!(inv * F(x), F(1));
    }
}

#[test]
#[ignore]
fn mod1000000007_all() {
    if cfg!(debug_assertions) {
        panic!("this is too heavy to run in debug mode");
    }

    #[modtype::use_modtype]
    type F = modtype::F<1_000_000_007u64>;

    (1u64..1_000_000_007)
        .into_par_iter()
        .for_each(|x| assert!((F::new_unchecked(x).inv() * F::new_unchecked(x)).is_one()));
}
