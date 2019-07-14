#[test]
fn mod2() {
    #[modtype::use_modtype]
    type F = modtype::F<2u32>;

    assert_eq!(F(0).sqrt(), Some(F(0)));
    assert_eq!(F(1).sqrt(), Some(F(1)));
}

#[test]
fn mod41() {
    #[modtype::use_modtype]
    type F = modtype::F<41u32>;

    let mut num_quadratics = 0;

    for n in 0..=40 {
        if let Some(r) = F(n).sqrt() {
            assert_eq!(r * r, F(n));
            num_quadratics += 1;
        }
    }

    assert_eq!(num_quadratics, 21);
}

#[test]
fn mod1000000007() {
    #[modtype::use_modtype]
    type F = modtype::F<1_000_000_007u64>;

    assert_eq!(F(42).sqrt(), Some(F(82_681_419)));
}
