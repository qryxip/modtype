#[test]
fn cmp() {
    #[modtype::use_modtype]
    type F = modtype::F<5u32>;

    for a in 0..=4 {
        for b in 0..=4 {
            assert_eq!(a == b, F(a) == F(b));
            assert_eq!(a != b, F(a) != F(b));
            assert_eq!(a.partial_cmp(&b), F(a).partial_cmp(&F(b)));
            assert_eq!(a < b, F(a) < F(b));
            assert_eq!(a <= b, F(a) <= F(b));
            assert_eq!(a > b, F(a) > F(b));
            assert_eq!(a >= b, F(a) >= F(b));
            assert_eq!(a.cmp(&b), F(a).cmp(&F(b)));
            assert_eq!(a.min(b), *F(a).min(F(b)));
            assert_eq!(a.max(b), *F(a).max(F(b)));
        }
    }
}
