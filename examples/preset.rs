use modtype::use_modtype;

#[use_modtype]
type F = modtype::u64::F<1_000_000_007u64>;

fn main() {
    static INPUT: &str = "13";
    let mut a = INPUT.parse::<F>().unwrap();
    a += F(1_000_000_000);
    dbg!(a);
}
