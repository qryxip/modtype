use modtype::ConstValue;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, ConstValue)]
#[modtype(const_value = 1_000_000_007u64)]
enum M {}

type Z = modtype::u64::Z<M>;

#[allow(non_snake_case)]
fn Z(value: u64) -> Z {
    Z::new(value)
}

fn main() {
    static INPUT: &str = "13";
    let mut a = INPUT.parse::<Z>().unwrap();
    a += Z(1_000_000_000);
    dbg!(a);
}
