use modtype::{use_modtype, ConstValue};

use std::marker::PhantomData;

fn main() {
    println!("{} / {} ≡ {}", F(3), F(4), F(3) / F(4));
}

#[use_modtype]
type F = F_<17u32>;

#[derive(
    modtype::new,
    modtype::get,
    Default,
    Clone,
    Copy,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    modtype::From,
    modtype::Into,
    modtype::Display,
    modtype::Debug,
    modtype::FromStr,
    modtype::Deref,
    modtype::Neg,
    modtype::Add,
    modtype::AddAssign,
    modtype::Sub,
    modtype::SubAssign,
    modtype::Mul,
    modtype::MulAssign,
    modtype::Div,
    modtype::DivAssign,
    modtype::Rem,
    modtype::RemAssign,
    modtype::Num,
    modtype::Unsigned,
    modtype::Bounded,
    modtype::Zero,
    modtype::One,
    modtype::FromPrimitive,
    modtype::Inv,
    modtype::CheckedNeg,
    modtype::CheckedAdd,
    modtype::CheckedSub,
    modtype::CheckedMul,
    modtype::CheckedDiv,
    modtype::CheckedRem,
    modtype::Pow,
    modtype::Integer,
)]
#[modtype(
    modulus = "M::VALUE",
    std = "std",
    num_traits = "num::traits",
    num_integer = "num::integer",
    num_bigint = "num::bigint",
    from(InnerValue, BigUint, BigInt),
    debug(SingleTuple),
    neg(for_ref = true),
    add(for_ref = true),
    add_assign(for_ref = true),
    sub(for_ref = true),
    sub_assign(for_ref = true),
    mul(for_ref = true),
    mul_assign(for_ref = true),
    div(for_ref = true),
    div_assign(for_ref = true),
    rem(for_ref = true),
    rem_assign(for_ref = true),
    inv(for_ref = true),
    pow(for_ref = true)
)]
struct F_<M: ConstValue<Value = u32>> {
    #[modtype(value)]
    __value: u32,
    phantom: PhantomData<fn() -> M>,
}
