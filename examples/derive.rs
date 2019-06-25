use modtype::ConstValue;

use std::marker::PhantomData;

fn main() {
    println!("{} / {} ≡ {}", F(3), F(4), F(3) / F(4));
}

type F = F_<Const17U32>;

#[allow(non_snake_case)]
fn F(value: u32) -> F {
    F::from(value)
}

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
    modtype::ToPrimitive,
    modtype::Inv,
    modtype::CheckedNeg,
    modtype::CheckedAdd,
    modtype::CheckedSub,
    modtype::CheckedMul,
    modtype::CheckedDiv,
    modtype::CheckedRem,
    modtype::Pow,
    modtype::Integer,
    modtype::ToBigUint,
    modtype::ToBigInt,
)]
#[modtype(
    modulus = "M::VALUE",
    std = "std",
    num_traits = "num::traits",
    num_integer = "num::integer",
    num_bigint = "num::bigint",
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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, ConstValue)]
#[modtype(const_value = 17u32)]
enum Const17U32 {}
