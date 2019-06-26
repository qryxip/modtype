use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_integer(&self) -> proc_macro::TokenStream {
        let Self {
            modulus,
            std,
            num_traits,
            num_integer,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl#impl_generics #num_integer::Integer for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn div_floor(&self, other: &Self) -> Self {
                    fn static_assert_copy<T: #std::marker::Copy>() {}
                    static_assert_copy::<Self>();

                    *self / *other
                }

                #[inline]
                fn mod_floor(&self, other: &Self) -> Self {
                    *self / *other
                }

                #[inline]
                fn gcd(&self, other: &Self) -> Self {
                    let max = #std::cmp::max(self.#field_ident, other.#field_ident);
                    <Self as #std::convert::From<#field_ty>>::from(max)
                }

                #[inline]
                fn lcm(&self, other: &Self) -> Self {
                    let mut value = #num_integer::lcm(self.#field_ident, other.#field_ident);
                    if value >= #modulus {
                        value %= #modulus;
                    }
                    <Self as #std::convert::From<#field_ty>>::from(value)
                }

                #[inline]
                fn divides(&self, other: &Self) -> bool {
                    <Self as #num_integer::Integer>::is_multiple_of(self, other)
                }

                #[inline]
                fn is_multiple_of(&self, other: &Self) -> bool {
                    <#field_ty as #num_traits::Zero>::is_zero(&(*self % *other))
                }

                #[inline]
                fn is_even(&self) -> bool {
                    <#field_ty as #num_integer::Integer>::is_even(&self.#field_ident)
                }

                #[inline]
                fn is_odd(&self) -> bool {
                    <#field_ty as #num_integer::Integer>::is_odd(&self.#field_ident)
                }

                #[inline]
                fn div_rem(&self, other: &Self) -> (Self, Self) {
                    (*self / *other, <Self as #num_traits::Zero>::zero())
                }
            }
        )
        .into()
    }
}
