use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_bounded(&self) -> proc_macro::TokenStream {
        let Self {
            modulus,
            std,
            num_traits,
            struct_ident,
            generics,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl#impl_generics #num_traits::Bounded for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn min_value() -> Self {
                    let zero = <#field_ty as #num_traits::Zero>::zero();
                    <Self as #std::convert::From<#field_ty>>::from(zero)
                }

                #[inline]
                fn max_value() -> Self {
                    let minus_1 = #modulus - <#field_ty as #num_traits::One>::one();
                    <Self as #std::convert::From<#field_ty>>::from(minus_1)
                }
            }
        )
        .into()
    }
}
