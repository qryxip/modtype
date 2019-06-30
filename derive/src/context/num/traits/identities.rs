use crate::context::Context;

use quote::quote;
use syn::parse_quote;

impl Context {
    pub(crate) fn derive_zero(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            implementation,
            num_traits,
            modtype,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let zero = parse_quote!(<#implementation as #modtype::Impl>::zero(#modulus));
        let zero = self.struct_expr(true, Some(zero));

        quote!(
            impl#impl_generics #num_traits::Zero for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn zero() -> Self {
                    #zero
                }

                #[inline]
                fn is_zero(&self) -> bool {
                    <#implementation as #modtype::Impl>::is_zero(self.#field_ident, #modulus)
                }
            }
        )
        .into()
    }

    pub(crate) fn derive_one(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            implementation,
            num_traits,
            modtype,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let one = parse_quote!(<#implementation as #modtype::Impl>::one(#modulus));
        let one = self.struct_expr(true, Some(one));

        quote!(
            impl#impl_generics #num_traits::One for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn one() -> Self {
                    #one
                }

                #[inline]
                fn is_one(&self) -> bool {
                    <#implementation as #modtype::Impl>::is_one(self.#field_ident, #modulus)
                }
            }
        )
        .into()
    }
}
