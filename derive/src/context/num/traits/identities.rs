use crate::context::Context;

use quote::quote;
use syn::{parse_quote, Ident};

impl Context {
    pub(crate) fn derive_zero(&self) -> proc_macro::TokenStream {
        self.derive_identity(
            parse_quote!(Zero),
            parse_quote!(zero),
            parse_quote!(is_zero),
        )
    }

    pub(crate) fn derive_one(&self) -> proc_macro::TokenStream {
        self.derive_identity(parse_quote!(One), parse_quote!(one), parse_quote!(is_one))
    }

    fn derive_identity(
        &self,
        trait_ident: Ident,
        value: Ident,
        is: Ident,
    ) -> proc_macro::TokenStream {
        let Context {
            num_traits,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let struct_expr = self.struct_expr(
            true,
            Some(parse_quote!(<#field_ty as #num_traits::#trait_ident>::#value())),
        );

        quote!(
            impl#impl_generics #num_traits::#trait_ident for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn #value() -> Self {
                    #struct_expr
                }

                #[inline]
                fn #is(&self) -> bool {
                    <#field_ty as #num_traits::#trait_ident>::#is(&self.#field_ident)
                }
            }
        )
        .into()
    }
}
