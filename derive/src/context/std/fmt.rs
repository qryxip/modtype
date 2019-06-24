use crate::context::Context;

use quote::quote;
use syn::{parse_quote, Ident};

impl Context {
    pub(crate) fn derive_display(&self) -> proc_macro::TokenStream {
        self.derive_fmt(parse_quote!(Display))
    }

    pub(crate) fn derive_debug_transparent(&self) -> proc_macro::TokenStream {
        self.derive_fmt(parse_quote!(Debug))
    }

    fn derive_fmt(&self, trait_ident: Ident) -> proc_macro::TokenStream {
        let Context {
            std,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl#impl_generics #std::fmt::#trait_ident for #struct_ident#ty_generics
                #where_clause
            {
                #[inline]
                fn fmt(&self, fmt: &mut #std::fmt::Formatter) -> #std::fmt::Result {
                    <#field_ty as #std::fmt::#trait_ident>::fmt(&self.#field_ident, fmt)
                }
            }
        )
        .into()
    }
}
