use crate::context::Context;

use quote::quote;
use syn::parse_quote;

impl Context {
    pub(crate) fn derive_from(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            std,
            struct_ident,
            generics,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let struct_expr = self.struct_expr(true, Some(parse_quote!(from % #modulus)));

        quote!(
            impl #impl_generics #std::convert::From<#field_ty> for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn from(from: #field_ty) -> Self {
                    #struct_expr
                }
            }
        )
        .into()
    }

    pub(crate) fn derive_into(&self) -> proc_macro::TokenStream {
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
            impl #impl_generics #std::convert::From<#struct_ident#ty_generics> for #field_ty
            #where_clause
            {
                #[inline]
                fn from(from: #struct_ident#ty_generics) -> Self {
                    from.#field_ident
                }
            }
        )
        .into()
    }
}
