use crate::context::Context;

use quote::quote;
use syn::{parse_quote, Ident, Type};

impl Context {
    pub(crate) fn derive_to_big_uint(&self) -> proc_macro::TokenStream {
        let Self {
            std, num_bigint, ..
        } = self;
        self.derive_ref_unary_transparent(
            parse_quote!(#num_bigint::ToBigUint),
            parse_quote!(to_biguint),
            parse_quote!(#std::option::Option<#num_bigint::BigUint>),
        )
    }

    pub(crate) fn derive_to_big_int(&self) -> proc_macro::TokenStream {
        let Self {
            std, num_bigint, ..
        } = self;
        self.derive_ref_unary_transparent(
            parse_quote!(#num_bigint::ToBigInt),
            parse_quote!(to_bigint),
            parse_quote!(#std::option::Option<#num_bigint::BigInt>),
        )
    }

    fn derive_ref_unary_transparent(
        &self,
        trait_ty: Type,
        fn_ident: Ident,
        output_ty: Type,
    ) -> proc_macro::TokenStream {
        let Context {
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl#impl_generics #trait_ty for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn #fn_ident(&self) -> #output_ty {
                    <#field_ty as #trait_ty>::#fn_ident(&self.#field_ident)
                }
            }
        )
        .into()
    }
}
