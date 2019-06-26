use crate::context::{Context, DebugKind, DebugOptions};

use quote::quote;
use syn::{parse_quote, Block, LitStr};

impl Context {
    pub(crate) fn derive_display(&self) -> proc_macro::TokenStream {
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
            impl#impl_generics #std::fmt::Display for #struct_ident#ty_generics
                #where_clause
            {
                #[inline]
                fn fmt(&self, fmt: &mut #std::fmt::Formatter) -> #std::fmt::Result {
                    <#field_ty as #std::fmt::Display>::fmt(&self.#field_ident, fmt)
                }
            }
        )
        .into()
    }

    pub(crate) fn derive_debug(&self) -> proc_macro::TokenStream {
        let Context {
            std,
            debug: DebugOptions(kind),
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let block: Block = match kind {
            DebugKind::SingleTuple => {
                let tuple_name = LitStr::new(&struct_ident.to_string(), struct_ident.span());
                parse_quote!({
                    let mut fmt = #std::fmt::Formatter::debug_tuple(fmt, #tuple_name);
                    #std::fmt::DebugTuple::field(&mut fmt, &self.#field_ident);
                    #std::fmt::DebugTuple::finish(&mut fmt)
                })
            }
            DebugKind::Transparent => parse_quote!({
                <#field_ty as #std::fmt::Debug>::fmt(&self.#field_ident, fmt)
            }),
        };

        quote!(
            impl#impl_generics #std::fmt::Debug for #struct_ident#ty_generics
                #where_clause
            {
                #[inline]
                fn fmt(&self, fmt: &mut #std::fmt::Formatter) -> #std::fmt::Result #block
            }
        )
        .into()
    }
}
