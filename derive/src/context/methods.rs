use crate::context::Context;

use quote::quote;
use syn::{parse_quote, ItemFn};

impl Context {
    pub(crate) fn derive_new(&self) -> proc_macro::TokenStream {
        let Context {
            std,
            struct_vis,
            struct_ident,
            field_ty,
            ..
        } = self;

        let doc = format!("Constructs a new `{}`.", struct_ident);

        self.derive_struct_method(parse_quote! {
            #[doc = #doc]
            #[inline]
            #struct_vis fn new(value: #field_ty) -> Self {
                <Self as #std::convert::From<#field_ty>>::from(value)
            }
        })
    }

    pub(crate) fn derive_new_unchecked(&self) -> proc_macro::TokenStream {
        let Context {
            struct_vis,
            struct_ident,
            field_ty,
            ..
        } = self;

        let doc = format!(
            "Constructs a new `{}` without checking the value.",
            struct_ident,
        );
        let struct_expr = self.struct_expr(true, Some(parse_quote!(value)));

        self.derive_struct_method(parse_quote! {
            #[doc = #doc]
            #[inline]
            #struct_vis fn new_unchecked(value: #field_ty) -> Self {
                #struct_expr
            }
        })
    }

    pub(crate) fn derive_get(&self) -> proc_macro::TokenStream {
        let Context {
            struct_vis,
            field_ident,
            field_ty,
            ..
        } = self;

        self.derive_struct_method(parse_quote! {
            #[doc = "Gets the inner value."]
            #[inline]
            #struct_vis fn get(self) -> #field_ty {
                self.#field_ident
            }
        })
    }

    fn derive_struct_method(&self, item_fn: ItemFn) -> proc_macro::TokenStream {
        let Context {
            struct_ident,
            generics,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl#impl_generics #struct_ident#ty_generics
            #where_clause
            {
                #item_fn
            }
        )
        .into()
    }
}
