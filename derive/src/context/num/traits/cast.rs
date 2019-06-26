use crate::context::Context;

use proc_macro2::Span;
use quote::quote;
use syn::{parse_quote, Ident, ItemFn};

impl Context {
    pub(crate) fn derive_from_primitive(&self) -> proc_macro::TokenStream {
        let Self {
            std,
            num_traits,
            struct_ident,
            generics,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let derive = |prim: Ident| -> ItemFn {
            let fn_ident = Ident::new(&format!("from_{}", prim), Span::call_site());
            parse_quote! {
                #[inline]
                fn #fn_ident(n: #prim) -> Option<Self> {
                    <#field_ty as #num_traits::FromPrimitive>::#fn_ident(n)
                        .map(<Self as #std::convert::From<#field_ty>>::from)
                }
            }
        };

        let methods = vec![
            derive(parse_quote!(i64)),
            derive(parse_quote!(u64)),
            derive(parse_quote!(isize)),
            derive(parse_quote!(i8)),
            derive(parse_quote!(i16)),
            derive(parse_quote!(i32)),
            derive(parse_quote!(i128)),
            derive(parse_quote!(usize)),
            derive(parse_quote!(u8)),
            derive(parse_quote!(u16)),
            derive(parse_quote!(u32)),
            derive(parse_quote!(u128)),
            derive(parse_quote!(f32)),
            derive(parse_quote!(f64)),
        ];

        quote!(
            impl#impl_generics #num_traits::FromPrimitive for #struct_ident#ty_generics
            #where_clause
            {
                #(#methods)*
            }
        )
        .into()
    }
}
