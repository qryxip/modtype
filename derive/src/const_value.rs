use if_chain::if_chain;
use proc_macro2::Span;
use quote::quote;
use syn::spanned::Spanned;
use syn::{
    parse_macro_input, parse_quote, Data, DeriveInput, Fields, IntSuffix, Lit, Meta, MetaList,
    MetaNameValue, NestedMeta, Type,
};

use std::mem;

pub(crate) fn const_value(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    fn compile_error(span: Span, msg: &str) -> proc_macro::TokenStream {
        syn::Error::new(span, msg).to_compile_error().into()
    }

    let DeriveInput {
        attrs,
        ident,
        generics,
        data,
        ..
    } = parse_macro_input!(input as DeriveInput);

    if !generics.params.is_empty() {
        return compile_error(generics.span(), "The generics parameters must be empty");
    }

    let field_attrs = match data {
        Data::Struct(data) => match data.fields {
            Fields::Named(fields) => fields.named.into_iter().flat_map(|f| f.attrs).collect(),
            Fields::Unnamed(fields) => fields.unnamed.into_iter().flat_map(|f| f.attrs).collect(),
            Fields::Unit => vec![],
        },
        Data::Enum(data) => data.variants.into_iter().flat_map(|f| f.attrs).collect(),
        Data::Union(data) => data
            .fields
            .named
            .into_iter()
            .flat_map(|f| f.attrs)
            .collect(),
    };
    for attr in field_attrs {
        if let Ok(meta) = attr.parse_meta() {
            match &meta {
                Meta::Word(ident)
                | Meta::NameValue(MetaNameValue { ident, .. })
                | Meta::List(MetaList { ident, .. })
                    if ident == "modtype" =>
                {
                    return compile_error(ident.span(), "not allowed here");
                }
                _ => {}
            }
        }
    }

    static MSG: &str = "expected `modtype(const_value = #LitInt)` where the `LitInt` has a suffix";

    let mut int = None;

    for attr in &attrs {
        if let Ok(meta) = attr.parse_meta() {
            match &meta {
                Meta::Word(ident) | Meta::NameValue(MetaNameValue { ident, .. })
                    if ident == "modtype" =>
                {
                    return compile_error(ident.span(), MSG);
                }
                Meta::List(MetaList { ident, nested, .. }) if ident == "modtype" => {
                    let (value, ty, span) = if_chain! {
                        if nested.len() == 1;
                        if let NestedMeta::Meta(Meta::NameValue(name_value)) = &nested[0];
                        if name_value.ident == "const_value";
                        if let Lit::Int(int) = &name_value.lit;
                        if let Some::<Type>(ty) = match int.suffix() {
                            IntSuffix::I8 => Some(parse_quote!(i8)),
                            IntSuffix::I16 => Some(parse_quote!(i16)),
                            IntSuffix::I32 => Some(parse_quote!(i32)),
                            IntSuffix::I64 => Some(parse_quote!(i64)),
                            IntSuffix::I128 => Some(parse_quote!(i128)),
                            IntSuffix::Isize => Some(parse_quote!(isize)),
                            IntSuffix::U8 => Some(parse_quote!(u8)),
                            IntSuffix::U16 => Some(parse_quote!(u16)),
                            IntSuffix::U32 => Some(parse_quote!(u32)),
                            IntSuffix::U64 => Some(parse_quote!(u64)),
                            IntSuffix::U128 => Some(parse_quote!(u128)),
                            IntSuffix::Usize => Some(parse_quote!(usize)),
                            IntSuffix::None => None,
                        };
                        then {
                            (int.clone(), ty, ident.span())
                        } else {
                            return compile_error(ident.span(), MSG);
                        }
                    };
                    if mem::replace(&mut int, Some((value, ty))).is_some() {
                        return compile_error(span, "multiple definition");
                    }
                }
                _ => {}
            }
        }
    }

    let (int, ty) = match int {
        None => return compile_error(Span::call_site(), MSG),
        Some(int) => int,
    };

    quote!(
        impl ::modtype::ConstValue for #ident {
            type Value = #ty;
            const VALUE: #ty = #int;
        }
    )
    .into()
}
