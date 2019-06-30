use if_chain::if_chain;
use proc_macro2::Span;
use quote::quote;
use syn::spanned::Spanned as _;
use syn::{
    parse_quote, AngleBracketedGenericArguments, Expr, GenericArgument, Ident, IntSuffix, Item,
    ItemType, Lit, Meta, MetaList, NestedMeta, PathArguments, Type,
};

use std::mem;

pub(crate) fn use_modtype(
    args: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let try_do = || -> syn::Result<proc_macro2::TokenStream> {
        // HACK
        let args = {
            let args = proc_macro2::TokenStream::from(args);
            let args = quote!(use_modtype(#args));
            syn::parse2::<MetaList>(args)
                .map_err(|err| {
                    static MSG: &str = "expected punctuated sequence of `NestedMeta`s with ','";
                    syn::Error::new(err.span(), MSG)
                })?
                .nested
        };

        let (mut constant, mut constructor) = (None, None);
        for arg in args {
            if let NestedMeta::Meta(Meta::List(list)) = &arg {
                if !["constant", "constructor"].contains(&list.ident.to_string().as_ref()) {
                    bail!(list.ident.span(), "expected `constant` or `constructor`");
                }
                if list.nested.len() != 1 {
                    bail!(list.nested.span(), "expected 1 item");
                }
                let word = match &list.nested[0] {
                    NestedMeta::Meta(Meta::Word(word)) => word.clone(),
                    meta => bail!(meta.span(), "expected identifier"),
                };
                let target = if list.ident == "constant" {
                    &mut constant
                } else {
                    &mut constructor
                };
                if mem::replace(target, Some(word)).is_some() {
                    bail!(list.ident.span(), "multiple definitions");
                }
            } else {
                bail!(arg.span(), "expected `MetaList` (`$Ident(..)`)")
            }
        }

        let item = match syn::parse::<Item>(item)? {
            Item::Type(item) => item,
            _ => bail!(Span::call_site(), "expected `type ..`"),
        };

        let (int, int_value, int_ty) = {
            let path = if_chain! {
                if let Type::Path(type_path) = &*item.ty;
                if type_path.qself.is_none();
                then {
                    &type_path.path
                } else {
                    bail!(item.span(), "expected `type $Ident = $Path;`")
                }
            };
            let expr = if_chain! {
                if let Some(last) = path.segments.iter().last();
                if let PathArguments::AngleBracketed(args) = &last.arguments;
                let AngleBracketedGenericArguments { args, .. } = args;
                let const_exprs = args
                    .iter()
                    .flat_map(|arg| match arg {
                        GenericArgument::Const(expr) => Some(expr),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                if const_exprs.len() == 1;
                then {
                    const_exprs[0]
                } else {
                    bail!(path.span(), "expected 1 const argument")
                }
            };
            if_chain! {
                if let Expr::Lit(expr_lit) = expr;
                if expr_lit.attrs.is_empty();
                if let Lit::Int(int) = &expr_lit.lit;
                if let Some::<Ident>(mut ty) = match int.suffix() {
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
                    ty.set_span(int.span());
                    let value = int.value();
                    (int, value, ty)
                } else {
                    bail!(expr.span(), "expected integer with a suffix");
                }
            }
        };

        let constant = constant.unwrap_or_else(|| {
            let str = format!("_{}{}", int_value, int_ty.to_string().to_uppercase());
            Ident::new(&str, int.span())
        });
        let constructor = constructor.unwrap_or_else(|| item.ident.clone());

        let mut ty = (*item.ty).clone();
        if_chain! {
            if let Type::Path(type_path) = &mut ty;
            if let Some(last) = type_path.path.segments.iter_mut().last();
            if let PathArguments::AngleBracketed(args) = &mut last.arguments;
            let AngleBracketedGenericArguments { args, .. } = args;
            if let Some(arg) = args
                .iter_mut()
                .flat_map(|arg| match arg {
                    arg @ GenericArgument::Const(_) => Some(arg),
                    _ => None,
                })
                .next();
            then {
                *arg = GenericArgument::Type(parse_quote!(#constant));
            } else {
                unreachable!();
            }
        }

        let ty = Box::new(ty);
        let item = ItemType { ty, ..item };
        let ty_alias = &item.ident;

        Ok(quote! {
            #item

            #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
            enum #constant {}

            impl ::modtype::ConstValue for #constant {
                type Value = #int_ty;
                const VALUE: #int_ty = #int;
            }

            #[allow(non_snake_case)]
            #[inline]
            fn #constructor(value: #int_ty) -> #ty_alias {
                <#ty_alias as ::std::convert::From<#int_ty>>::from(value)
            }
        })
    };

    try_syn!(try_do()).into()
}
