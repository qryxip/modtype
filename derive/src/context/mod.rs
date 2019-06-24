mod methods;
mod num;
mod std;

use if_chain::if_chain;
use proc_macro2::Span;
use quote::quote;
use syn::spanned::Spanned;
use syn::{
    parse_quote, Attribute, Data, DataEnum, DataStruct, DataUnion, DeriveInput, Expr, ExprStruct,
    Field, Fields, FieldsNamed, Generics, Ident, Lit, Meta, MetaList, MetaNameValue, NestedMeta,
    Path, Type, Visibility,
};

#[rustfmt::skip]
use ::std::convert::TryFrom;
#[rustfmt::skip]
use ::std::mem;

pub(crate) struct Context {
    modulus: Expr,
    std: Path,
    num_traits: Path,
    num_integer: Path,
    num_bigint: Path,
    no_impl_for_ref: bool,
    struct_vis: Visibility,
    struct_ident: Ident,
    generics: Generics,
    field_ident: Ident,
    field_ty: Type,
    other_fields: Vec<(Ident, Type)>,
}

impl Context {
    fn struct_expr(&self, path_is_self: bool, value_expr: Option<Expr>) -> ExprStruct {
        let Self {
            std,
            struct_ident,
            field_ident,
            other_fields,
            ..
        } = self;

        let struct_ident_or_self: Path = if path_is_self {
            parse_quote!(Self)
        } else {
            parse_quote!(#struct_ident)
        };

        let value_field = match value_expr {
            None => quote!(#field_ident),
            Some(value_expr) => quote!(#field_ident: #value_expr),
        };

        let assign = other_fields
            .iter()
            .map(|(ident, ty)| quote!(#ident: <#ty as #std::default::Default>::default()));

        parse_quote! {
            #struct_ident_or_self {
                #value_field,
                #(#assign,)*
            }
        }
    }
}

impl TryFrom<DeriveInput> for Context {
    type Error = syn::Error;

    fn try_from(input: DeriveInput) -> syn::Result<Self> {
        fn error_on_target_attr(meta: &Meta) -> syn::Result<()> {
            match meta {
                Meta::Word(ident)
                | Meta::NameValue(MetaNameValue { ident, .. })
                | Meta::List(MetaList { ident, .. })
                    if ident == "modtype" =>
                {
                    Err(syn::Error::new(ident.span(), "`modtype` not allowed here"))
                }
                _ => Ok(()),
            }
        }

        fn put_expr_for(lhs: Span, rhs: &Lit, dist: &mut Option<Expr>) -> syn::Result<()> {
            let expr = match rhs {
                Lit::Int(int) => Ok(parse_quote!(#int)),
                Lit::Str(s) => s.parse(),
                rhs => Err(rhs.to_error("expected string or unsigned 64-bit integer")),
            }?;
            match mem::replace(dist, Some(expr)) {
                Some(_) => Err(syn::Error::new(lhs, "multiple definitions")),
                None => Ok(()),
            }
        }

        fn put_path_for(lhs: Span, rhs: &Lit, dist: &mut Option<Path>) -> syn::Result<()> {
            let path = match rhs {
                Lit::Str(s) => s.parse::<Path>(),
                rhs => Err(rhs.to_error("expected string literal")),
            }?;
            match mem::replace(dist, Some(path)) {
                Some(_) => Err(syn::Error::new(lhs, "multiple definitions")),
                None => Ok(()),
            }
        }

        fn put_true_for(word: Span, dist: &mut bool) -> syn::Result<()> {
            if ::std::mem::replace(dist, true) {
                Err(syn::Error::new(word, "multiple definitions"))
            } else {
                Ok(())
            }
        }

        trait SpannedExt {
            fn to_error(&self, mes: impl ::std::fmt::Display) -> syn::Error;
        }

        impl<T: Spanned> SpannedExt for T {
            fn to_error(&self, mes: impl ::std::fmt::Display) -> syn::Error {
                syn::Error::new(self.span(), mes)
            }
        }

        let DeriveInput {
            attrs,
            vis: struct_vis,
            ident: struct_ident,
            generics,
            data,
        } = input;

        let mut modulus = None;
        let mut std = None;
        let mut num_traits = None;
        let mut num_integer = None;
        let mut num_bigint = None;
        let mut no_impl_for_ref = false;

        let mut put_expr_or_path = |name_value: &MetaNameValue| -> syn::Result<_> {
            let span = name_value.span();
            let MetaNameValue { ident, lit, .. } = name_value;
            if ident == "modulus" {
                put_expr_for(ident.span(), lit, &mut modulus)
            } else if ident == "std" {
                put_path_for(ident.span(), lit, &mut std)
            } else if ident == "num_traits" {
                put_path_for(ident.span(), lit, &mut num_traits)
            } else if ident == "num_integer" {
                put_path_for(ident.span(), lit, &mut num_integer)
            } else if ident == "num_bigint" {
                put_path_for(ident.span(), lit, &mut num_bigint)
            } else if ident == "no_impl_for_ref" {
                Err(syn::Error::new(span, "expected `no_impl_for_ref`"))
            } else {
                Err(syn::Error::new(span, "unknown identifier"))
            }
        };

        let mut put_true = |word: &Ident| -> syn::Result<_> {
            if ["modulus", "std", "num_traits", "num_integer", "num_bigint"]
                .contains(&word.to_string().as_str())
            {
                Err(word.to_error(format!("expected `{} = #LitStr`", word)))
            } else if word == "no_impl_for_ref" {
                put_true_for(word.span(), &mut no_impl_for_ref)
            } else {
                Err(word.to_error("unknown identifier"))
            }
        };

        attrs
            .iter()
            .flat_map(Attribute::parse_meta)
            .try_for_each::<_, syn::Result<_>>(|meta| {
                if_chain! {
                    if let Meta::List(MetaList { ident, nested, .. }) = &meta;
                    if ident == "modtype";
                    then {
                        for nested in nested {
                            match nested {
                                NestedMeta::Meta(Meta::Word(word)) => put_true(word)?,
                                NestedMeta::Meta(Meta::NameValue(kv)) => put_expr_or_path(kv)?,
                                _ => return Err(nested.to_error("expected `#Ident` or `#Ident = #Lit`")),
                            }
                        }
                        Ok(())
                    } else {
                        error_on_target_attr(&meta)
                    }
                }
            })?;

        let modulus = modulus.ok_or_else(|| struct_ident.to_error("`modulus` required"))?;
        let std = std.unwrap_or_else(|| parse_quote!(::std));
        let num_traits = num_traits.unwrap_or_else(|| parse_quote!(::num::traits));
        let num_integer = num_integer.unwrap_or_else(|| parse_quote!(::num::integer));
        let num_bigint = num_bigint.unwrap_or_else(|| parse_quote!(::num::bigint));

        let fields = match data {
            Data::Struct(DataStruct { fields, .. }) => Ok(fields),
            Data::Enum(DataEnum { enum_token, .. }) => {
                Err(enum_token.to_error("expected a struct"))
            }
            Data::Union(DataUnion { union_token, .. }) => {
                Err(union_token.to_error("expected a struct"))
            }
        }?;

        let named = match fields {
            Fields::Named(FieldsNamed { named, .. }) => Ok(named),
            fields => Err(fields.to_error("expected named fields")),
        }?;
        let named_span = named.span();

        let (mut value_field, mut other_fields) = (None, vec![]);
        'l: for field in named {
            for attr in &field.attrs {
                if let Ok(meta) = attr.parse_meta() {
                    if_chain! {
                        if let Meta::List(MetaList { ident, nested, .. }) = &meta;
                        if ident == "modtype";
                        then {
                            if ![parse_quote!(value), parse_quote!(value,)].contains(nested) {
                                return Err(nested.to_error("expected `value` or `value,`"));
                            }
                            value_field = Some(field);
                            continue 'l;
                        } else {
                            error_on_target_attr(&meta)?;
                        }
                    }
                }
            }
            other_fields.push((field.ident.unwrap(), field.ty));
        }

        let Field {
            vis,
            ident,
            ty: field_ty,
            ..
        } = value_field
            .ok_or_else(|| syn::Error::new(named_span, "`#[modtype(value)]` not found"))?;
        let field_ident = ident.unwrap();

        if vis != Visibility::Inherited {
            return Err(vis.to_error("the field visibility must be `Inherited`"));
        }

        if !field_ident.to_string().starts_with("__") {
            return Err(field_ident.to_error("the field name must start with \"__\""));
        }

        Ok(Self {
            modulus,
            std,
            num_traits,
            num_integer,
            num_bigint,
            no_impl_for_ref,
            struct_vis,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            other_fields,
        })
    }
}
