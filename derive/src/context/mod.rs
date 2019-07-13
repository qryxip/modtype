mod num;
mod std;

use if_chain::if_chain;
use proc_macro2::Span;
use quote::quote;
use syn::spanned::Spanned;
use syn::{
    parse_quote, Block, Data, DataEnum, DataStruct, DataUnion, DeriveInput, Expr, ExprStruct,
    Field, Fields, FieldsNamed, Generics, Ident, Lit, Meta, MetaList, MetaNameValue, NestedMeta,
    Path, Type, Visibility,
};

#[rustfmt::skip]
use ::std::convert::TryFrom;
#[rustfmt::skip]
use ::std::mem;

pub(crate) struct Context {
    modulus: Expr,
    cartridge: Path,
    std: Path,
    num_traits: Path,
    num_bigint: Path,
    modtype: Path,
    non_static_modulus: bool,
    struct_ident: Ident,
    generics: Generics,
    field_ident: Ident,
    field_ty: Type,
    other_fields: Vec<(Ident, Type)>,
}

impl Context {
    fn with_features(&self, features: &[Ident]) -> Generics {
        let Self {
            cartridge,
            modtype,
            generics,
            ..
        } = self;

        let bindings = {
            let mut bindings = quote!();
            for feature in features {
                if !bindings.is_empty() {
                    bindings.extend(quote!(,));
                }
                bindings.extend(quote!(#feature = #modtype::True));
            }
            bindings
        };

        let mut generics = generics.clone();
        generics
            .where_clause
            .get_or_insert_with(|| parse_quote!(where))
            .predicates
            .push(parse_quote! {
                <#cartridge as #modtype::Cartridge>::Features: #modtype::Features<#bindings>
            });

        generics
    }

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

    fn struct_update(&self, method: Ident, args: &[Expr]) -> (ExprStruct, ExprStruct) {
        let Self {
            cartridge,
            modtype,
            struct_ident,
            field_ident,
            other_fields,
            ..
        } = self;

        let value = quote!(<#cartridge as #modtype::Cartridge>::#method(#(#args, )*));

        if other_fields.is_empty() {
            (
                parse_quote!(Self { #field_ident: #value }),
                parse_quote!(#struct_ident { #field_ident: #value }),
            )
        } else {
            (
                parse_quote!(Self { #field_ident: #value, ..self }),
                parse_quote!(#struct_ident { #field_ident: #value, ..*self }),
            )
        }
    }

    fn struct_update_option(&self, method: Ident, args: &[Expr]) -> (Block, Block) {
        let Self {
            cartridge,
            std,
            modtype,
            struct_ident,
            field_ident,
            other_fields,
            ..
        } = self;

        let mut update_move = quote! {
            let #field_ident = <#cartridge as #modtype::Cartridge>::#method(#(#args, )*)?;
        };
        let mut update_copy = quote! {
            let #field_ident = <#cartridge as #modtype::Cartridge>::#method(#(#args, )*)?;
        };

        if other_fields.is_empty() {
            update_move.extend(quote! {
                #std::option::Option::Some(Self { #field_ident })
            });
            update_copy.extend(quote! {
                #std::option::Option::Some(#struct_ident { #field_ident })
            });
        } else {
            update_move.extend(quote! {
                #std::option::Option::Some(Self { #field_ident, ..self })
            });
            update_copy.extend(quote! {
                #std::option::Option::Some(#struct_ident { #field_ident, ..*self })
            });
        }

        (parse_quote!({#update_move}), parse_quote!({#update_copy}))
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

        fn put_expr(lhs: Span, rhs: &Lit, dist: &mut Option<Expr>) -> syn::Result<()> {
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

        fn put_path(lhs: Span, rhs: &Lit, dist: &mut Option<Path>) -> syn::Result<()> {
            let path = match rhs {
                Lit::Str(s) => s.parse::<Path>(),
                rhs => Err(rhs.to_error("expected string literal")),
            }?;
            match mem::replace(dist, Some(path)) {
                Some(_) => Err(syn::Error::new(lhs, "multiple definitions")),
                None => Ok(()),
            }
        }

        fn put_true(word: Span, dist: &mut bool) -> syn::Result<()> {
            if mem::replace(dist, true) {
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
            ident: struct_ident,
            generics,
            data,
            ..
        } = input;

        let mut modulus = None;
        let mut cartridge = None;
        let mut std = None;
        let mut num_traits = None;
        let mut num_integer = None;
        let mut num_bigint = None;
        let mut modtype = None;
        let mut non_static_modulus = false;

        fn error_on_ident(ident: &Ident) -> syn::Error {
            match ident.to_string().as_ref() {
                "modulus" => ident.to_error("expected `modulus = $LitStr`"),
                "cartridge" => ident.to_error("expected `cartridge = $LitStr`"),
                "std" => ident.to_error("expected `std = $LitStr`"),
                "num_traits" => ident.to_error("expected `num_traits = $LitStr`"),
                "num_integer" => ident.to_error("expected `num_integer = $LitStr`"),
                "num_bigint" => ident.to_error("expected `num_bigint = $LitStr`"),
                "modtype" => ident.to_error("expected `modtype = $LitStr`"),
                "non_static_modulus" => ident.to_error("expected `non_static_modulus`"),
                _ => ident.to_error("unknown identifier"),
            }
        }

        let mut on_word = |word: &Ident| -> syn::Result<()> {
            match word.to_string().as_ref() {
                "non_static_modulus" => put_true(word.span(), &mut non_static_modulus),
                _ => Err(error_on_ident(word)),
            }
        };

        fn on_list(list: &MetaList) -> syn::Result<()> {
            Err(error_on_ident(&list.ident))
        }

        let mut on_name_value = |name_value: &MetaNameValue| -> syn::Result<_> {
            let MetaNameValue { ident, lit, .. } = name_value;
            match ident.to_string().as_ref() {
                "modulus" => put_expr(ident.span(), lit, &mut modulus),
                "cartridge" => put_path(ident.span(), lit, &mut cartridge),
                "std" => put_path(ident.span(), lit, &mut std),
                "num_traits" => put_path(ident.span(), lit, &mut num_traits),
                "num_integer" => put_path(ident.span(), lit, &mut num_integer),
                "num_bigint" => put_path(ident.span(), lit, &mut num_bigint),
                "modtype" => put_path(ident.span(), lit, &mut modtype),
                _ => Err(error_on_ident(ident)),
            }
        };

        attrs.iter().try_for_each::<_, syn::Result<_>>(|attr| {
            if let Ok(meta) = attr.parse_meta() {
                if_chain! {
                    if let Ok(meta) = attr.parse_meta();
                    if let Meta::List(MetaList { ident, nested, .. }) = &meta;
                    if ident == "modtype";
                    then {
                        for nested in nested {
                            match nested {
                                NestedMeta::Meta(Meta::Word(word)) => on_word(word)?,
                                NestedMeta::Meta(Meta::List(list)) => on_list(list)?,
                                NestedMeta::Meta(Meta::NameValue(kv)) => on_name_value(kv)?,
                                NestedMeta::Literal(_) => {
                                    bail!(nested.span(), "expected meta. not literal");
                                },
                            }
                        }
                    } else {
                        error_on_target_attr(&meta)?;
                    }
                }
            }
            Ok(())
        })?;

        let modulus = modulus.ok_or_else(|| struct_ident.to_error("`modulus` required"))?;
        let cartridge = cartridge.ok_or_else(|| struct_ident.to_error("`cartridge` required"))?;

        let std = std.unwrap_or_else(|| parse_quote!(::std));
        let num_traits = num_traits.unwrap_or_else(|| parse_quote!(::num::traits));
        let num_bigint = num_bigint.unwrap_or_else(|| parse_quote!(::num::bigint));
        let modtype = modtype.unwrap_or_else(|| parse_quote!(::modtype));

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

        Ok(Self {
            modulus,
            cartridge,
            std,
            num_traits,
            num_bigint,
            modtype,
            non_static_modulus,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            other_fields,
        })
    }
}
