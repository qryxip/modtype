mod methods;
mod num;
mod std;

use if_chain::if_chain;
use maplit::btreeset;
use proc_macro2::Span;
use quote::quote;
use syn::spanned::Spanned;
use syn::{
    parse_quote, Data, DataEnum, DataStruct, DataUnion, DeriveInput, Expr, ExprStruct, Field,
    Fields, FieldsNamed, Generics, Ident, Lit, Meta, MetaList, MetaNameValue, NestedMeta, Path,
    Type, Visibility,
};

#[rustfmt::skip]
use ::std::convert::{TryFrom, TryInto as _};
#[rustfmt::skip]
use ::std::collections::BTreeSet;
#[rustfmt::skip]
use ::std::mem;

pub(crate) struct Context {
    modulus: Expr,
    std: Path,
    num_traits: Path,
    num_integer: Path,
    num_bigint: Path,
    from: FromOptions,
    debug: DebugOptions,
    neg: OpOptions,
    add: OpOptions,
    add_assign: OpOptions,
    sub: OpOptions,
    sub_assign: OpOptions,
    mul: OpOptions,
    mul_assign: OpOptions,
    div: OpOptions,
    div_assign: OpOptions,
    rem: OpOptions,
    rem_assign: OpOptions,
    inv: OpOptions,
    pow: OpOptions,
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

        fn put_list_opts(
            list: &MetaList,
            dist: &mut Option<impl for<'a> TryFrom<&'a MetaList, Error = syn::Error>>,
        ) -> syn::Result<()> {
            if mem::replace(dist, Some(list.try_into()?)).is_some() {
                bail!(list.ident.span(), "multiple definitions");
            }
            Ok(())
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

        let mut from = None;
        let mut modulus = None;
        let mut std = None;
        let mut num_traits = None;
        let mut num_integer = None;
        let mut num_bigint = None;
        let mut debug = None;
        let mut neg = None;
        let mut add = None;
        let mut add_assign = None;
        let mut sub = None;
        let mut sub_assign = None;
        let mut mul = None;
        let mut mul_assign = None;
        let mut div = None;
        let mut div_assign = None;
        let mut rem = None;
        let mut rem_assign = None;
        let mut inv = None;
        let mut pow = None;

        fn error_on_ident(ident: &Ident) -> syn::Error {
            match ident.to_string().as_ref() {
                "modulus" => ident.to_error("expected `modulus = $LitStr`"),
                "std" => ident.to_error("expected `std = $LitStr`"),
                "num_traits" => ident.to_error("expected `num_traits = $LitStr`"),
                "num_integer" => ident.to_error("expected `num_integer = $LitStr`"),
                "num_bigint" => ident.to_error("expected `num_bigint = $LitStr`"),
                "from" => ident.to_error("expected `from(..)`"),
                "debug" => ident.to_error("expected `debug = $Ident`"),
                "neg" => ident.to_error("expected `neg(..)`"),
                "add" => ident.to_error("expected `add(..)`"),
                "add_assign" => ident.to_error("expected `add_assign(..)`"),
                "sub" => ident.to_error("expected `sub(..)`"),
                "sub_assign" => ident.to_error("expected `sub_assign(..)`"),
                "mul" => ident.to_error("expected `mul(..)`"),
                "mul_assign" => ident.to_error("expected `mul_assign(..)`"),
                "div" => ident.to_error("expected `div(..)`"),
                "div_assign" => ident.to_error("expected `div_assign(..)`"),
                "rem" => ident.to_error("expected `rem(..)`"),
                "rem_assign" => ident.to_error("expected `rem_assign(..)`"),
                "inv" => ident.to_error("expected `inv(..)`"),
                "pow" => ident.to_error("expected `pow(..)`"),
                _ => ident.to_error("unknown identifier"),
            }
        }

        fn on_word(word: &Ident) -> syn::Result<()> {
            Err(error_on_ident(word))
        }

        let mut on_list = |list: &MetaList| -> syn::Result<_> {
            match list.ident.to_string().as_ref() {
                "from" => put_list_opts(list, &mut from),
                "debug" => put_list_opts(list, &mut debug),
                "neg" => put_list_opts(list, &mut neg),
                "add" => put_list_opts(list, &mut add),
                "add_assign" => put_list_opts(list, &mut add_assign),
                "sub" => put_list_opts(list, &mut sub),
                "sub_assign" => put_list_opts(list, &mut sub_assign),
                "mul" => put_list_opts(list, &mut mul),
                "mul_assign" => put_list_opts(list, &mut mul_assign),
                "div" => put_list_opts(list, &mut div),
                "div_assign" => put_list_opts(list, &mut div_assign),
                "rem" => put_list_opts(list, &mut rem),
                "rem_assign" => put_list_opts(list, &mut rem_assign),
                "inv" => put_list_opts(list, &mut inv),
                "pow" => put_list_opts(list, &mut pow),
                _ => Err(error_on_ident(&list.ident)),
            }
        };

        let mut on_name_value = |name_value: &MetaNameValue| -> syn::Result<_> {
            let MetaNameValue { ident, lit, .. } = name_value;
            match ident.to_string().as_ref() {
                "modulus" => put_expr(ident.span(), lit, &mut modulus),
                "std" => put_path(ident.span(), lit, &mut std),
                "num_traits" => put_path(ident.span(), lit, &mut num_traits),
                "num_integer" => put_path(ident.span(), lit, &mut num_integer),
                "num_bigint" => put_path(ident.span(), lit, &mut num_bigint),
                _ => Err(error_on_ident(ident)),
            }
        };

        attrs.iter().try_for_each::<_, syn::Result<_>>(|attr| {
            let meta = attr
                .parse_meta()
                .map_err(|e| syn::Error::new(e.span(), format!("invalid meta: {}", e)))?;
            if_chain! {
                if let Meta::List(MetaList { ident, nested, .. }) = &meta;
                if ident == "modtype";
                then {
                    for nested in nested {
                        match nested {
                            NestedMeta::Meta(Meta::Word(word)) => on_word(word)?,
                            NestedMeta::Meta(Meta::List(list)) => on_list(list)?,
                            NestedMeta::Meta(Meta::NameValue(kv)) => on_name_value(kv)?,
                            NestedMeta::Literal(_) => bail!(nested.span(), "expected meta. not literal"),
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
        let from = from.unwrap_or_default();
        let debug = debug.unwrap_or_default();
        let neg = neg.unwrap_or_default();
        let add = add.unwrap_or_default();
        let add_assign = add_assign.unwrap_or_default();
        let sub = sub.unwrap_or_default();
        let sub_assign = sub_assign.unwrap_or_default();
        let mul = mul.unwrap_or_default();
        let mul_assign = mul_assign.unwrap_or_default();
        let div = div.unwrap_or_default();
        let div_assign = div_assign.unwrap_or_default();
        let rem = rem.unwrap_or_default();
        let rem_assign = rem_assign.unwrap_or_default();
        let inv = inv.unwrap_or_default();
        let pow = pow.unwrap_or_default();

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
            from,
            debug,
            neg,
            add,
            add_assign,
            sub,
            sub_assign,
            mul,
            mul_assign,
            div,
            div_assign,
            rem,
            rem_assign,
            inv,
            pow,
            struct_vis,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            other_fields,
        })
    }
}

struct FromOptions(BTreeSet<FromType>);

impl Default for FromOptions {
    fn default() -> Self {
        Self(btreeset![
            FromType::InnerValue,
            FromType::BigUint,
            FromType::BigInt,
        ])
    }
}

impl TryFrom<&'_ MetaList> for FromOptions {
    type Error = syn::Error;

    fn try_from(list: &'_ MetaList) -> syn::Result<Self> {
        let mut set = btreeset![];
        for nested in &list.nested {
            let word = match nested {
                NestedMeta::Meta(Meta::Word(word)) => word,
                nested => bail!(nested.span(), "expected identifier"),
            };
            let value = match word.to_string().as_ref() {
                "InnerValue" => FromType::InnerValue,
                "BigUint" => FromType::BigUint,
                "BigInt" => FromType::BigInt,
                _ => bail!(word.span(), "expected `InnerValue`, `BigUint`, or `BigInt`"),
            };
            if !set.insert(value) {
                bail!(word.span(), "multiple definitions");
            }
        }
        Ok(Self(set))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum FromType {
    InnerValue,
    BigUint,
    BigInt,
}

#[derive(Clone, Copy)]
struct DebugOptions(DebugKind);

impl Default for DebugOptions {
    fn default() -> Self {
        Self(DebugKind::SingleTuple)
    }
}

impl TryFrom<&'_ MetaList> for DebugOptions {
    type Error = syn::Error;

    fn try_from(list: &'_ MetaList) -> syn::Result<Self> {
        let kind = if_chain! {
            if list.nested.len() == 1;
            if let NestedMeta::Meta(Meta::Word(word)) = &list.nested[0];
            then {
                match word.to_string().as_ref() {
                    "SingleTuple" => DebugKind::SingleTuple,
                    "Transparent" => DebugKind::Transparent,
                    _ => bail!(word.span(), "expected `SingleTuple` or `Transparent`"),
                }
            } else {
                bail!(list.ident.span(), "expected `{}($Ident)`", list.ident);
            }
        };
        Ok(Self(kind))
    }
}

#[derive(Clone, Copy)]
enum DebugKind {
    SingleTuple,
    Transparent,
}

#[derive(Clone, Copy)]
struct OpOptions {
    for_ref: bool,
}

impl Default for OpOptions {
    fn default() -> Self {
        Self { for_ref: true }
    }
}

impl TryFrom<&'_ MetaList> for OpOptions {
    type Error = syn::Error;

    fn try_from(list: &'_ MetaList) -> syn::Result<Self> {
        let mut for_ref = None;

        for nested in &list.nested {
            let name_value = match nested {
                NestedMeta::Meta(Meta::NameValue(name_value)) => name_value,
                nested => bail!(nested.span(), "expected `$MetaNameValue` (`$Ident = $Lit`)"),
            };
            if name_value.ident == "for_ref" {
                let value = match &name_value.lit {
                    Lit::Bool(value) => value.value,
                    lit => bail!(lit.span(), "expected bool literal"),
                };
                for_ref = Some(value);
            } else {
                bail!(name_value.ident.span(), "expected `for_ref`");
            }
        }

        Ok(Self {
            for_ref: for_ref.unwrap_or_else(|| Self::default().for_ref),
        })
    }
}
