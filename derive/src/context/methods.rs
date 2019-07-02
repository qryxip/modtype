use crate::context::Context;

use quote::quote;
use syn::{parse_quote, ItemFn};

impl Context {
    pub(crate) fn derive_new(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            implementation,
            modtype,
            struct_vis,
            struct_ident,
            field_ty,
            ..
        } = self;

        let doc = format!("Constructs a new `{}`.", struct_ident);

        let value_expr = parse_quote!(<#implementation as #modtype::Impl>::new(value, #modulus));
        let struct_expr = self.struct_expr(true, Some(value_expr));

        self.derive_struct_method(parse_quote! {
            #[doc = #doc]
            #[inline]
            #struct_vis fn new(value: #field_ty) -> Self {
                #struct_expr
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
            modulus,
            implementation,
            modtype,
            struct_vis,
            field_ident,
            field_ty,
            ..
        } = self;

        self.derive_struct_method(parse_quote! {
            #[doc = "Gets the inner value."]
            #[inline]
            #struct_vis fn get(self) -> #field_ty {
                <#implementation as #modtype::Impl>::get(self.#field_ident, #modulus)
            }
        })
    }

    pub(crate) fn derive_plus(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            struct_vis,
            field_ident,
            field_ty,
            ..
        } = self;

        let (update, _) = self.struct_update(
            parse_quote!(plus),
            &[
                parse_quote!(self.#field_ident),
                parse_quote!(rhs),
                parse_quote!(#modulus),
            ],
        );

        self.derive_struct_method(parse_quote! {
            /// Add `rhs` to `self`.
            #[inline]
            #struct_vis fn plus(self, rhs: #field_ty) -> Self {
                #update
            }
        })
    }

    pub(crate) fn derive_minus(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            struct_vis,
            field_ident,
            field_ty,
            ..
        } = self;

        let (update, _) = self.struct_update(
            parse_quote!(minus),
            &[
                parse_quote!(self.#field_ident),
                parse_quote!(rhs),
                parse_quote!(#modulus),
            ],
        );

        self.derive_struct_method(parse_quote! {
            /// Subtract `rhs` from `self`.
            #[inline]
            #struct_vis fn minus(self, rhs: #field_ty) -> Self {
                #update
            }
        })
    }

    pub(crate) fn derive_times(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            struct_vis,
            field_ident,
            field_ty,
            ..
        } = self;

        let (update, _) = self.struct_update(
            parse_quote!(times),
            &[
                parse_quote!(self.#field_ident),
                parse_quote!(rhs),
                parse_quote!(#modulus),
            ],
        );

        self.derive_struct_method(parse_quote! {
            /// Multiply `self` by `rhs`.
            #[inline]
            #struct_vis fn times(self, rhs: #field_ty) -> Self {
                #update
            }
        })
    }

    pub(crate) fn derive_obelus(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            struct_vis,
            field_ident,
            field_ty,
            ..
        } = self;

        let (update, _) = self.struct_update(
            parse_quote!(obelus),
            &[
                parse_quote!(self.#field_ident),
                parse_quote!(rhs),
                parse_quote!(#modulus),
            ],
        );

        self.derive_struct_method(parse_quote! {
            /// Divide `self` by `rhs`.
            #[inline]
            #struct_vis fn obelus(self, rhs: #field_ty) -> Self {
                #update
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
