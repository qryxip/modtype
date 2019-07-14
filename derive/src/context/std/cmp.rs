use crate::context::Context;

use quote::quote;
use syn::parse_quote;

impl Context {
    pub(crate) fn derive_partial_eq(&self) -> proc_macro2::TokenStream {
        let Self {
            modulus,
            cartridge,
            std,
            modtype,
            struct_ident,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[parse_quote!(Equality)]);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote! {
            #[automatically_derived]
            impl#impl_generics #std::cmp::PartialEq for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn eq(&self, other: &Self) -> bool {
                    <#cartridge as #modtype::Cartridge>::eq(
                        self.#field_ident,
                        other.#field_ident,
                        #modulus,
                    )
                }
            }
        }
    }

    pub(crate) fn derive_eq(&self) -> proc_macro2::TokenStream {
        let Self {
            std, struct_ident, ..
        } = self;
        let generics = self.with_features(&[parse_quote!(Equality)]);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote! {
            #[automatically_derived]
            impl#impl_generics #std::cmp::Eq for #struct_ident#ty_generics
            #where_clause
            {
            }
        }
    }

    pub(crate) fn derive_partial_ord(&self) -> proc_macro2::TokenStream {
        let Self {
            modulus,
            cartridge,
            std,
            modtype,
            struct_ident,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[parse_quote!(Equality), parse_quote!(Order)]);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote! {
            #[automatically_derived]
            impl#impl_generics #std::cmp::PartialOrd for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn partial_cmp(&self, other: &Self) -> #std::option::Option<#std::cmp::Ordering> {
                    #std::option::Option::Some(
                        <#cartridge as #modtype::Cartridge>::cmp(
                            self.#field_ident,
                            other.#field_ident,
                            #modulus,
                        ),
                    )
                }
            }
        }
    }

    pub(crate) fn derive_ord(&self) -> proc_macro2::TokenStream {
        let Self {
            modulus,
            cartridge,
            std,
            modtype,
            struct_ident,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[parse_quote!(Equality), parse_quote!(Order)]);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote! {
            #[automatically_derived]
            impl#impl_generics #std::cmp::Ord for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn cmp(&self, other: &Self) -> #std::cmp::Ordering {
                    <#cartridge as #modtype::Cartridge>::cmp(
                        self.#field_ident,
                        other.#field_ident,
                        #modulus,
                    )
                }
            }
        }
    }
}
