use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_partial_eq(&self) -> proc_macro2::TokenStream {
        let Self {
            std,
            struct_ident,
            generics,
            field_ident,
            other_fields,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let other_eqs = other_fields
            .iter()
            .map(|(ident, _)| quote!(self.#ident == other.#ident));
        let other_nes = other_fields
            .iter()
            .map(|(ident, _)| quote!(self.#ident != other.#ident));

        quote! {
            #[automatically_derived]
            impl#impl_generics #std::cmp::PartialEq for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn eq(&self, other: &Self) -> bool {
                    self.#field_ident == other.#field_ident
                        #(&& #other_eqs)*
                }

                #[allow(clippy::partialeq_ne_impl)]
                #[inline]
                fn ne(&self, other: &Self) -> bool {
                    self.#field_ident != other.#field_ident
                        #(|| #other_nes)*
                }
            }
        }
    }

    pub(crate) fn derive_eq(&self) -> proc_macro2::TokenStream {
        let Self {
            std,
            struct_ident,
            generics,
            ..
        } = self;
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
            std,
            struct_ident,
            generics,
            field_ident,
            other_fields,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let mut idents = vec![field_ident];
        idents.extend(other_fields.iter().map(|(i, _)| i));
        let last_ident = idents.iter().last().unwrap_or(&field_ident);

        let mut l_g_t_e = quote!(#std::cmp::Ord::cmp(&self.#last_ident, &other.#last_ident));
        for ident in idents.iter().rev().skip(1) {
            l_g_t_e = quote! {
                ::std::cmp::Ordering::then_with(
                    #l_g_t_e,
                    || #std::cmp::Ord::cmp(&self.#ident, &other.#ident),
                )
            };
        }

        quote! {
            #[automatically_derived]
            impl#impl_generics #std::cmp::PartialOrd for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn partial_cmp(&self, other: &Self) -> #std::option::Option<#std::cmp::Ordering> {
                    #std::option::Option::Some(#std::cmp::Ord::cmp(self, other))
                }

                #[inline]
                fn lt(&self, other: &Self) -> bool {
                    #l_g_t_e == #std::cmp::Ordering::Less
                }

                #[inline]
                fn le(&self, other: &Self) -> bool {
                    #l_g_t_e != #std::cmp::Ordering::Greater
                }

                #[inline]
                fn gt(&self, other: &Self) -> bool {
                    #l_g_t_e == #std::cmp::Ordering::Greater
                }

                #[inline]
                fn ge(&self, other: &Self) -> bool {
                    #l_g_t_e != #std::cmp::Ordering::Less
                }
            }
        }
    }

    pub(crate) fn derive_ord(&self) -> proc_macro2::TokenStream {
        let Self {
            std,
            struct_ident,
            generics,
            field_ident,
            other_fields,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let mut idents = vec![field_ident];
        idents.extend(other_fields.iter().map(|(i, _)| i));

        let mut cmp = quote!({ #std::cmp::Ordering::Equal });
        for ident in idents.iter().rev() {
            cmp = quote! {
                match #std::cmp::Ord::cmp(&self.#ident, &other.#ident) {
                    #std::cmp::Ordering::Equal => #cmp,
                    cmp => cmp,
                }
            };
        }

        quote! {
            #[automatically_derived]
            impl#impl_generics #std::cmp::Ord for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn cmp(&self, other: &Self) -> #std::cmp::Ordering {
                    #cmp
                }
            }
        }
    }
}
