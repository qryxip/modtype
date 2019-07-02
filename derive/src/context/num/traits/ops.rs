use crate::context::Context;

use quote::quote;
use syn::{parse_quote, Ident};

impl Context {
    pub(crate) fn derive_inv(&self) -> proc_macro2::TokenStream {
        let Context {
            modulus,
            num_traits,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[parse_quote!(Division)], &generics);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let (struct_update, struct_update_deref) = self.struct_update(
            parse_quote!(inv),
            &[parse_quote!(self.#field_ident), modulus.clone()],
        );

        quote! {
            impl#impl_generics #num_traits::Inv for #struct_ident#ty_generics
            #where_clause
            {
                type Output = #struct_ident#ty_generics;

                #[inline]
                fn inv(self) -> #struct_ident#ty_generics {
                    #struct_update
                }
            }

            impl#impl_generics #num_traits::Inv for &'_ #struct_ident#ty_generics
            #where_clause
            {
                type Output = #struct_ident#ty_generics;

                #[inline]
                fn inv(self) -> #struct_ident#ty_generics {
                    #struct_update_deref
                }
            }
        }
    }

    pub(crate) fn derive_checked_neg(&self) -> proc_macro2::TokenStream {
        let Context {
            modulus,
            std,
            num_traits,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[parse_quote!(Subtraction)], &generics);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let (_, update) = self.struct_update_option(
            parse_quote!(checked_neg),
            &[parse_quote!(self.#field_ident), parse_quote!(#modulus)],
        );

        quote! {
            impl#impl_generics #num_traits::CheckedNeg for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn checked_neg(&self) -> #std::option::Option<Self> #update
            }
        }
    }

    pub(crate) fn derive_checked_add(&self) -> proc_macro2::TokenStream {
        self.derive_checked_bin(
            parse_quote!(CheckedAdd),
            parse_quote!(checked_add),
            parse_quote!(Addition),
        )
    }

    pub(crate) fn derive_checked_sub(&self) -> proc_macro2::TokenStream {
        self.derive_checked_bin(
            parse_quote!(CheckedSub),
            parse_quote!(checked_sub),
            parse_quote!(Subtraction),
        )
    }

    pub(crate) fn derive_checked_mul(&self) -> proc_macro2::TokenStream {
        self.derive_checked_bin(
            parse_quote!(CheckedMul),
            parse_quote!(checked_mul),
            parse_quote!(Multiplication),
        )
    }

    pub(crate) fn derive_checked_div(&self) -> proc_macro2::TokenStream {
        self.derive_checked_bin(
            parse_quote!(CheckedDiv),
            parse_quote!(checked_div),
            parse_quote!(Division),
        )
    }

    pub(crate) fn derive_checked_rem(&self) -> proc_macro2::TokenStream {
        self.derive_checked_bin(
            parse_quote!(CheckedRem),
            parse_quote!(checked_rem),
            parse_quote!(Division),
        )
    }

    fn derive_checked_bin(
        &self,
        trait_ident: Ident,
        method: Ident,
        feature: Ident,
    ) -> proc_macro2::TokenStream {
        let Context {
            modulus,
            std,
            num_traits,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[feature], &generics);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let (_, update) = self.struct_update_option(
            method.clone(),
            &[
                parse_quote!(self.#field_ident),
                parse_quote!(rhs.#field_ident),
                parse_quote!(#modulus),
            ],
        );

        quote! {
            impl#impl_generics #num_traits::#trait_ident for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn #method(&self, rhs: &Self) -> #std::option::Option<Self> #update
            }
        }
    }
}
