use crate::context::Context;

use quote::quote;
use syn::{parse_quote, Ident};

impl Context {
    pub(crate) fn derive_deref(&self) -> proc_macro2::TokenStream {
        let Context {
            std,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let generics = self.with_features(&[parse_quote!(Deref)], &generics);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote! {
            impl#impl_generics #std::ops::Deref for #struct_ident#ty_generics
            #where_clause
            {
                type Target = #field_ty;

                #[inline]
                fn deref(&self) -> &#field_ty {
                    &self.#field_ident
                }
            }
        }
    }

    pub(crate) fn derive_neg(&self) -> proc_macro2::TokenStream {
        let Context {
            modulus,
            std,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[parse_quote!(Subtraction)], &generics);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let (struct_update, struct_update_deref) = self.struct_update(
            parse_quote!(neg),
            &[parse_quote!(self.#field_ident), modulus.clone()],
        );

        quote! {
            impl#impl_generics #std::ops::Neg for #struct_ident#ty_generics
            #where_clause
            {
                type Output = Self;

                #[inline]
                fn neg(self) -> Self {
                    #struct_update
                }
            }

            impl#impl_generics #std::ops::Neg for &'_ #struct_ident#ty_generics
            #where_clause
            {
                type Output = #struct_ident#ty_generics;

                #[inline]
                fn neg(self) -> #struct_ident#ty_generics {
                    #struct_update_deref
                }
            }
        }
    }

    pub(crate) fn derive_add(&self) -> proc_macro2::TokenStream {
        self.derive_bin(parse_quote!(Add), parse_quote!(add), parse_quote!(Addition))
    }

    pub(crate) fn derive_add_assign(&self) -> proc_macro2::TokenStream {
        self.derive_bin_assign(
            parse_quote!(AddAssign),
            parse_quote!(add_assign),
            parse_quote!(add),
            parse_quote!(Addition),
        )
    }

    pub(crate) fn derive_sub(&self) -> proc_macro2::TokenStream {
        self.derive_bin(
            parse_quote!(Sub),
            parse_quote!(sub),
            parse_quote!(Subtraction),
        )
    }

    pub(crate) fn derive_sub_assign(&self) -> proc_macro2::TokenStream {
        self.derive_bin_assign(
            parse_quote!(SubAssign),
            parse_quote!(sub_assign),
            parse_quote!(sub),
            parse_quote!(Subtraction),
        )
    }

    pub(crate) fn derive_mul(&self) -> proc_macro2::TokenStream {
        self.derive_bin(
            parse_quote!(Mul),
            parse_quote!(mul),
            parse_quote!(Multiplication),
        )
    }

    pub(crate) fn derive_mul_assign(&self) -> proc_macro2::TokenStream {
        self.derive_bin_assign(
            parse_quote!(MulAssign),
            parse_quote!(mul_assign),
            parse_quote!(mul),
            parse_quote!(Multiplication),
        )
    }

    pub(crate) fn derive_div(&self) -> proc_macro2::TokenStream {
        self.derive_bin(parse_quote!(Div), parse_quote!(div), parse_quote!(Division))
    }

    pub(crate) fn derive_div_assign(&self) -> proc_macro2::TokenStream {
        self.derive_bin_assign(
            parse_quote!(DivAssign),
            parse_quote!(div_assign),
            parse_quote!(div),
            parse_quote!(Division),
        )
    }

    pub(crate) fn derive_rem(&self) -> proc_macro2::TokenStream {
        self.derive_bin(parse_quote!(Rem), parse_quote!(rem), parse_quote!(Division))
    }

    pub(crate) fn derive_rem_assign(&self) -> proc_macro2::TokenStream {
        self.derive_bin_assign(
            parse_quote!(RemAssign),
            parse_quote!(rem_assign),
            parse_quote!(rem),
            parse_quote!(Division),
        )
    }

    fn derive_bin(
        &self,
        trait_ident: Ident,
        method: Ident,
        feature: Ident,
    ) -> proc_macro2::TokenStream {
        let Context {
            modulus,
            std,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[feature], &generics);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let (struct_update, struct_update_deref) = self.struct_update(
            method.clone(),
            &[
                parse_quote!(self.#field_ident),
                parse_quote!(rhs.#field_ident),
                modulus.clone(),
            ],
        );

        quote! {
            impl
                #impl_generics
            #std::ops::#trait_ident<#struct_ident#ty_generics> for #struct_ident#ty_generics
            #where_clause
            {
                type Output = #struct_ident#ty_generics;

                #[inline]
                fn #method(self, rhs: #struct_ident#ty_generics) -> #struct_ident#ty_generics {
                    #struct_update
                }
            }

            impl
                #impl_generics
            #std::ops::#trait_ident<&'_ #struct_ident#ty_generics> for #struct_ident#ty_generics
            #where_clause
            {
                type Output = #struct_ident#ty_generics;

                #[inline]
                fn #method(self, rhs: &'_ #struct_ident#ty_generics) -> #struct_ident#ty_generics {
                    #struct_update
                }
            }

            impl
                #impl_generics
            #std::ops::#trait_ident<#struct_ident#ty_generics> for &'_ #struct_ident#ty_generics
            #where_clause
            {
                type Output = #struct_ident#ty_generics;

                #[inline]
                fn #method(self, rhs: #struct_ident#ty_generics) -> #struct_ident#ty_generics {
                    #struct_update_deref
                }
            }

            impl
                #impl_generics
            #std::ops::#trait_ident<&'_ #struct_ident#ty_generics> for &'_ #struct_ident#ty_generics
            #where_clause
            {
                type Output = #struct_ident#ty_generics;

                #[inline]
                fn #method(self, rhs: &'_ #struct_ident#ty_generics) -> #struct_ident#ty_generics {
                    #struct_update_deref
                }
            }
        }
    }

    fn derive_bin_assign(
        &self,
        trait_ident: Ident,
        fn_ident: Ident,
        impl_method: Ident,
        feature: Ident,
    ) -> proc_macro2::TokenStream {
        let Context {
            modulus,
            std,
            struct_ident,
            generics,
            field_ident,
            ..
        } = &self;
        let generics = self.with_features(&[feature], &generics);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let (_, update) = self.struct_update(
            impl_method,
            &[
                parse_quote!(self.#field_ident),
                parse_quote!(rhs.#field_ident),
                modulus.clone(),
            ],
        );

        quote! {
            impl#impl_generics #std::ops::#trait_ident<Self> for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn #fn_ident(&mut self, rhs: Self) {
                    *self = #update;
                }
            }

            impl#impl_generics #std::ops::#trait_ident<&'_ Self> for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn #fn_ident(&mut self, rhs: &'_ Self) {
                    *self = #update;
                }
            }
        }
    }
}
