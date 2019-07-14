use crate::context::Context;

use quote::quote;
use syn::{parse_quote, Ident};

impl Context {
    pub(crate) fn derive_deref(&self) -> proc_macro2::TokenStream {
        let Context {
            std,
            struct_ident,
            field_ident,
            field_ty,
            ..
        } = self;
        let generics = self.with_features(&[parse_quote!(Deref)]);
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
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[parse_quote!(PartialSubtraction)]);
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
        self.derive_bin(
            parse_quote!(Add),
            parse_quote!(add),
            parse_quote!(PartialAddition),
        )
    }

    pub(crate) fn derive_add_assign(&self) -> proc_macro2::TokenStream {
        self.derive_bin_assign(
            parse_quote!(AddAssign),
            parse_quote!(add_assign),
            parse_quote!(add),
            parse_quote!(PartialAddition),
        )
    }

    pub(crate) fn derive_sub(&self) -> proc_macro2::TokenStream {
        self.derive_bin(
            parse_quote!(Sub),
            parse_quote!(sub),
            parse_quote!(PartialSubtraction),
        )
    }

    pub(crate) fn derive_sub_assign(&self) -> proc_macro2::TokenStream {
        self.derive_bin_assign(
            parse_quote!(SubAssign),
            parse_quote!(sub_assign),
            parse_quote!(sub),
            parse_quote!(PartialSubtraction),
        )
    }

    pub(crate) fn derive_mul(&self) -> proc_macro2::TokenStream {
        self.derive_bin(
            parse_quote!(Mul),
            parse_quote!(mul),
            parse_quote!(PartialMultiplication),
        )
    }

    pub(crate) fn derive_mul_assign(&self) -> proc_macro2::TokenStream {
        self.derive_bin_assign(
            parse_quote!(MulAssign),
            parse_quote!(mul_assign),
            parse_quote!(mul),
            parse_quote!(PartialMultiplication),
        )
    }

    pub(crate) fn derive_div(&self) -> proc_macro2::TokenStream {
        self.derive_bin(
            parse_quote!(Div),
            parse_quote!(div),
            parse_quote!(PartialDivision),
        )
    }

    pub(crate) fn derive_div_assign(&self) -> proc_macro2::TokenStream {
        self.derive_bin_assign(
            parse_quote!(DivAssign),
            parse_quote!(div_assign),
            parse_quote!(div),
            parse_quote!(PartialDivision),
        )
    }

    pub(crate) fn derive_rem(&self) -> proc_macro2::TokenStream {
        self.derive_bin(
            parse_quote!(Rem),
            parse_quote!(rem),
            parse_quote!(PartialDivision),
        )
    }

    pub(crate) fn derive_rem_assign(&self) -> proc_macro2::TokenStream {
        self.derive_bin_assign(
            parse_quote!(RemAssign),
            parse_quote!(rem_assign),
            parse_quote!(rem),
            parse_quote!(PartialDivision),
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
            cartridge,
            std,
            num_bigint,
            num_rational,
            modtype,
            struct_ident,
            field_ident,
            other_fields,
            ..
        } = self;

        let generics = self.with_features(&[feature.clone()]);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let (struct_update, struct_update_deref) = self.struct_update(
            method.clone(),
            &[
                parse_quote!(self.#field_ident),
                parse_quote!(rhs.#field_ident),
                modulus.clone(),
            ],
        );

        let mut acc = quote! {
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
        };

        let generics = self.with_features(&[feature.clone(), parse_quote!(FlexibleRhs)]);
        let (_, _, where_clause) = generics.split_for_impl();

        let generics = self.with_features(&[
            feature.clone(),
            parse_quote!(PartialSubtraction),
            parse_quote!(FlexibleRhs),
        ]);
        let (_, _, where_clause_sub) = generics.split_for_impl();

        let generics = self.with_features(&[
            feature.clone(),
            parse_quote!(AssumePrimeModulus),
            parse_quote!(PartialDivision),
            parse_quote!(FlexibleRhs),
        ]);
        let (_, _, where_clause_div) = generics.split_for_impl();

        let generics = self.with_features(&[
            feature.clone(),
            parse_quote!(AssumePrimeModulus),
            parse_quote!(PartialSubtraction),
            parse_quote!(PartialDivision),
            parse_quote!(FlexibleRhs),
        ]);
        let (_, _, where_clause_sub_div) = generics.split_for_impl();

        let generics = self.with_features(&[
            feature.clone(),
            parse_quote!(AssumePrimeModulus),
            parse_quote!(PartialSubtraction),
            parse_quote!(PartialMultiplication),
            parse_quote!(PartialDivision),
            parse_quote!(FlexibleRhs),
        ]);
        let (_, _, where_clause_sub_mul_div) = generics.split_for_impl();

        for (rhs_ty, convert, where_clause) in &[
            (quote!(u8), quote!(from_u8), where_clause),
            (quote!(u16), quote!(from_u16), where_clause),
            (quote!(u32), quote!(from_u32), where_clause),
            (quote!(u64), quote!(from_u64), where_clause),
            (quote!(u128), quote!(from_u128), where_clause),
            (quote!(usize), quote!(from_usize), where_clause),
            (quote!(i8), quote!(from_i8), where_clause_sub),
            (quote!(i16), quote!(from_i16), where_clause_sub),
            (quote!(i32), quote!(from_i32), where_clause_sub),
            (quote!(i64), quote!(from_i64), where_clause_sub),
            (quote!(i128), quote!(from_i128), where_clause_sub),
            (quote!(isize), quote!(from_isize), where_clause_sub),
            (
                quote!(f32),
                quote!(from_float_prim),
                where_clause_sub_mul_div,
            ),
            (
                quote!(f64),
                quote!(from_float_prim),
                where_clause_sub_mul_div,
            ),
            (
                quote!(#num_bigint::BigUint),
                quote!(from_biguint),
                where_clause,
            ),
            (
                quote!(#num_bigint::BigInt),
                quote!(from_bigint),
                where_clause_sub,
            ),
            (
                quote!(#num_rational::Ratio<#num_bigint::BigUint>),
                quote!(from_biguint_ratio),
                where_clause_div,
            ),
            (
                quote!(#num_rational::Ratio<#num_bigint::BigInt>),
                quote!(from_bigint_ratio),
                where_clause_sub_div,
            ),
        ] {
            let value_rhs_move = quote! {
                <#cartridge as #modtype::Cartridge>::#method(
                    self.#field_ident,
                    <#cartridge as #modtype::Cartridge>::#convert(rhs, #modulus),
                    #modulus,
                )
            };
            let value_rhs_clone = quote! {
                <#cartridge as #modtype::Cartridge>::#method(
                    self.#field_ident,
                    <#cartridge as #modtype::Cartridge>::#convert(
                        <#rhs_ty as #std::clone::Clone>::clone(rhs),
                        #modulus
                    ),
                    #modulus,
                )
            };

            let (update_move_move, update_move_clone, update_deref_move, update_deref_clone) =
                if other_fields.is_empty() {
                    (
                        quote!(#struct_ident { #field_ident: #value_rhs_move }),
                        quote!(#struct_ident { #field_ident: #value_rhs_clone }),
                        quote!(#struct_ident { #field_ident: #value_rhs_move }),
                        quote!(#struct_ident { #field_ident: #value_rhs_clone }),
                    )
                } else {
                    (
                        quote!(#struct_ident { #field_ident: #value_rhs_move, ..self }),
                        quote!(#struct_ident { #field_ident: #value_rhs_clone, ..self }),
                        quote!(#struct_ident { #field_ident: #value_rhs_move, ..*self }),
                        quote!(#struct_ident { #field_ident: #value_rhs_clone, ..*self }),
                    )
                };

            acc.extend(quote! {
                impl #impl_generics #std::ops::#trait_ident<#rhs_ty> for #struct_ident#ty_generics
                #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    #[inline]
                    fn #method(self, rhs: #rhs_ty) -> #struct_ident#ty_generics {
                        #update_move_move
                    }
                }

                impl
                    #impl_generics
                #std::ops::#trait_ident<&'_ #rhs_ty> for #struct_ident#ty_generics
                #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    #[inline]
                    fn #method(self, rhs: &'_ #rhs_ty) -> #struct_ident#ty_generics {
                        #update_move_clone
                    }
                }

                impl
                    #impl_generics
                #std::ops::#trait_ident<#rhs_ty> for &'_ #struct_ident#ty_generics
                #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    #[inline]
                    fn #method(self, rhs: #rhs_ty) -> #struct_ident#ty_generics {
                        #update_deref_move
                    }
                }

                impl
                    #impl_generics
                #std::ops::#trait_ident<&'_ #rhs_ty> for &'_ #struct_ident#ty_generics
                #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    #[inline]
                    fn #method(self, rhs: &'_ #rhs_ty) -> #struct_ident#ty_generics {
                        #update_deref_clone
                    }
                }
            });
        }

        acc
    }

    fn derive_bin_assign(
        &self,
        trait_ident: Ident,
        fn_ident: Ident,
        cartridge_method: Ident,
        feature: Ident,
    ) -> proc_macro2::TokenStream {
        let Context {
            modulus,
            cartridge,
            std,
            num_bigint,
            num_rational,
            modtype,
            struct_ident,
            field_ident,
            other_fields,
            ..
        } = &self;
        let generics = self.with_features(&[feature.clone()]);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let (_, update) = self.struct_update(
            cartridge_method.clone(),
            &[
                parse_quote!(self.#field_ident),
                parse_quote!(rhs.#field_ident),
                modulus.clone(),
            ],
        );

        let mut acc = quote! {
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
        };

        let generics = self.with_features(&[feature.clone(), parse_quote!(FlexibleRhs)]);
        let (_, _, where_clause) = generics.split_for_impl();

        let generics = self.with_features(&[
            feature.clone(),
            parse_quote!(PartialSubtraction),
            parse_quote!(FlexibleRhs),
        ]);
        let (_, _, where_clause_sub) = generics.split_for_impl();

        let generics = self.with_features(&[
            feature.clone(),
            parse_quote!(AssumePrimeModulus),
            parse_quote!(PartialDivision),
            parse_quote!(FlexibleRhs),
        ]);
        let (_, _, where_clause_div) = generics.split_for_impl();

        let generics = self.with_features(&[
            feature.clone(),
            parse_quote!(AssumePrimeModulus),
            parse_quote!(PartialSubtraction),
            parse_quote!(PartialDivision),
            parse_quote!(FlexibleRhs),
        ]);
        let (_, _, where_clause_sub_div) = generics.split_for_impl();

        let generics = self.with_features(&[
            feature.clone(),
            parse_quote!(AssumePrimeModulus),
            parse_quote!(PartialSubtraction),
            parse_quote!(PartialMultiplication),
            parse_quote!(PartialDivision),
            parse_quote!(FlexibleRhs),
        ]);
        let (_, _, where_clause_sub_mul_div) = generics.split_for_impl();

        for (rhs_ty, convert, where_clause) in &[
            (quote!(u8), quote!(from_u8), where_clause),
            (quote!(u16), quote!(from_u16), where_clause),
            (quote!(u32), quote!(from_u32), where_clause),
            (quote!(u64), quote!(from_u64), where_clause),
            (quote!(u128), quote!(from_u128), where_clause),
            (quote!(usize), quote!(from_usize), where_clause),
            (quote!(i8), quote!(from_i8), where_clause_sub),
            (quote!(i16), quote!(from_i16), where_clause_sub),
            (quote!(i32), quote!(from_i32), where_clause_sub),
            (quote!(i64), quote!(from_i64), where_clause_sub),
            (quote!(i128), quote!(from_i128), where_clause_sub),
            (quote!(isize), quote!(from_isize), where_clause_sub),
            (
                quote!(f32),
                quote!(from_float_prim),
                where_clause_sub_mul_div,
            ),
            (
                quote!(f64),
                quote!(from_float_prim),
                where_clause_sub_mul_div,
            ),
            (
                quote!(#num_bigint::BigUint),
                quote!(from_biguint),
                where_clause,
            ),
            (
                quote!(#num_bigint::BigInt),
                quote!(from_bigint),
                where_clause_sub,
            ),
            (
                quote!(#num_rational::Ratio<#num_bigint::BigUint>),
                quote!(from_biguint_ratio),
                where_clause_div,
            ),
            (
                quote!(#num_rational::Ratio<#num_bigint::BigInt>),
                quote!(from_bigint_ratio),
                where_clause_sub_div,
            ),
        ] {
            let value_rhs_move = quote! {
                <#cartridge as #modtype::Cartridge>::#cartridge_method(
                    self.#field_ident,
                    <#cartridge as #modtype::Cartridge>::#convert(rhs, #modulus),
                    #modulus,
                )
            };
            let value_rhs_clone = quote! {
                <#cartridge as #modtype::Cartridge>::#cartridge_method(
                    self.#field_ident,
                    <#cartridge as #modtype::Cartridge>::#convert(
                        <#rhs_ty as #std::clone::Clone>::clone(rhs),
                        #modulus
                    ),
                    #modulus,
                )
            };

            let (update_rhs_move, update_rhs_clone) = if other_fields.is_empty() {
                (
                    quote!(#struct_ident { #field_ident: #value_rhs_move }),
                    quote!(#struct_ident { #field_ident: #value_rhs_clone }),
                )
            } else {
                (
                    quote!(#struct_ident { #field_ident: #value_rhs_move, ..*self }),
                    quote!(#struct_ident { #field_ident: #value_rhs_clone, ..*self }),
                )
            };

            acc.extend(quote! {
                impl
                    #impl_generics
                #std::ops::#trait_ident<#rhs_ty> for #struct_ident#ty_generics
                #where_clause
                {
                    #[inline]
                    fn #fn_ident(&mut self, rhs: #rhs_ty) {
                        *self = #update_rhs_move;
                    }
                }

                impl
                    #impl_generics
                #std::ops::#trait_ident<&'_ #rhs_ty> for #struct_ident#ty_generics
                #where_clause
                {
                    #[inline]
                    fn #fn_ident(&mut self, rhs: &'_ #rhs_ty) {
                        *self = #update_rhs_clone;
                    }
                }
            });
        }

        acc
    }
}
