use crate::context::Context;

use quote::quote;
use syn::{parse_quote, Ident};

impl Context {
    pub(crate) fn derive_pow(&self) -> proc_macro2::TokenStream {
        let Context {
            modulus,
            num_traits,
            struct_ident,
            field_ident,
            ..
        } = self;

        let generics = self.with_features(&[parse_quote!(PartialMultiplication)]);
        let (impl_generics, ty_generics, unsigned) = generics.split_for_impl();
        let generics = self.with_features(&[
            parse_quote!(PartialMultiplication),
            parse_quote!(PartialDivision),
        ]);
        let (_, _, signed) = generics.split_for_impl();

        let mut acc = quote!();

        let trios: &[(Ident, Ident, _)] = &[
            (parse_quote!(u8), parse_quote!(pow_unsigned), unsigned),
            (parse_quote!(u16), parse_quote!(pow_unsigned), unsigned),
            (parse_quote!(u32), parse_quote!(pow_unsigned), unsigned),
            (parse_quote!(u64), parse_quote!(pow_unsigned), unsigned),
            (parse_quote!(u128), parse_quote!(pow_unsigned), unsigned),
            (parse_quote!(usize), parse_quote!(pow_unsigned), unsigned),
            (parse_quote!(i8), parse_quote!(pow_signed), signed),
            (parse_quote!(i16), parse_quote!(pow_signed), signed),
            (parse_quote!(i32), parse_quote!(pow_signed), signed),
            (parse_quote!(i64), parse_quote!(pow_signed), signed),
            (parse_quote!(i128), parse_quote!(pow_signed), signed),
            (parse_quote!(isize), parse_quote!(pow_signed), signed),
        ];

        for (exp, method, where_clause) in trios {
            let (update_c_c, update_r_c) = self.struct_update(
                method.clone(),
                &[
                    parse_quote!(self.#field_ident),
                    parse_quote!(exp),
                    modulus.clone(),
                ],
            );
            let (update_c_r, update_r_r) = self.struct_update(
                method.clone(),
                &[
                    parse_quote!(self.#field_ident),
                    parse_quote!(*exp),
                    modulus.clone(),
                ],
            );

            acc.extend(quote! {
                impl#impl_generics #num_traits::Pow<#exp> for #struct_ident#ty_generics
                #where_clause
                {
                    type Output = Self;

                    #[inline]
                    fn pow(self, exp: #exp) -> Self {
                        #update_c_c
                    }
                }

                impl#impl_generics #num_traits::Pow<&'_ #exp> for #struct_ident#ty_generics
                #where_clause
                {
                    type Output = Self;

                    #[inline]
                    fn pow(self, exp: &'_ #exp) -> Self {
                        #update_c_r
                    }
                }

                impl#impl_generics #num_traits::Pow<#exp> for &'_ #struct_ident#ty_generics
                #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    #[inline]
                    fn pow(self, exp: #exp) -> #struct_ident#ty_generics {
                        #update_r_c
                    }
                }

                impl#impl_generics #num_traits::Pow<&'_ #exp> for &'_ #struct_ident#ty_generics
                #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    #[inline]
                    fn pow(self, exp: &'_ #exp) -> #struct_ident#ty_generics {
                        #update_r_r
                    }
                }
            });
        }
        acc
    }
}
