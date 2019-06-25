use crate::context::Context;

use quote::quote;
use syn::{parse_quote, Type};

impl Context {
    pub(crate) fn derive_pow(&self) -> proc_macro::TokenStream {
        let Context {
            std,
            num_traits,
            pow,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let mut tys: Vec<(Type, Type)> = vec![
            (parse_quote!(#struct_ident#ty_generics), parse_quote!(u8)),
            (parse_quote!(#struct_ident#ty_generics), parse_quote!(u16)),
            (parse_quote!(#struct_ident#ty_generics), parse_quote!(u32)),
            (parse_quote!(#struct_ident#ty_generics), parse_quote!(u64)),
            (parse_quote!(#struct_ident#ty_generics), parse_quote!(u128)),
            (parse_quote!(#struct_ident#ty_generics), parse_quote!(usize)),
        ];

        if pow.for_ref {
            tys.extend(vec![
                (
                    parse_quote!(#struct_ident#ty_generics),
                    parse_quote!(&'_ u8),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(u8),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(&'_ u8),
                ),
                (
                    parse_quote!(#struct_ident#ty_generics),
                    parse_quote!(&'_ u16),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(u16),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(&'_ u16),
                ),
                (
                    parse_quote!(#struct_ident#ty_generics),
                    parse_quote!(&'_ u32),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(u32),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(&'_ u32),
                ),
                (
                    parse_quote!(#struct_ident#ty_generics),
                    parse_quote!(&'_ u64),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(u64),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(&'_ u64),
                ),
                (
                    parse_quote!(#struct_ident#ty_generics),
                    parse_quote!(&'_ u128),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(u128),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(&'_ u128),
                ),
                (
                    parse_quote!(#struct_ident#ty_generics),
                    parse_quote!(&'_ usize),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(usize),
                ),
                (
                    parse_quote!(&'_ #struct_ident#ty_generics),
                    parse_quote!(&'_ usize),
                ),
            ]);
        }

        let mut ret = quote!();
        for (base_ty, exp_ty) in tys {
            let base_star_token = if let Type::Reference(_) = base_ty {
                quote!(*)
            } else {
                quote!()
            };

            let exp_star_token = if let Type::Reference(_) = exp_ty {
                quote!(*)
            } else {
                quote!()
            };

            ret.extend(quote! {
                impl#impl_generics #num_traits::Pow<#exp_ty> for #base_ty
                    #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    #[inline]
                    fn pow(self, exp: #exp_ty) -> #struct_ident#ty_generics {
                        fn static_assert_copy<T: #std::marker::Copy>() {}
                        static_assert_copy::<#struct_ident#ty_generics>();

                        let mut base = #base_star_token self;
                        let mut exp = #exp_star_token exp;
                        let mut acc = #base_star_token self;
                        acc.#field_ident = <#field_ty as #num_traits::One>::one();

                        while exp > 0 {
                            if (exp & 0x1) == 0x1 {
                                acc *= base;
                            }
                            exp /= 2;
                            base *= base;
                        }

                        acc
                    }
                }
            });
        }
        ret.into()
    }
}
