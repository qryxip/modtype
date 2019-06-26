use crate::context::Context;

use quote::quote;
use syn::{parse_quote, Path};

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

        let derive = |exp: &Path, signed: bool, base_ref: bool, exp_ref: bool| -> _ {
            let (base, base_star_token) = if base_ref {
                (quote!(&'_ #struct_ident#ty_generics), quote!(*))
            } else {
                (quote!(#struct_ident#ty_generics), quote!())
            };

            let (exp, exp_star_token) = if exp_ref {
                (quote!(&'_ #exp), quote!(*))
            } else {
                (quote!(#exp), quote!())
            };

            let on_signed_pre = if signed {
                quote! {
                    let neg = exp < 0;
                    if neg {
                        exp = -exp;
                    }
                }
            } else {
                quote!()
            };

            let on_signed_post = if signed {
                quote! {
                    if neg {
                        acc = <#struct_ident#ty_generics as #num_traits::Inv>::inv(acc);
                    }
                }
            } else {
                quote!()
            };

            quote! {
                impl#impl_generics #num_traits::Pow<#exp> for #base
                #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    fn pow(self, exp: #exp) -> #struct_ident#ty_generics {
                        fn static_assert_copy<T: #std::marker::Copy>() {}
                        static_assert_copy::<#struct_ident#ty_generics>();

                        let mut base = #base_star_token self;
                        let mut exp = #exp_star_token exp;
                        let mut acc = #base_star_token self;
                        acc.#field_ident = <#field_ty as #num_traits::One>::one();

                        #on_signed_pre

                        while exp > 0 {
                            if (exp & 0x1) == 0x1 {
                                acc *= base;
                            }
                            exp /= 2;
                            base *= base;
                        }

                        #on_signed_post

                        acc
                    }
                }
            }
        };

        let mut ret = quote!();

        for exp in &[
            parse_quote!(u8),
            parse_quote!(u16),
            parse_quote!(u32),
            parse_quote!(u64),
            parse_quote!(u128),
            parse_quote!(usize),
        ] {
            ret.extend(derive(exp, false, false, false));
            if pow.for_ref {
                ret.extend(derive(exp, false, false, true));
                ret.extend(derive(exp, false, true, false));
                ret.extend(derive(exp, false, true, true));
            }
        }

        for exp in &[
            parse_quote!(i8),
            parse_quote!(i16),
            parse_quote!(i32),
            parse_quote!(i64),
            parse_quote!(i128),
            parse_quote!(isize),
        ] {
            ret.extend(derive(exp, true, false, false));
            if pow.for_ref {
                ret.extend(derive(exp, true, false, true));
                ret.extend(derive(exp, true, true, false));
                ret.extend(derive(exp, true, true, true));
            }
        }

        ret.into()
    }
}
