use crate::context::Context;

use quote::quote;
use syn::{parse_quote, Type};

impl Context {
    pub(crate) fn derive_pow_u8(&self) -> proc_macro::TokenStream {
        self.derive_pow(parse_quote!(u8))
    }

    pub(crate) fn derive_pow_u16(&self) -> proc_macro::TokenStream {
        self.derive_pow(parse_quote!(u16))
    }

    pub(crate) fn derive_pow_u32(&self) -> proc_macro::TokenStream {
        self.derive_pow(parse_quote!(u32))
    }

    pub(crate) fn derive_pow_u64(&self) -> proc_macro::TokenStream {
        self.derive_pow(parse_quote!(u64))
    }

    pub(crate) fn derive_pow_u128(&self) -> proc_macro::TokenStream {
        self.derive_pow(parse_quote!(u128))
    }

    pub(crate) fn derive_pow_usize(&self) -> proc_macro::TokenStream {
        self.derive_pow(parse_quote!(usize))
    }

    fn derive_pow(&self, exp_ty: Type) -> proc_macro::TokenStream {
        let Context {
            std,
            num_traits,
            no_impl_for_ref,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let derive = |base_ty: &Type, exp_ty: &Type| -> _ {
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

            quote! {
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
            }
        };

        let mut ret = derive(&parse_quote!(#struct_ident#ty_generics), &exp_ty);
        if !no_impl_for_ref {
            ret.extend(derive(
                &parse_quote!(#struct_ident#ty_generics),
                &parse_quote!(&'_ #exp_ty),
            ));
            ret.extend(derive(
                &parse_quote!(&'_ #struct_ident#ty_generics),
                &exp_ty,
            ));
            ret.extend(derive(
                &parse_quote!(&'_ #struct_ident#ty_generics),
                &parse_quote!(&'_ #exp_ty),
            ));
        }
        ret.into()
    }
}
