use crate::context::{Context, OpOptions};

use quote::quote;
use syn::{parse_quote, BinOp, Expr, Ident, ImplGenerics, ItemFn, Type};

impl Context {
    pub(crate) fn derive_deref(&self) -> proc_macro::TokenStream {
        let Context {
            std,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl#impl_generics #std::ops::Deref for #struct_ident#ty_generics
            #where_clause
            {
                type Target = #field_ty;

                #[inline]
                fn deref(&self) -> &#field_ty {
                    &self.#field_ident
                }
            }
        )
        .into()
    }

    pub(crate) fn derive_neg(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            std,
            neg,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let derive = |lhs_ty: Type| {
            let struct_update = if let Type::Reference(_) = &lhs_ty {
                self.struct_update(false, parse_quote!(*self))
            } else {
                self.struct_update(false, parse_quote!(self))
            };

            quote! {
                impl#impl_generics #std::ops::Neg for #lhs_ty
                #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    #[inline]
                    fn neg(self) -> #struct_ident#ty_generics {
                        fn static_assert_add<O, L: #std::ops::Add<L, Output = O>>() {}
                        fn static_assert_sub<O, L: #std::ops::Sub<L, Output = O>>() {}
                        static_assert_add::<#struct_ident#ty_generics, Self>();
                        static_assert_sub::<#struct_ident#ty_generics, Self>();
                        let #field_ident = (#modulus) - self.#field_ident;
                        #struct_update
                    }
                }
            }
        };

        let mut ret = derive(parse_quote!(#struct_ident#ty_generics));
        if neg.for_ref {
            ret.extend(derive(parse_quote!(&'_ #struct_ident#ty_generics)))
        }
        ret.into()
    }

    pub(crate) fn derive_add(&self) -> proc_macro::TokenStream {
        self.derive_bin_almost_transparent(
            parse_quote!(Add),
            parse_quote!(add),
            |l, r, _| parse_quote!(#l + #r),
            self.add,
        )
    }

    pub(crate) fn derive_add_assign(&self) -> proc_macro::TokenStream {
        self.derive_bin_assign(
            parse_quote!(AddAssign),
            parse_quote!(add_assign),
            parse_quote!(+),
            self.add_assign,
        )
    }

    pub(crate) fn derive_sub(&self) -> proc_macro::TokenStream {
        self.derive_bin_almost_transparent(
            parse_quote!(Sub),
            parse_quote!(sub),
            |l, r, m| parse_quote!(#m + #l - #r),
            self.sub,
        )
    }

    pub(crate) fn derive_sub_assign(&self) -> proc_macro::TokenStream {
        self.derive_bin_assign(
            parse_quote!(SubAssign),
            parse_quote!(sub_assign),
            parse_quote!(-),
            self.sub_assign,
        )
    }

    pub(crate) fn derive_mul(&self) -> proc_macro::TokenStream {
        self.derive_bin_almost_transparent(
            parse_quote!(Mul),
            parse_quote!(mul),
            |l, r, _| parse_quote!(#l * #r),
            self.mul,
        )
    }

    pub(crate) fn derive_mul_assign(&self) -> proc_macro::TokenStream {
        self.derive_bin_assign(
            parse_quote!(MulAssign),
            parse_quote!(mul_assign),
            parse_quote!(*),
            self.mul_assign,
        )
    }

    pub(crate) fn derive_div(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            std,
            num_traits,
            div,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (_, ty_generics, _) = generics.split_for_impl();

        self.derive_bin(parse_quote!(Div), *div, |lhs_is_ref, rhs_ty| {
            let struct_update = if lhs_is_ref {
                self.struct_update(false, parse_quote!(*self))
            } else {
                self.struct_update(false, parse_quote!(self))
            };

            parse_quote! {
                fn div(self, rhs: #rhs_ty) -> #struct_ident#ty_generics {
                    fn static_assert_copy<T: #std::marker::Copy>() {}
                    static_assert_copy::<#struct_ident#ty_generics>();

                    fn extended_gcd(a: i128, b: i128) -> (i128, i128, i128) {
                        if a == 0 {
                            (b, 0, 1)
                        } else {
                            let (d, u, v) = extended_gcd(b % a, a);
                            (d, v - (b / a) * u, u)
                        }
                    }

                    let lhs = <#field_ty as #num_traits::ToPrimitive>::to_i128(&self.#field_ident);
                    let lhs = #std::option::Option::expect(lhs, "could not convert to `i128`");
                    let rhs = <#field_ty as #num_traits::ToPrimitive>::to_i128(&rhs.#field_ident);
                    let rhs = #std::option::Option::expect(rhs, "could not convert to `i128`");
                    let modulus = <#field_ty as #num_traits::ToPrimitive>::to_i128(&#modulus);
                    let modulus =
                        #std::option::Option::expect(modulus, "could not convert to `i128`");
                    if rhs == 0 {
                        panic!("attempt to divide by zero");
                    }
                    let (d, u, _) = extended_gcd(rhs, modulus);
                    if rhs % d != 0 {
                        panic!("RHS is not a multiple of gcd({}, {})", rhs, modulus);
                    }
                    let mut #field_ident = (lhs * u) % modulus;
                    if #field_ident < 0 {
                        #field_ident += modulus;
                    }
                    let #field_ident =
                        <#field_ty as #num_traits::FromPrimitive>::from_i128(#field_ident);
                    let #field_ident = #std::option::Option::unwrap(#field_ident);
                    #struct_update
                }
            }
        })
    }

    pub(crate) fn derive_div_assign(&self) -> proc_macro::TokenStream {
        self.derive_bin_assign(
            parse_quote!(DivAssign),
            parse_quote!(div_assign),
            parse_quote!(/),
            self.div_assign,
        )
    }

    pub(crate) fn derive_rem(&self) -> proc_macro::TokenStream {
        let Context {
            std,
            rem,
            num_traits,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (_, ty_generics, _) = generics.split_for_impl();

        self.derive_bin(parse_quote!(Rem), *rem, |lhs_is_ref, rhs_ty| {
            let struct_update = if lhs_is_ref {
                self.struct_update(false, parse_quote!(*self))
            } else {
                self.struct_update(false, parse_quote!(self))
            };

            parse_quote! {
                fn rem(self, rhs: #rhs_ty) -> #struct_ident#ty_generics {
                    fn static_assert_copy<T: #std::marker::Copy>() {}
                    static_assert_copy::<#struct_ident#ty_generics>();

                    if <#field_ty as #num_traits::Zero>::is_zero(&rhs.#field_ident) {
                        panic!("attempt to calculate the remainder with a divisor of zero")
                    }
                    let #field_ident = <#field_ty as #num_traits::Zero>::zero();
                    #struct_update
                }
            }
        })
    }

    pub(crate) fn derive_rem_assign(&self) -> proc_macro::TokenStream {
        self.derive_bin_assign(
            parse_quote!(RemAssign),
            parse_quote!(rem_assign),
            parse_quote!(%),
            self.rem_assign,
        )
    }

    fn derive_bin_almost_transparent(
        &self,
        trait_ident: Ident,
        fn_ident: Ident,
        op: fn(&Expr, &Expr, &Expr) -> Expr,
        opts: OpOptions,
    ) -> proc_macro::TokenStream {
        let Context {
            modulus,
            std,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;

        let (_, ty_generics, _) = generics.split_for_impl();

        let expr = op(
            &parse_quote!(self.#field_ident),
            &parse_quote!(rhs.#field_ident),
            &modulus,
        );

        self.derive_bin(trait_ident, opts, |lhs_is_ref, rhs_ty| {
            let struct_update = if lhs_is_ref {
                self.struct_update(false, parse_quote!(*self))
            } else {
                self.struct_update(false, parse_quote!(self))
            };

            parse_quote! {
                #[inline]
                fn #fn_ident(self, rhs: #rhs_ty) -> #struct_ident#ty_generics {
                    fn static_assert_copy<T: #std::marker::Copy>() {}
                    static_assert_copy::<#struct_ident#ty_generics>();

                    let mut #field_ident = #expr;
                    if #field_ident >= #modulus {
                        #field_ident %= #modulus;
                    }
                    #struct_update
                }
            }
        })
    }

    fn derive_bin(
        &self,
        trait_ident: Ident,
        opts: OpOptions,
        derive_fn: impl Fn(bool, &Type) -> ItemFn,
    ) -> proc_macro::TokenStream {
        let Context {
            std,
            struct_ident,
            generics,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let derive = |impl_generics: &ImplGenerics, lhs_ty: Type, rhs_ty: Type| -> _ {
            let lhs_is_ref = match &lhs_ty {
                Type::Reference(_) => true,
                _ => false,
            };
            let item_fn = derive_fn(lhs_is_ref, &rhs_ty);
            quote! {
                impl#impl_generics #std::ops::#trait_ident<#rhs_ty> for #lhs_ty
                #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    #item_fn
                }
            }
        };

        let mut ret = derive(
            &impl_generics,
            parse_quote!(#struct_ident#ty_generics),
            parse_quote!(#struct_ident#ty_generics),
        );

        if opts.for_ref {
            ret.extend(derive(
                &impl_generics,
                parse_quote!(&'_ #struct_ident#ty_generics),
                parse_quote!(#struct_ident#ty_generics),
            ));

            ret.extend(derive(
                &impl_generics,
                parse_quote!(#struct_ident#ty_generics),
                parse_quote!(&'_ #struct_ident#ty_generics),
            ));

            ret.extend(derive(
                &impl_generics,
                parse_quote!(&'_ #struct_ident#ty_generics),
                parse_quote!(&'_ #struct_ident#ty_generics),
            ));
        }

        ret.into()
    }

    fn derive_bin_assign(
        &self,
        trait_ident: Ident,
        fn_ident: Ident,
        bin_op: BinOp,
        opts: OpOptions,
    ) -> proc_macro::TokenStream {
        let Context {
            std,
            struct_ident,
            generics,
            ..
        } = &self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let derive = |rhs_ty: Type, rhs_deref: bool| -> _ {
            let star_token = if rhs_deref { quote!(*) } else { quote!() };
            quote! {
                impl#impl_generics #std::ops::#trait_ident<#rhs_ty> for #struct_ident#ty_generics
                #where_clause
                {
                    #[inline]
                    fn #fn_ident(&mut self, rhs: #rhs_ty) {
                        fn static_assert_copy<T: #std::marker::Copy>() {}
                        static_assert_copy::<Self>();
                        *self = *self #bin_op #star_token rhs;
                    }
                }
            }
        };

        let mut ret = derive(parse_quote!(Self), false);
        if opts.for_ref {
            ret.extend(derive(parse_quote!(&'_ Self), true));
        }
        ret.into()
    }
}
