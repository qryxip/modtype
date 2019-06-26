use crate::context::Context;

use quote::quote;
use syn::{parse_quote, BinOp, Expr, Ident, Type};

impl Context {
    pub(crate) fn derive_inv(&self) -> proc_macro::TokenStream {
        let Context {
            std,
            num_traits,
            inv,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let derive = |ty: Type| -> _ {
            let struct_update = if let Type::Reference(_) = &ty {
                self.struct_update(false, parse_quote!(*self))
            } else {
                self.struct_update(true, parse_quote!(self))
            };

            quote! {
                impl#impl_generics #num_traits::Inv for #ty
                    #where_clause
                {
                    type Output = #struct_ident#ty_generics;

                    #[inline]
                    fn inv(self) -> #struct_ident#ty_generics {
                        fn static_assert_copy<T: #std::marker::Copy>() {}
                        static_assert_copy::<#struct_ident#ty_generics>();

                        let #field_ident = <#field_ty as #num_traits::One>::one();
                        let one = #struct_update;
                        one / self
                    }
                }
            }
        };

        let mut ret = derive(parse_quote!(#struct_ident#ty_generics));
        if inv.for_ref {
            ret.extend(derive(parse_quote!(&'_ #struct_ident#ty_generics)));
        }
        ret.into()
    }

    pub(crate) fn derive_checked_neg(&self) -> proc_macro::TokenStream {
        let Context {
            std,
            num_traits,
            struct_ident,
            generics,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl#impl_generics #num_traits::CheckedNeg for #struct_ident#ty_generics
                #where_clause
            {
                #[inline]
                fn checked_neg(&self) -> #std::option::Option<Self> {
                    fn static_assert_copy<T: #std::marker::Copy>() {}
                    static_assert_copy::<Self>();
                    Some(-*self)
                }
            }
        )
        .into()
    }

    pub(crate) fn derive_checked_add(&self) -> proc_macro::TokenStream {
        self.derive_checked_bin(
            parse_quote!(CheckedAdd),
            parse_quote!(checked_add),
            false,
            parse_quote!(+),
        )
    }

    pub(crate) fn derive_checked_sub(&self) -> proc_macro::TokenStream {
        self.derive_checked_bin(
            parse_quote!(CheckedSub),
            parse_quote!(checked_sub),
            false,
            parse_quote!(-),
        )
    }

    pub(crate) fn derive_checked_mul(&self) -> proc_macro::TokenStream {
        self.derive_checked_bin(
            parse_quote!(CheckedMul),
            parse_quote!(checked_mul),
            false,
            parse_quote!(*),
        )
    }

    pub(crate) fn derive_checked_div(&self) -> proc_macro::TokenStream {
        self.derive_checked_bin(
            parse_quote!(CheckedDiv),
            parse_quote!(checked_div),
            true,
            parse_quote!(/),
        )
    }

    pub(crate) fn derive_checked_rem(&self) -> proc_macro::TokenStream {
        self.derive_checked_bin(
            parse_quote!(CheckedRem),
            parse_quote!(checked_rem),
            true,
            parse_quote!(%),
        )
    }

    fn derive_checked_bin(
        &self,
        trait_ident: Ident,
        fn_ident: Ident,
        return_none_if_rhs_is_zero: bool,
        op: BinOp,
    ) -> proc_macro::TokenStream {
        let Context {
            std,
            num_traits,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let expr: Expr = if return_none_if_rhs_is_zero {
            parse_quote! {
                if <#field_ty as #num_traits::Zero>::is_zero(&rhs.#field_ident) {
                    None
                } else {
                    Some(*self #op *rhs)
                }
            }
        } else {
            parse_quote!(Some(*self #op *rhs))
        };

        quote!(
            impl#impl_generics #num_traits::#trait_ident for #struct_ident#ty_generics
                #where_clause
            {
                #[inline]
                fn #fn_ident(&self, rhs: &Self) -> #std::option::Option<Self> {
                    fn static_assert_copy<T: #std::marker::Copy>() {}
                    static_assert_copy::<Self>();
                    #expr
                }
            }
        )
        .into()
    }
}
