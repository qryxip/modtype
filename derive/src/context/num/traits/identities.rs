use crate::context::Context;

use quote::quote;
use syn::parse_quote;

impl Context {
    pub(crate) fn derive_zero(&self) -> proc_macro2::TokenStream {
        if self.non_static_modulus {
            return quote!();
        }

        let Context {
            modulus,
            cartridge,
            num_traits,
            modtype,
            struct_ident,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[parse_quote!(PartialAddition)]);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let zero = parse_quote!(<#cartridge as #modtype::Cartridge>::zero(#modulus));
        let zero = self.struct_expr(true, Some(zero));

        quote! {
            impl#impl_generics #num_traits::Zero for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn zero() -> Self {
                    #zero
                }

                #[inline]
                fn is_zero(&self) -> bool {
                    <#cartridge as #modtype::Cartridge>::is_zero(self.#field_ident, #modulus)
                }
            }
        }
    }

    pub(crate) fn derive_one(&self) -> proc_macro2::TokenStream {
        if self.non_static_modulus {
            return quote!();
        }

        let Context {
            modulus,
            cartridge,
            num_traits,
            modtype,
            struct_ident,
            field_ident,
            ..
        } = self;
        let generics =
            self.with_features(&[parse_quote!(Equality), parse_quote!(PartialMultiplication)]);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let one = parse_quote!(<#cartridge as #modtype::Cartridge>::one(#modulus));
        let one = self.struct_expr(true, Some(one));

        quote! {
            impl#impl_generics #num_traits::One for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn one() -> Self {
                    #one
                }

                #[inline]
                fn is_one(&self) -> bool {
                    <#cartridge as #modtype::Cartridge>::is_one(self.#field_ident, #modulus)
                }
            }
        }
    }
}
