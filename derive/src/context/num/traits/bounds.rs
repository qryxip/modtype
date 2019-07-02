use crate::context::Context;

use quote::quote;
use syn::parse_quote;

impl Context {
    pub(crate) fn derive_bounded(&self) -> proc_macro2::TokenStream {
        if self.non_static_modulus {
            return quote!();
        }

        let Self {
            modulus,
            implementation,
            num_traits,
            modtype,
            struct_ident,
            generics,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let min_value = parse_quote!(<#implementation as #modtype::Impl>::min_value(#modulus));
        let min_value = self.struct_expr(true, Some(min_value));
        let max_value = parse_quote!(<#implementation as #modtype::Impl>::max_value(#modulus));
        let max_value = self.struct_expr(true, Some(max_value));

        quote! {
            impl#impl_generics #num_traits::Bounded for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn min_value() -> Self {
                    #min_value
                }

                #[inline]
                fn max_value() -> Self {
                    #max_value
                }
            }
        }
    }
}
