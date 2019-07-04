use crate::context::Context;

use quote::quote;
use syn::parse_quote;

impl Context {
    pub(crate) fn derive_unsigned(&self) -> proc_macro2::TokenStream {
        if self.non_static_modulus {
            return quote!();
        }

        let Self {
            num_traits,
            struct_ident,
            ..
        } = self;
        let generics = self.with_features(&[
            parse_quote!(AssumePrimeModulus),
            parse_quote!(PartialAddition),
            parse_quote!(PartialSubtraction),
            parse_quote!(PartialMultiplication),
            parse_quote!(PartialDivision),
        ]);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote! {
            impl#impl_generics #num_traits::Unsigned for #struct_ident#ty_generics
            #where_clause {}
        }
    }
}
