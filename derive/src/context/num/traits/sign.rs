use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_unsigned(&self) -> proc_macro::TokenStream {
        let Self {
            num_traits,
            struct_ident,
            generics,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl#impl_generics #num_traits::Unsigned for #struct_ident#ty_generics
            #where_clause {}
        )
        .into()
    }
}