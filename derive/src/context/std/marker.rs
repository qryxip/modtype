use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_copy(&self) -> proc_macro::TokenStream {
        let Self {
            std,
            struct_ident,
            generics,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            #[automatically_derived]
            impl#impl_generics #std::marker::Copy for #struct_ident#ty_generics
            #where_clause
            {
            }
        )
        .into()
    }
}
