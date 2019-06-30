use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_default(&self) -> proc_macro::TokenStream {
        let Self {
            std,
            struct_ident,
            generics,
            field_ident,
            other_fields,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let mut idents = vec![field_ident];
        idents.extend(other_fields.iter().map(|(i, _)| i));

        let mut updates = vec![quote!(#field_ident: #std::default::Default::default())];
        for (ident, _) in other_fields {
            updates.push(quote!(#ident: #std::default::Default::default()));
        }

        quote!(
            #[automatically_derived]
            impl#impl_generics #std::default::Default for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn default() -> Self {
                    Self {
                        #(#updates,)*
                    }
                }
            }
        )
        .into()
    }
}
