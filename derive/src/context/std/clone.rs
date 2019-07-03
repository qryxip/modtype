use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_clone(&self) -> proc_macro2::TokenStream {
        let Self {
            std,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            other_fields,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let other_tys = other_fields.iter().map(|(_, t)| quote!(#t));
        let other_copies = other_fields.iter().map(|(i, _)| quote!(#i: self.#i));

        quote! {
            #[automatically_derived]
            impl#impl_generics #std::clone::Clone for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn clone(&self) -> Self {
                    fn static_assert_copy<T: #std::marker::Copy>() {}
                    static_assert_copy::<#field_ty>();
                    #(static_assert_copy::<#other_tys>();)*

                    Self {
                        #field_ident: self.#field_ident,
                        #(#other_copies, )*
                    }
                }
            }
        }
    }
}
