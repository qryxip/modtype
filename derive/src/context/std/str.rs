use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_from_str(&self) -> proc_macro::TokenStream {
        let Context {
            std,
            struct_ident,
            generics,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl#impl_generics #std::str::FromStr for #struct_ident#ty_generics
            #where_clause
            {
                type Err = <#field_ty as #std::str::FromStr>::Err;

                #[inline]
                fn from_str(
                    s: &str,
                ) -> #std::result::Result<Self, <#field_ty as #std::str::FromStr>::Err> {
                    let value = <#field_ty as #std::str::FromStr>::from_str(s)?;
                    Ok(<Self as #std::convert::From<#field_ty>>::from(value))
                }
            }
        )
        .into()
    }
}
