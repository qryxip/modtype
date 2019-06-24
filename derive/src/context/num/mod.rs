mod bigint;
mod integer;
mod traits;

use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_num(&self) -> proc_macro::TokenStream {
        let Self {
            std,
            num_traits,
            struct_ident,
            generics,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl#impl_generics #num_traits::Num for #struct_ident#ty_generics
            #where_clause
            {
                type FromStrRadixErr = <#field_ty as #num_traits::Num>::FromStrRadixErr;

                #[inline]
                fn from_str_radix(
                    str: &str,
                    radix: u32,
                ) -> #std::result::Result<Self, <#field_ty as #num_traits::Num>::FromStrRadixErr> {
                    let value = <#field_ty as #num_traits::Num>::from_str_radix(str, radix)?;
                    Ok(<Self as #std::convert::From<#field_ty>>::from(value))
                }
            }
        )
        .into()
    }
}
