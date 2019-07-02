use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_from_str(&self) -> proc_macro2::TokenStream {
        if self.non_static_modulus {
            return quote!();
        }

        let Context {
            modulus,
            implementation,
            std,
            modtype,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let struct_expr = self.struct_expr(true, None);

        quote! {
            impl#impl_generics #std::str::FromStr for #struct_ident#ty_generics
            #where_clause
            {
                type Err = #std::num::ParseIntError;

                #[inline]
                fn from_str(s: &str) -> #std::result::Result<Self, #std::num::ParseIntError> {
                    let #field_ident = <#implementation as #modtype::Impl>::from_str(s, #modulus)?;
                    #std::result::Result::Ok(#struct_expr)
                }
            }
        }
    }
}
