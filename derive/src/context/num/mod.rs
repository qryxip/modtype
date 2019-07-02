mod traits;

use crate::context::Context;

use quote::quote;
use syn::parse_quote;

impl Context {
    pub(crate) fn derive_num(&self) -> proc_macro2::TokenStream {
        if self.non_static_modulus {
            return quote!();
        }

        let Self {
            modulus,
            implementation,
            std,
            modtype,
            num_traits,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(
            &[
                parse_quote!(Addition),
                parse_quote!(Subtraction),
                parse_quote!(Multiplication),
                parse_quote!(Division),
            ],
            &generics,
        );
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let struct_expr = self.struct_expr(true, None);

        quote! {
            impl#impl_generics #num_traits::Num for #struct_ident#ty_generics
            #where_clause
            {
                type FromStrRadixErr = #std::num::ParseIntError;

                #[inline]
                fn from_str_radix(
                    str: &str,
                    radix: u32,
                ) -> #std::result::Result<Self, #std::num::ParseIntError> {
                    let #field_ident =
                        <#implementation as #modtype::Impl>::from_str_radix(str, radix, #modulus)?;
                    Ok(#struct_expr)
                }
            }
        }
    }
}
