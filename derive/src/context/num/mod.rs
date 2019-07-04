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
            cartridge,
            std,
            modtype,
            num_traits,
            struct_ident,
            field_ident,
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
                        <#cartridge as #modtype::Cartridge>::from_str_radix(str, radix, #modulus)?;
                    Ok(#struct_expr)
                }
            }
        }
    }
}
