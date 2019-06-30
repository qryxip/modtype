mod traits;

use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_num(&self) -> proc_macro::TokenStream {
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
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let struct_expr = self.struct_expr(true, None);

        quote!(
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
        )
        .into()
    }
}
