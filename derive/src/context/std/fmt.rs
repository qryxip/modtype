use crate::context::Context;

use quote::quote;
use syn::LitStr;

impl Context {
    pub(crate) fn derive_display(&self) -> proc_macro2::TokenStream {
        let Context {
            modulus,
            cartridge,
            std,
            modtype,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote! {
            impl#impl_generics #std::fmt::Display for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn fmt(&self, fmt: &mut #std::fmt::Formatter) -> #std::fmt::Result {
                    <#cartridge as #modtype::Cartridge>::fmt_display(
                        self.#field_ident,
                        #modulus,
                        fmt,
                    )
                }
            }
        }
    }

    pub(crate) fn derive_debug(&self) -> proc_macro2::TokenStream {
        let Context {
            modulus,
            cartridge,
            std,
            modtype,
            struct_ident,
            generics,
            field_ident,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let tuple_name = LitStr::new(&struct_ident.to_string(), struct_ident.span());

        quote! {
            impl#impl_generics #std::fmt::Debug for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn fmt(&self, fmt: &mut #std::fmt::Formatter) -> #std::fmt::Result {
                    <#cartridge as #modtype::Cartridge>::fmt_debug(
                        self.#field_ident,
                        #modulus,
                        #tuple_name,
                        fmt,
                    )
                }
            }
        }
    }
}
