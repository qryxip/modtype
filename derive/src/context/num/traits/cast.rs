use crate::context::Context;

use quote::quote;
use syn::parse_quote;

impl Context {
    pub(crate) fn derive_from_primitive(&self) -> proc_macro2::TokenStream {
        if self.non_static_modulus {
            return quote!();
        }

        let Self {
            modulus,
            cartridge,
            std,
            num_traits,
            modtype,
            struct_ident,
            field_ident,
            ..
        } = self;
        let generics = self.with_features(&[
            parse_quote!(AssumePrimeModulus),
            parse_quote!(PartialSubtraction),
            parse_quote!(PartialMultiplication),
            parse_quote!(PartialDivision),
        ]);
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let struct_expr = self.struct_expr(true, None);

        quote! {
            impl#impl_generics #num_traits::FromPrimitive for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn from_i64(value: i64) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_i64(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_u64(value: u64) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_u64(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_i8(value: i8) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_i8(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_i16(value: i16) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_i16(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_i32(value: i32) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_i32(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_i128(value: i128) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_i128(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_isize(value: isize) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_isize(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_u8(value: u8) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_u8(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_u16(value: u16) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_u16(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_u32(value: u32) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_u32(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_u128(value: u128) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_u128(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_usize(value: usize) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_usize(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_f32(value: f32) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_float_prim(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_f64(value: f64) -> Option<Self> {
                    let #field_ident =
                        <#cartridge as #modtype::Cartridge>::from_float_prim(value, #modulus)?;
                    #std::option::Option::Some(#struct_expr)
                }
            }
        }
    }
}
