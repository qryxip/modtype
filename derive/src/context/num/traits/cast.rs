use crate::context::Context;

use quote::quote;

impl Context {
    pub(crate) fn derive_from_primitive(&self) -> proc_macro::TokenStream {
        let Self {
            modulus,
            std,
            num_traits,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let struct_expr = self.struct_expr(true, None);

        quote!(
            impl#impl_generics #num_traits::FromPrimitive for #struct_ident#ty_generics
            #where_clause
            {
                #[inline]
                fn from_u64(mut value: u64) -> Option<Self> {
                    let __modulus = #modulus;

                    let #field_ident = if let #std::option::Option::Some(mut value) =
                        <#field_ty as #num_traits::FromPrimitive>::from_u64(value)
                    {
                        if value >= __modulus {
                            value %= __modulus;
                        }
                        value
                    } else {
                        let modulus = <#field_ty as #num_traits::ToPrimitive>::to_u64(&__modulus)?;
                        if value >= modulus {
                            value %= modulus;
                        }
                        <#field_ty as #num_traits::FromPrimitive>::from_u64(value)?
                    };

                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_i64(mut value: i64) -> Option<Self> {
                    let __modulus = #modulus;

                    let neg = value < 0;
                    if neg {
                        value = -value;
                    }

                    let mut #field_ident = if let #std::option::Option::Some(mut value) =
                        <#field_ty as #num_traits::FromPrimitive>::from_i64(value)
                    {
                        if value >= __modulus {
                            value %= __modulus;
                        }
                        value
                    } else {
                        let modulus = <#field_ty as #num_traits::ToPrimitive>::to_i64(&__modulus)?;
                        if value >= modulus {
                            value %= modulus;
                        }
                        <#field_ty as #num_traits::FromPrimitive>::from_i64(value)?
                    };

                    if neg {
                        #field_ident = __modulus - #field_ident;
                    }

                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_u128(mut value: u128) -> Option<Self> {
                    let __modulus = #modulus;

                    let #field_ident = if let #std::option::Option::Some(mut value) =
                        <#field_ty as #num_traits::FromPrimitive>::from_u128(value)
                    {
                        if value >= __modulus {
                            value %= __modulus;
                        }
                        value
                    } else {
                        let modulus = <#field_ty as #num_traits::ToPrimitive>::to_u128(&__modulus)?;
                        if value >= modulus {
                            value %= modulus;
                        }
                        <#field_ty as #num_traits::FromPrimitive>::from_u128(value)?
                    };

                    #std::option::Option::Some(#struct_expr)
                }

                #[inline]
                fn from_i128(mut value: i128) -> Option<Self> {
                    let __modulus = #modulus;

                    let neg = value < 0;
                    if neg {
                        value = -value;
                    }

                    let mut #field_ident = if let #std::option::Option::Some(mut value) =
                        <#field_ty as #num_traits::FromPrimitive>::from_i128(value)
                    {
                        if value >= __modulus {
                            value %= __modulus;
                        }
                        value
                    } else {
                        let modulus = <#field_ty as #num_traits::ToPrimitive>::to_i128(&__modulus)?;
                        if value >= modulus {
                            value %= modulus;
                        }
                        <#field_ty as #num_traits::FromPrimitive>::from_i128(value)?
                    };

                    if neg {
                        #field_ident = __modulus - #field_ident;
                    }

                    #std::option::Option::Some(#struct_expr)
                }

                fn from_f32(value: f32) -> Option<Self> {
                    let __modulus = #modulus;
                    let (mantissa, exponent, sign) =
                        <f32 as #num_traits::Float>::integer_decode(value);

                    let two = <Self as #num_traits::FromPrimitive>::from_u64(2)?;
                    let ret = <Self as #num_traits::FromPrimitive>::from_u64(mantissa)?;
                    let ret = ret * <Self as #num_traits::Pow<i16>>::pow(two, exponent);
                    Some(if sign == -1 { -ret } else { ret })
                }

                fn from_f64(value: f64) -> Option<Self> {
                    let __modulus = #modulus;
                    let (mantissa, exponent, sign) =
                        <f64 as #num_traits::Float>::integer_decode(value);

                    let two = <Self as #num_traits::FromPrimitive>::from_u64(2)?;
                    let ret = <Self as #num_traits::FromPrimitive>::from_u64(mantissa)?;
                    let ret = ret * <Self as #num_traits::Pow<i16>>::pow(two, exponent);
                    Some(if sign == -1 { -ret } else { ret })
                }
            }
        )
        .into()
    }
}
