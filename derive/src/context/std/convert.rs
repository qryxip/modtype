use crate::context::{Context, FromOptions, FromType};

use quote::quote;

impl Context {
    pub(crate) fn derive_from(&self) -> proc_macro::TokenStream {
        let Context {
            modulus,
            std,
            num_bigint,
            from: FromOptions(from_tys),
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let mut ret = quote!();

        let struct_expr = self.struct_expr(true, None);

        if from_tys.contains(&FromType::InnerValue) {
            ret.extend(quote! {
                impl #impl_generics #std::convert::From<#field_ty> for #struct_ident#ty_generics
                #where_clause
                {
                    #[inline]
                    fn from(from: #field_ty) -> Self {
                        let #field_ident = from % (#modulus);
                        #struct_expr
                    }
                }
            });
        }

        if from_tys.contains(&FromType::BigUint) {
            ret.extend(quote! {
                impl #impl_generics #std::convert::From<#num_bigint::BigUint> for #struct_ident#ty_generics
                #where_clause
                {
                    #[inline]
                    fn from(from: #num_bigint::BigUint) -> Self {
                        let modulus = <#field_ty as #std::string::ToString>::to_string(&(#modulus));
                        let modulus = <#num_bigint::BigUint as #std::str::FromStr>::from_str(&modulus);
                        let modulus = #std::result::Result::unwrap(modulus);
                        let #field_ident = <#std::string::ToString>::to_string(&(from % modulus));
                        let #field_ident = <#field_ty as #std::str::FromStr>::from_str(&#field_ident);
                        let #field_ident = #std::result::Result::unwrap(#field_ident);
                        #struct_expr
                    }
                }
            });
        }

        if from_tys.contains(&FromType::BigInt) {
            ret.extend(quote! {
                impl #impl_generics #std::convert::From<#num_bigint::BigInt> for #struct_ident#ty_generics
                #where_clause
                {
                    #[inline]
                    fn from(from: #num_bigint::BigInt) -> Self {
                        let original_modulus = #modulus;
                        let modulus = <#field_ty as #std::string::ToString>::to_string(&(#modulus));
                        let modulus = <#num_bigint::BigInt as #std::str::FromStr>::from_str(&modulus);
                        let modulus = #std::result::Result::unwrap(modulus);
                        let unsigned = #num_bigint::BigInt::sign(&from) == #num_bigint::Sign::Minus;
                        let from = if unsigned { -from } else { from };
                        let #field_ident = <#std::string::ToString>::to_string(&(from % modulus));
                        let #field_ident = <#field_ty as #std::str::FromStr>::from_str(&#field_ident);
                        let #field_ident: #field_ty = #std::result::Result::unwrap(#field_ident);
                        let #field_ident: #field_ty = if unsigned {
                            original_modulus - #field_ident
                        } else {
                            #field_ident
                        };
                        #struct_expr
                    }
                }
            });
        }

        ret.into()
    }

    pub(crate) fn derive_into(&self) -> proc_macro::TokenStream {
        let Context {
            std,
            struct_ident,
            generics,
            field_ident,
            field_ty,
            ..
        } = self;
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        quote!(
            impl #impl_generics #std::convert::From<#struct_ident#ty_generics> for #field_ty
            #where_clause
            {
                #[inline]
                fn from(from: #struct_ident#ty_generics) -> Self {
                    from.#field_ident
                }
            }
        )
        .into()
    }
}
