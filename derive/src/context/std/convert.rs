use crate::context::Context;

use quote::quote;
use syn::parse_quote;

impl Context {
    pub(crate) fn derive_from(&self) -> proc_macro2::TokenStream {
        if self.non_static_modulus {
            return quote!();
        }

        let Context {
            modulus,
            cartridge,
            std,
            num_bigint,
            modtype,
            struct_ident,
            generics,
            ..
        } = self;

        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

        let generics = self.with_features(&[
            parse_quote!(AssumePrimeModulus),
            parse_quote!(PartialSubtraction),
            parse_quote!(PartialMultiplication),
            parse_quote!(PartialDivision),
        ]);
        let (_, _, where_clause_div) = generics.split_for_impl();

        let generics = self.with_features(&[parse_quote!(PartialSubtraction)]);
        let (_, _, where_clause_sub) = generics.split_for_impl();

        let mut acc = quote!();

        for (from_ty, method_ident, where_clause) in &[
            (quote!(u8), quote!(from_u8), where_clause),
            (quote!(u16), quote!(from_u16), where_clause),
            (quote!(u32), quote!(from_u32), where_clause),
            (quote!(u64), quote!(from_u64), where_clause),
            (quote!(u128), quote!(from_u128), where_clause),
            (quote!(usize), quote!(from_usize), where_clause),
            (quote!(i8), quote!(from_i8), where_clause_sub),
            (quote!(i16), quote!(from_i16), where_clause_sub),
            (quote!(i32), quote!(from_i32), where_clause_sub),
            (quote!(i64), quote!(from_i64), where_clause_sub),
            (quote!(i128), quote!(from_i128), where_clause_sub),
            (quote!(isize), quote!(from_isize), where_clause_sub),
            (quote!(f32), quote!(from_float_prim), where_clause_div),
            (quote!(f64), quote!(from_float_prim), where_clause_div),
            (
                quote!(#num_bigint::BigUint),
                quote!(from_biguint),
                where_clause,
            ),
            (
                quote!(#num_bigint::BigInt),
                quote!(from_bigint),
                where_clause_sub,
            ),
        ] {
            let value_expr = parse_quote! {
                <#cartridge as #modtype::Cartridge>::#method_ident(from, #modulus)
            };
            let struct_expr = self.struct_expr(true, Some(value_expr));

            acc.extend(quote! {
                impl #impl_generics #std::convert::From<#from_ty> for #struct_ident#ty_generics
                #where_clause
                {
                    #[inline]
                    fn from(from: #from_ty) -> Self {
                        #struct_expr
                    }
                }
            });
        }

        acc
    }
}
