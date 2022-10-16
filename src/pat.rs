use swc_ecma_ast::{BindingIdent, Ident, Pat, RestPat};
use syn::{parse_quote, PatType, Token};

use crate::{ty::ts_type_to_type, util::sanitize_sym};

pub fn pat_to_pat_type(pat: &Pat) -> PatType {
    match pat {
        Pat::Ident(BindingIdent {
            id: Ident { sym, optional, .. },
            type_ann,
        }) => {
            let pat: syn::Pat = {
                let ident = sanitize_sym(sym);
                parse_quote!(#ident)
            };
            let mut ty = if let Some(ann) = type_ann {
                ts_type_to_type(&ann.type_ann)
            } else {
                parse_quote!(::wasm_bindgen::JsValue)
            };

            if *optional {
                ty = parse_quote!(::std::option::Option<#ty>);
            }

            PatType {
                attrs: vec![],
                pat: Box::new(pat),
                colon_token: <Token!(:)>::default(),
                ty: Box::new(ty),
            }
        }
        // TODO: wasm bindgen variadic
        Pat::Rest(RestPat { arg, .. }) => pat_to_pat_type(arg),
        Pat::Array(_) | Pat::Object(_) | Pat::Assign(_) | Pat::Invalid(_) | Pat::Expr(_) => {
            todo!("{pat:?}")
        }
    }
}
