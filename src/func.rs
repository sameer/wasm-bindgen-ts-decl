use swc_ecma_ast::{Function, TsKeywordType, TsKeywordTypeKind};
use syn::{
    parse_quote, punctuated::Punctuated, token::Comma, visit_mut::VisitMut, FnArg, Ident,
    ReturnType, Signature, Token,
};

use crate::{
    pat::pat_to_pat_type,
    ty::ts_type_to_type,
    util::{sanitize_sym, BindingsCleaner},
};

pub fn function_signature(name: &Ident, function: &Function) -> Signature {
    let generics: Vec<Ident> = function
        .type_params
        .as_ref()
        .iter()
        .flat_map(|tp| tp.params.iter())
        .map(|t| sanitize_sym(&t.name.sym))
        .collect();
    let mut generic_stripper = BindingsCleaner(generics);

    let mut params: Punctuated<FnArg, Comma> = Punctuated::new();
    for param in function.params.iter() {
        params.push(FnArg::Typed(pat_to_pat_type(&param.pat)));
    }
    let ret = function
        .return_type
        .as_ref()
        .filter(|t| {
            !matches!(
                t.type_ann.as_ts_keyword_type(),
                Some(TsKeywordType {
                    kind: TsKeywordTypeKind::TsVoidKeyword,
                    ..
                })
            )
        })
        .map(|r| ts_type_to_type(&r.type_ann))
        .map(|t| ReturnType::Type(<Token!(->)>::default(), Box::new(t)))
        .unwrap_or(ReturnType::Default);

    let mut sig = parse_quote! {
        fn #name (#params) #ret
    };
    generic_stripper.visit_signature_mut(&mut sig);
    sig
}

