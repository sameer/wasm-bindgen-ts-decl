use std::collections::HashSet;

use swc_ecma_ast::{
    Ident, Str, TsEntityName, TsFnOrConstructorType, TsImportType, TsKeywordTypeKind, TsType,
    TsTypeRef, TsUnionOrIntersectionType,
};
use syn::{parse_quote, parse_str, punctuated::Punctuated, token::Comma, GenericArgument, Type};

use crate::util::{import_path_to_type_path_prefix, sanitize_sym};
pub fn ts_type_to_type(ty: &TsType) -> Type {
    match ty {
        TsType::TsKeywordType(kt) => match kt.kind {
            TsKeywordTypeKind::TsUnknownKeyword
            | TsKeywordTypeKind::TsAnyKeyword
            | TsKeywordTypeKind::TsNullKeyword
            | TsKeywordTypeKind::TsUndefinedKeyword
            | TsKeywordTypeKind::TsNeverKeyword => parse_quote!(::wasm_bindgen::JsValue),
            TsKeywordTypeKind::TsNumberKeyword => parse_quote!(::core::primitive::f64),
            TsKeywordTypeKind::TsBooleanKeyword => parse_quote!(::core::primitive::bool),
            TsKeywordTypeKind::TsStringKeyword => parse_quote!(::std::string::String),

            TsKeywordTypeKind::TsVoidKeyword => parse_quote!(()),
            TsKeywordTypeKind::TsObjectKeyword
            | TsKeywordTypeKind::TsBigIntKeyword
            | TsKeywordTypeKind::TsSymbolKeyword
            | TsKeywordTypeKind::TsIntrinsicKeyword => todo!("{kt:?}"),
        },
        TsType::TsFnOrConstructorType(fnorc) => match fnorc {
            TsFnOrConstructorType::TsFnType(_) => parse_quote!(::wasm_bindgen::JsValue),
            TsFnOrConstructorType::TsConstructorType(ct) => todo!("{ct:?}"),
        },
        TsType::TsTypeRef(TsTypeRef {
            type_name,
            type_params,
            ..
        }) => match type_name {
            TsEntityName::TsQualifiedName(qn) => todo!("{qn:?}"),
            TsEntityName::Ident(Ident { sym, .. }) => {
                let ident = sanitize_sym(sym.as_ref());
                if let Some(type_params) = type_params {
                    let mut params: Punctuated<GenericArgument, Comma> = Punctuated::new();
                    for param in &type_params.params {
                        params.push(GenericArgument::Type(ts_type_to_type(param)));
                    }
                    if ident == "Array" {
                        parse_quote!(::std::boxed::Box<[#params]>)
                    } else {
                        parse_quote!(#ident)
                    }
                } else {
                    parse_quote!(#ident)
                }
            }
        },
        TsType::TsTypeQuery(_) => {
            eprintln!("Type queries unsupported");
            parse_quote!(::wasm_bindgen::JsValue)
        }
        TsType::TsTypeLit(_) => {
            eprintln!("Type literals unsupported");
            parse_quote!(::wasm_bindgen::JsValue)
        }
        TsType::TsArrayType(at) => {
            let elem_ty = ts_type_to_type(&at.elem_type);
            parse_quote!(Box<[#elem_ty]>)
        }
        TsType::TsOptionalType(ot) => {
            let opt_ty = ts_type_to_type(&ot.type_ann);
            parse_quote!(::std::option::Option<#opt_ty>)
        }
        TsType::TsUnionOrIntersectionType(uoi) => match uoi {
            TsUnionOrIntersectionType::TsUnionType(union) => {
                if union.types.len() == 2
                    && union.types[1]
                        .as_ref()
                        .as_ts_keyword_type()
                        .map(|k| k.kind == TsKeywordTypeKind::TsUndefinedKeyword)
                        .unwrap_or(false)
                {
                    let opt_ty = ts_type_to_type(&union.types[0]);
                    parse_quote!(::std::option::Option<#opt_ty>)
                } else {
                    parse_quote!(::wasm_bindgen::JsValue)
                }
            }
            TsUnionOrIntersectionType::TsIntersectionType(it) => todo!("{it:?}"),
        },
        TsType::TsParenthesizedType(pt) => {
            let pty = ts_type_to_type(&pt.type_ann);
            parse_quote!((#pty))
        }
        TsType::TsLitType(_) => {
            parse_quote!(::wasm_bindgen::JsValue)
        }

        TsType::TsImportType(TsImportType {
            arg: Str { value, .. },
            qualifier,
            ..
        }) => {
            if !value.starts_with('.') {
                parse_quote!(::wasm_bindgen::JsValue)
            } else {
                let path = import_path_to_type_path_prefix(value);
                let ident = sanitize_sym(&qualifier.as_ref().unwrap().as_ident().unwrap().sym);
                parse_quote! {
                    #path :: #ident
                }
            }
        }
        TsType::TsTupleType(_)
        | TsType::TsRestType(_)
        | TsType::TsTypePredicate(_)
        | TsType::TsConditionalType(_)
        | TsType::TsInferType(_)
        | TsType::TsTypeOperator(_)
        | TsType::TsIndexedAccessType(_)
        | TsType::TsMappedType(_)
        | TsType::TsThisType(_) => todo!("{ty:?}"),
    }
}

pub fn wasm_abi_set(custom: &HashSet<String>) -> HashSet<Type> {
    thread_local! {
        static SLICEABLE_BUILTINS: [Type; 8] = [
            parse_quote!(i32), parse_quote!(isize), parse_quote!(i64),
            parse_quote!(u32), parse_quote!(usize), parse_quote!(u64),
            parse_quote!(f32), parse_quote!(f64),
        ];
        static NON_SLICEABLE_BUILTINS: [Type; 4] = [
            parse_quote!(bool), parse_quote!(char),
            parse_quote!(()),
            parse_quote!(::std::string::String),
        ];
    }

    SLICEABLE_BUILTINS.with(|builtins| {
        let js_objects = custom.iter().map(|t| parse_str::<Type>(t).unwrap());
        let refs = builtins
            .iter()
            .cloned()
            .chain(NON_SLICEABLE_BUILTINS.with(|b| b.clone()))
            .chain(js_objects.clone())
            .map::<Type, _>(|t| parse_quote!(&#t));
        let opts = builtins
            .iter()
            .cloned()
            .chain(NON_SLICEABLE_BUILTINS.with(|b| b.clone()))
            .chain(js_objects.clone())
            .map::<Type, _>(|t| parse_quote!(::std::option::Option<#t>));
        let boxed_slices = builtins
            .iter()
            .cloned()
            .chain(js_objects.clone())
            .map::<Type, _>(|t| parse_quote!(::std::boxed::Box<[#t]>));
        let opt_boxed_slices = builtins
            .iter()
            .cloned()
            .chain(js_objects.clone())
            .map::<Type, _>(|t| parse_quote!(::std::option::Option<::std::boxed::Box<[#t]>>));

        builtins
            .iter()
            .cloned()
            .chain(js_objects.clone())
            .chain(refs)
            .chain(opts)
            .chain(boxed_slices)
            .chain(opt_boxed_slices)
            .chain(std::iter::once(parse_quote!(::wasm_bindgen::JsValue)))
            .collect()
    })
}
