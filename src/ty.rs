use std::collections::HashSet;

use swc_ecma_ast::{
    ArrayPat, BindingIdent, Ident, ObjectPat, Pat, RestPat, Str, TsEntityName,
    TsFnOrConstructorType, TsFnParam, TsFnType, TsImportType, TsIntersectionType,
    TsKeywordTypeKind, TsTupleElement, TsTupleType, TsType, TsTypeRef, TsUnionOrIntersectionType,
};
use syn::{
    parse_quote, parse_str,
    punctuated::Punctuated,
    token::{Colon2, Comma},
    visit_mut::VisitMut,
    GenericArgument, Path, PathArguments, PathSegment, Type, TypePath,
};

use crate::{
    util::{
        import_path_to_type_path_prefix, sanitize_sym, ByeByeGenerics, KNOWN_JS_SYS_TYPES,
        KNOWN_STRING_TYPES, KNOWN_WEB_SYS_TYPES,
    },
    wasm::js_value,
};
pub fn ts_type_to_type(ty: &TsType) -> Type {
    match ty {
        TsType::TsKeywordType(kt) => match kt.kind {
            TsKeywordTypeKind::TsUnknownKeyword
            | TsKeywordTypeKind::TsAnyKeyword
            | TsKeywordTypeKind::TsNullKeyword
            | TsKeywordTypeKind::TsUndefinedKeyword
            | TsKeywordTypeKind::TsNeverKeyword
            | TsKeywordTypeKind::TsObjectKeyword => js_value().into(),
            TsKeywordTypeKind::TsNumberKeyword => parse_quote!(::core::primitive::f64),
            TsKeywordTypeKind::TsBooleanKeyword => parse_quote!(::core::primitive::bool),
            TsKeywordTypeKind::TsStringKeyword => parse_quote!(::std::string::String),

            TsKeywordTypeKind::TsVoidKeyword => parse_quote!(()),
            TsKeywordTypeKind::TsBigIntKeyword
            | TsKeywordTypeKind::TsSymbolKeyword
            | TsKeywordTypeKind::TsIntrinsicKeyword => todo!("{kt:?}"),
        },
        TsType::TsFnOrConstructorType(fnorc) => match fnorc {
            TsFnOrConstructorType::TsFnType(TsFnType {
                params,
                type_params,
                // TODO: insert this return type on the signature
                type_ann,
                ..
            }) => {
                let mut gen = ByeByeGenerics::new(type_params.iter());
                let mut inputs: Punctuated<Type, Comma> = Punctuated::new();
                for p in params {
                    let ty = match p {
                        TsFnParam::Ident(BindingIdent { type_ann, .. })
                        // TODO: how to mark this as variadic :(
                        | TsFnParam::Rest(RestPat { type_ann, .. })
                        | TsFnParam::Array(ArrayPat { type_ann, .. })
                        | TsFnParam::Object(ObjectPat { type_ann , ..} )=> {
                            type_ann.as_ref().map(|ann| ts_type_to_type(&ann.type_ann))
                        }
                    };
                    inputs.push(ty.unwrap_or_else(|| js_value().into()));
                }
                inputs.iter_mut().for_each(|i| gen.visit_type_mut(i));
                parse_quote! {
                    &(dyn Fn(#inputs))
                }
            }
            TsFnOrConstructorType::TsConstructorType(ct) => todo!("{ct:?}"),
        },
        TsType::TsTypeRef(TsTypeRef {
            type_name,
            type_params,
            ..
        }) => match type_name {
            qn @ TsEntityName::TsQualifiedName(_) => {
                let mut type_path: Punctuated<PathSegment, Colon2> = Punctuated::new();

                let mut syms = vec![];
                let mut qn = qn;
                while let TsEntityName::TsQualifiedName(quali) = qn {
                    syms.push(&quali.right.sym);
                    qn = &quali.left;
                }
                if let TsEntityName::Ident(ident) = qn {
                    syms.push(&ident.sym);
                }

                for sym in syms[1..].iter().rev() {
                    let revised_raw_name = format!("{}Mod", sym);
                    type_path.push(PathSegment {
                        ident: sanitize_sym(&revised_raw_name),
                        arguments: PathArguments::None,
                    });
                }
                type_path.push(PathSegment {
                    ident: sanitize_sym(syms.first().unwrap()),
                    arguments: PathArguments::None,
                });

                TypePath {
                    qself: None,
                    path: Path {
                        leading_colon: None,
                        segments: type_path,
                    },
                }
                .into()
            }
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
        TsType::TsTypeQuery(tq) => {
            eprintln!("Type queries unsupported");
            js_value().into()
        }
        TsType::TsTypeLit(tl) => {
            eprintln!("Type literals unsupported");
            js_value().into()
        }
        TsType::TsArrayType(at) => {
            let elem_ty = ts_type_to_type(&at.elem_type);
            parse_quote!(::std::boxed::Box<[#elem_ty]>)
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
                        .map(|k| {
                            matches!(
                                k.kind,
                                TsKeywordTypeKind::TsUndefinedKeyword
                                    | TsKeywordTypeKind::TsNullKeyword
                            )
                        })
                        .unwrap_or(false)
                {
                    let opt_ty = ts_type_to_type(&union.types[0]);
                    parse_quote!(::std::option::Option<#opt_ty>)
                } else {
                    js_value().into()
                }
            }
            TsUnionOrIntersectionType::TsIntersectionType(TsIntersectionType { types, .. }) => {
                if let Some(ty) = types.first() {
                    return ts_type_to_type(ty);
                }
                eprintln!("Empty intersection type");
                js_value().into()
            }
        },
        TsType::TsParenthesizedType(pt) => {
            let pty = ts_type_to_type(&pt.type_ann);
            parse_quote!((#pty))
        }
        TsType::TsLitType(_tlt) => {
            eprintln!("Lit types unsupported");
            js_value().into()
        }

        TsType::TsImportType(TsImportType {
            arg: Str { value, .. },
            qualifier,
            ..
        }) => {
            if !value.starts_with('.') {
                eprintln!("Import unknown");
                js_value().into()
            } else {
                let path = import_path_to_type_path_prefix(value);
                let ident = sanitize_sym(&qualifier.as_ref().unwrap().as_ident().unwrap().sym);
                parse_quote! {
                    #path :: #ident
                }
            }
        }
        TsType::TsTupleType(TsTupleType { elem_types, .. }) => {
            let mut types: Punctuated<Type, Comma> = Punctuated::new();
            for TsTupleElement { ty, .. } in elem_types {
                types.push(ts_type_to_type(ty));
            }
            parse_quote!((#types))
        }
        TsType::TsIndexedAccessType(_iat) => {
            eprintln!("Indexed access type unsupported");
            js_value().into()
        }
        TsType::TsInferType(_) => js_value().into(),
        TsType::TsThisType(_) => {
            parse_quote!(Self)
        }
        TsType::TsRestType(_)
        | TsType::TsTypePredicate(_)
        | TsType::TsConditionalType(_)
        | TsType::TsTypeOperator(_)
        | TsType::TsMappedType(_) => todo!("{ty:?}"),
    }
}

pub fn wasm_abi_set(custom: &HashSet<String>) -> HashSet<Type> {
    thread_local! {
        static SLICEABLE_BUILTINS: [Type; 8] = [
            parse_quote!(::core::primitive::i32), parse_quote!(::core::primitive::isize), parse_quote!(::core::primitive::i64),
            parse_quote!(::core::primitive::u32), parse_quote!(::core::primitive::usize), parse_quote!(::core::primitive::u64),
            parse_quote!(::core::primitive::f32), parse_quote!(::core::primitive::f64),
        ];
        static NON_SLICEABLE_BUILTINS: [Type; 4] = [
            parse_quote!(::core::primitive::bool), parse_quote!(::core::primitive::char),
            parse_quote!(()),
            parse_quote!(::std::string::String),
        ];
        static KNOWN_TYPES: HashSet<Type> = KNOWN_STRING_TYPES.iter().chain(KNOWN_WEB_SYS_TYPES.iter()).chain(KNOWN_JS_SYS_TYPES.iter()).map(|s| {
            parse_str(s).unwrap()
        }).collect();
    }

    SLICEABLE_BUILTINS.with(|builtins| {
        let js_objects = custom.iter().map(|t| parse_str::<Type>(t).unwrap());
        let refs = builtins
            .iter()
            .cloned()
            .chain(NON_SLICEABLE_BUILTINS.with(|b| b.clone()))
            .chain(KNOWN_TYPES.with(|t| t.clone()))
            .chain(js_objects.clone())
            .map::<Type, _>(|t| parse_quote!(&#t));
        let opts = builtins
            .iter()
            .cloned()
            .chain(NON_SLICEABLE_BUILTINS.with(|b| b.clone()))
            .chain(KNOWN_TYPES.with(|t| t.clone()))
            .chain(js_objects.clone())
            .map::<Type, _>(|t| parse_quote!(::std::option::Option<#t>));
        let boxed_slices = builtins
            .iter()
            .cloned()
            .chain(KNOWN_TYPES.with(|t| t.clone()))
            .chain(js_objects.clone())
            .map::<Type, _>(|t| parse_quote!(::std::boxed::Box<[#t]>));
        let opt_boxed_slices = builtins
            .iter()
            .cloned()
            .chain(KNOWN_TYPES.with(|t| t.clone()))
            .chain(js_objects.clone())
            .map::<Type, _>(|t| parse_quote!(::std::option::Option<::std::boxed::Box<[#t]>>));

        builtins
            .iter()
            .cloned()
            .chain(NON_SLICEABLE_BUILTINS.with(|b| b.clone()))
            .chain(KNOWN_TYPES.with(|t| t.clone()))
            .chain(js_objects.clone())
            .chain(refs)
            .chain(opts)
            .chain(boxed_slices)
            .chain(opt_boxed_slices)
            .chain(std::iter::once(js_value().into()))
            .collect()
    })
}

pub fn fn_param_to_pat(param: TsFnParam) -> Pat {
    match param {
        TsFnParam::Ident(i) => Pat::Ident(i),
        TsFnParam::Array(a) => Pat::Array(a),
        TsFnParam::Rest(r) => Pat::Rest(r),
        TsFnParam::Object(o) => Pat::Object(o),
    }
}
