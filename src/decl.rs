use swc_ecma_ast::{
    Accessibility, ClassDecl, ClassMember, ClassMethod, ClassProp, Constructor, Decl, FnDecl,
    Function, Ident, MethodKind, Param, TsGetterSignature, TsInterfaceBody, TsInterfaceDecl,
    TsMethodSignature, TsModuleBlock, TsModuleDecl, TsModuleName, TsNamespaceBody,
    TsPropertySignature, TsSetterSignature, TsType, TsTypeAliasDecl, TsTypeAnn, TsTypeElement,
    TsTypeLit,
};
use syn::{
    parse_quote, parse_str,
    punctuated::Punctuated,
    token::{Brace, Comma},
    visit_mut::VisitMut,
    FnArg, ForeignItem, ForeignItemFn, ForeignItemType, Item, ItemMod, Pat, PatType, Signature,
    Token, VisPublic, Visibility,
};

use crate::{
    func::function_signature,
    module::module_as_binding,
    pat::pat_to_pat_type,
    ty::{fn_param_to_pat, ts_type_to_type},
    util::{sanitize_sym, ByeByeGenerics, ModuleBindingsCleaner},
    wasm::js_value,
};

/// Get the raw identifier for a declaration if any
pub fn decl_ident(decl: &Decl) -> Option<&str> {
    match decl {
        Decl::Class(ClassDecl { ident, .. }) | Decl::Fn(FnDecl { ident, .. }) => Some(&ident.sym),
        Decl::Var(v) => v
            .decls
            .first()
            .and_then(|d| d.name.as_ident())
            .map(|i| i.sym.as_ref()),
        Decl::TsInterface(i) => Some(&i.id.sym),
        Decl::TsTypeAlias(a) => Some(&a.id.sym),
        Decl::TsEnum(e) => Some(&e.id.sym),
        Decl::TsModule(m) => match &m.id {
            TsModuleName::Ident(i) => Some(&i.sym),
            TsModuleName::Str(s) => Some(&s.value),
        },
    }
}

/// Convert classes, variables, type aliases, and interfaces to [ForeignItem]s.
pub fn decl_to_items(decl: &Decl) -> Vec<ForeignItem> {
    match decl {
        Decl::Class(class) => class_to_binding(class),
        Decl::Fn(FnDecl {
            ident: Ident { sym, .. },
            function,
            ..
        }) => {
            let name = sanitize_sym(sym);
            let sig = function_signature(&name, function);

            vec![parse_quote! {
                pub #sig;
            }]
        }
        Decl::Var(var) => {
            assert!(var.decls.len() == 1);
            let pat_type = pat_to_pat_type(&var.decls.first().unwrap().name);
            let ident = if let Pat::Ident(ident) = pat_type.pat.as_ref() {
                ident
            } else {
                unreachable!()
            };
            vec![parse_quote! {
                #[wasm_bindgen(js_name = #ident)]
                pub static #pat_type;
            }]
        }
        Decl::TsTypeAlias(t) => {
            let TsTypeAliasDecl {
                id: Ident { sym, .. },
                type_ann,
                type_params,
                ..
            } = t.as_ref();
            let alias = ty_to_binding(sym);
            let name = alias.ident.clone();
            let mut items = vec![alias.into()];

            let mut cleaner = ByeByeGenerics::new(type_params.iter());
            if let TsType::TsTypeLit(TsTypeLit { members, .. }) = type_ann.as_ref() {
                items.append(&mut ty_elems_to_binding(
                    &name,
                    &mut cleaner,
                    members.iter(),
                ));
            }
            items
        }
        Decl::TsInterface(iface) => {
            let TsInterfaceDecl {
                id: Ident { sym, .. },
                type_params,
                // TODO: extends
                extends,
                body: TsInterfaceBody { body, .. },
                ..
            } = iface.as_ref();
            let iface = ty_to_binding(sym);
            let mut cleaner = ByeByeGenerics::new(type_params.iter());
            let mut elems = ty_elems_to_binding(&iface.ident, &mut cleaner, body.iter());
            elems
                .iter_mut()
                .for_each(|e| cleaner.visit_foreign_item_mut(e));
            let mut items = vec![iface.into()];
            items.append(&mut elems);
            items
        }
        Decl::TsEnum(_) => {
            todo!("{decl:?}")
        }
        // Needs to be handled separately since we will create a mod for it
        Decl::TsModule(_) => {
            vec![]
        }
    }
}

pub fn ts_module_to_binding(module: &TsModuleDecl) -> Option<Item> {
    let raw_name = match &module.id {
        TsModuleName::Ident(i) => &i.sym,
        TsModuleName::Str(s) => &s.value,
    };
    let name = sanitize_sym(raw_name);

    let items = match module.body.as_ref() {
        Some(TsNamespaceBody::TsModuleBlock(TsModuleBlock { body, .. })) => {
            module_as_binding(body, Some(&raw_name))
        }
        Some(TsNamespaceBody::TsNamespaceDecl(_)) => {
            eprintln!("TS namespaces unsupported: {name}");
            return None;
        }
        None => {
            return None;
        }
    };

    Some(
        ItemMod {
            attrs: vec![],
            vis: Visibility::Public(VisPublic {
                pub_token: <Token!(pub)>::default(),
            }),
            mod_token: <Token!(mod)>::default(),
            ident: parse_str(&format!("{name}Mod")).unwrap(),
            content: Some((Brace::default(), items)),
            semi: None,
        }
        .into(),
    )
}

/// Convert class to its binding
fn class_to_binding(
    ClassDecl {
        ident: Ident {
            sym: raw_class_name,
            ..
        },
        class,
        ..
    }: &ClassDecl,
) -> Vec<ForeignItem> {
    let mut items = vec![];

    let mut cleaner = ByeByeGenerics::new(class.type_params.iter());

    let mut clazz: ForeignItemType = ty_to_binding(raw_class_name);
    if let Some(Ident { sym, .. }) = class.super_class.as_ref().and_then(|c| c.as_ident()) {
        let sup = sanitize_sym(sym.as_ref());
        clazz
            .attrs
            .push(parse_quote!(#[wasm_bindgen(extends = #sup)]));
    }
    let class_name = clazz.ident.clone();
    items.push(clazz.into());

    for member in &class.body {
        match member {
            ClassMember::Method(ClassMethod { accessibility, .. })
            | ClassMember::Constructor(Constructor { accessibility, .. })
            | ClassMember::ClassProp(ClassProp { accessibility, .. })
                if matches!(
                    accessibility,
                    Some(Accessibility::Private | Accessibility::Protected)
                ) =>
            {
                continue;
            }
            ClassMember::PrivateMethod(_) | ClassMember::PrivateProp(_) => {}
            ClassMember::TsIndexSignature(_)
            | ClassMember::Empty(_)
            | ClassMember::StaticBlock(_) => todo!("{member:?}"),
            ClassMember::Constructor(Constructor { key, params, .. }) => {
                let raw_name: &str = &key.as_ident().unwrap().sym;
                let name = if raw_name == "constructor" {
                    parse_str("new").unwrap()
                } else {
                    sanitize_sym(raw_name)
                };
                let mut syn_params: Punctuated<FnArg, Comma> = Punctuated::new();
                for param in params.iter() {
                    syn_params.push(FnArg::Typed(pat_to_pat_type(
                        &param.as_param().unwrap().pat,
                    )));
                }
                let mut sig = parse_quote! {
                    fn #name(#syn_params) -> #class_name
                };
                cleaner.visit_signature_mut(&mut sig);
                items.push(parse_quote! {
                    #[wasm_bindgen(constructor)]
                    pub #sig;
                });
            }
            ClassMember::Method(ClassMethod {
                key,
                function,
                kind,
                is_static,
                ..
            }) => {
                if let Some(Ident { sym, .. }) = key.as_ident() {
                    items.push(
                        method_to_binding(
                            &class_name,
                            &mut cleaner,
                            sym,
                            *kind,
                            *is_static,
                            function,
                        )
                        .into(),
                    );
                }
            }
            ClassMember::ClassProp(ClassProp {
                key,
                type_ann,
                is_static,
                is_optional,
                ..
            }) => {
                if let Some(Ident { sym, .. }) = key.as_ident() {
                    items.push(
                        prop_to_binding(
                            &class_name,
                            &mut cleaner,
                            sym,
                            *is_static,
                            *is_optional,
                            type_ann.as_ref(),
                        )
                        .into(),
                    );
                }
            }
        }
    }

    items
}

fn ty_elems_to_binding<'a>(
    name: &syn::Ident,
    class_cleaner: &mut ByeByeGenerics,
    elems: impl Iterator<Item = &'a TsTypeElement>,
) -> Vec<ForeignItem> {
    let mut items = vec![];
    for elem in elems {
        match elem {
            TsTypeElement::TsCallSignatureDecl(_) => todo!(),
            TsTypeElement::TsConstructSignatureDecl(_) => todo!(),
            TsTypeElement::TsPropertySignature(TsPropertySignature {
                key,
                params,
                type_ann,
                type_params,
                optional,
                ..
            }) => {
                assert!(params.is_empty());
                if let Some(Ident { sym, .. }) = key.as_ident() {
                    let mut cleaner = ByeByeGenerics::new(type_params.iter()).join(&class_cleaner);
                    items.push(prop_to_binding(
                        &name,
                        &mut cleaner,
                        sym,
                        false,
                        *optional,
                        type_ann.as_ref(),
                    ));
                }
            }
            TsTypeElement::TsGetterSignature(TsGetterSignature {
                span,
                key,
                type_ann,
                ..
            }) => {
                let fake_func = Function {
                    params: vec![],
                    decorators: vec![],
                    span: span.clone(),
                    body: None,
                    is_generator: false,
                    is_async: false,
                    type_params: None,
                    return_type: type_ann.clone(),
                };
                if let Some(Ident { sym, .. }) = key.as_ident() {
                    items.push(
                        method_to_binding(
                            &name,
                            class_cleaner,
                            sym,
                            MethodKind::Getter,
                            false,
                            &fake_func,
                        )
                        .into(),
                    );
                }
            }
            TsTypeElement::TsSetterSignature(TsSetterSignature {
                span, key, param, ..
            }) => {
                let fake_func = Function {
                    params: std::iter::once(param)
                        .cloned()
                        .map(fn_param_to_pat)
                        .map(|pat| Param {
                            span: span.clone(),
                            decorators: vec![],
                            pat,
                        })
                        .collect(),
                    decorators: vec![],
                    span: span.clone(),
                    body: None,
                    is_generator: false,
                    is_async: false,
                    type_params: None,
                    return_type: None,
                };
                if let Some(Ident { sym, .. }) = key.as_ident() {
                    items.push(
                        method_to_binding(
                            &name,
                            class_cleaner,
                            sym,
                            MethodKind::Setter,
                            false,
                            &fake_func,
                        )
                        .into(),
                    );
                }
            }
            TsTypeElement::TsMethodSignature(TsMethodSignature {
                span,
                key,
                params,
                type_ann,
                type_params,
                ..
            }) => {
                let fake_func = Function {
                    params: params
                        .iter()
                        .cloned()
                        .map(fn_param_to_pat)
                        .map(|pat| Param {
                            span: span.clone(),
                            decorators: vec![],
                            pat,
                        })
                        .collect(),
                    decorators: vec![],
                    span: span.clone(),
                    body: None,
                    is_generator: false,
                    is_async: false,
                    type_params: type_params.clone(),
                    return_type: type_ann.clone(),
                };
                let mut cleaner = ByeByeGenerics::new(type_params.iter()).join(&class_cleaner);
                if let Some(Ident { sym, .. }) = key.as_ident() {
                    items.push(
                        method_to_binding(
                            &name,
                            &mut cleaner,
                            sym,
                            MethodKind::Method,
                            false,
                            &fake_func,
                        )
                        .into(),
                    );
                }
            }
            TsTypeElement::TsIndexSignature(_) => {
                eprintln!("Index signatures not supported");
            }
        }
    }

    let mut dedupe = ModuleBindingsCleaner::default();
    items
        .iter_mut()
        .for_each(|i| dedupe.visit_foreign_item_mut(i));

    items
}

fn method_to_binding(
    class_name: &syn::Ident,
    cleaner: &mut ByeByeGenerics,
    raw_method_name: &str,
    kind: MethodKind,
    is_static: bool,
    function: &Function,
) -> ForeignItemFn {
    let method_name = match kind {
        MethodKind::Method => sanitize_sym(raw_method_name),
        MethodKind::Getter => sanitize_sym(&format!("get_{}", sanitize_sym(raw_method_name))),
        MethodKind::Setter => sanitize_sym(&format!("set_{}", sanitize_sym(raw_method_name))),
    };
    let mut sig = function_signature(&method_name, function);
    cleaner.visit_signature_mut(&mut sig);

    if !is_static {
        sig.inputs.insert(
            0,
            FnArg::Typed(PatType {
                attrs: vec![],
                pat: Box::new(parse_quote!(this)),
                colon_token: <Token!(:)>::default(),
                ty: Box::new(parse_quote!(&#class_name)),
            }),
        );
    }

    let mut f: ForeignItemFn = parse_quote! {
        pub #sig;
    };
    f.attrs.push(if is_static {
        parse_quote!(#[wasm_bindgen(static_method_of = #class_name)])
    } else {
        match kind {
            MethodKind::Method => parse_quote!(#[wasm_bindgen(method)]),
            MethodKind::Getter => parse_quote!(#[wasm_bindgen(method, getter)]),
            MethodKind::Setter => parse_quote!(#[wasm_bindgen(method, setter)]),
        }
    });
    // if method_name != raw_method_name {
    f.attrs
        .push(parse_quote!(#[wasm_bindgen(js_name = #raw_method_name)]));
    // }

    f
}

fn ty_to_binding(raw_name: &str) -> ForeignItemType {
    let name = sanitize_sym(raw_name);
    let mut ty: ForeignItemType = parse_quote! {
        pub type #name;
    };
    // if name != raw_name {
    ty.attrs
        .push(parse_quote!(#[wasm_bindgen(js_name = #raw_name)]));
    // }
    ty
}

fn prop_to_binding(
    class_name: &syn::Ident,
    cleaner: &mut ByeByeGenerics,
    raw_prop_name: &str,
    is_static: bool,
    is_optional: bool,
    type_ann: Option<&Box<TsTypeAnn>>,
) -> ForeignItem {
    let prop_name = sanitize_sym(raw_prop_name);
    let mut ty = if let Some(ann) = type_ann {
        ts_type_to_type(&ann.type_ann)
    } else {
        js_value().into()
    };
    if is_optional {
        ty = parse_quote!(::std::option::Option<#ty>);
    }
    let mut sig: Signature = parse_quote! {
        fn #prop_name(this: &#class_name) -> #ty
    };
    cleaner.visit_signature_mut(&mut sig);

    let mut f: ForeignItemFn = parse_quote! {
        pub #sig;
    };
    f.attrs.push(if is_static {
        parse_quote!(#[wasm_bindgen(static_method_of = #class_name)])
    } else {
        parse_quote!(#[wasm_bindgen(method)])
    });
    // if prop_name != raw_prop_name {
    f.attrs
        .push(parse_quote!(#[wasm_bindgen(js_name = #raw_prop_name)]));
    // }
    f.into()
}
