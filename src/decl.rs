use swc_ecma_ast::{
    Accessibility, ClassDecl, ClassMember, ClassMethod, ClassProp, Constructor, Decl, ExportDecl,
    FnDecl, Ident, MethodKind, ModuleDecl, ModuleItem, Stmt, TsIndexSignature, TsModuleBlock,
    TsModuleName, TsNamespaceBody, TsPropertySignature, TsType, TsTypeAliasDecl, TsTypeAnn,
    TsTypeElement, TsTypeLit,
};
use syn::{
    parse_quote, punctuated::Punctuated, token::Comma, visit_mut::VisitMut, FnArg, ForeignItem,
    ForeignItemFn, ForeignItemType, PatType, Signature, Token,
};

use crate::{
    func::function_signature,
    pat::pat_to_pat_type,
    ty::ts_type_to_type,
    util::{sanitize_sym, BindingsCleaner},
};

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

pub fn decl_to_items(decl: &Decl) -> Vec<ForeignItem> {
    let mut items = vec![];
    let mut namespaces = vec![];
    match decl {
        Decl::Class(class) => {
            items.append(&mut class_to_binding(class));
        }
        Decl::Fn(FnDecl {
            ident: Ident { sym, .. },
            function,
            ..
        }) => {
            let name = sanitize_sym(sym);
            let sig = function_signature(&name, function);
            items.push(parse_quote! {
                pub #sig;
            });
        }
        Decl::Var(var) => {
            assert!(var.decls.len() == 1);
            let mut pat_type = pat_to_pat_type(&var.decls.first().unwrap().name);
            let mut cleaner = BindingsCleaner(vec![]);
            cleaner.visit_pat_type_mut(&mut pat_type);
            items.push(parse_quote! {
                pub static #pat_type;
            });
        }
        Decl::TsTypeAlias(t) => {
            let TsTypeAliasDecl {
                id: Ident { sym, .. },
                type_ann,
                ..
            } = t.as_ref();
            let raw_name: &str = sym;
            let name = sanitize_sym(sym);
            let mut ty: ForeignItemType = parse_quote! {
                pub type #name;
            };
            if name != raw_name {
                ty.attrs
                    .push(parse_quote!(#[wasm_bindgen(js_name = #raw_name)]));
            }
            items.push(ty.into());

            if let TsType::TsTypeLit(TsTypeLit { members, .. }) = type_ann.as_ref() {
                for member in members {
                    match member {
                        TsTypeElement::TsCallSignatureDecl(_) => todo!(),
                        TsTypeElement::TsConstructSignatureDecl(_) => todo!(),
                        TsTypeElement::TsPropertySignature(TsPropertySignature {
                            readonly,
                            key,
                            computed,
                            optional,
                            init,
                            params,
                            type_ann,
                            type_params,
                            ..
                        }) => {
                            assert!(params.is_empty());
                            if let Some(ident) = key.as_ident() {
                                let generics: Vec<syn::Ident> = type_params
                                    .as_ref()
                                    .iter()
                                    .flat_map(|tp| tp.params.iter())
                                    .map(|t| sanitize_sym(&t.name.sym))
                                    .collect();
                                let mut cleaner = BindingsCleaner(generics);
                                items.push(prop_to_binding(
                                    &name,
                                    Some(&mut cleaner),
                                    &ident.sym,
                                    false,
                                    type_ann.as_ref(),
                                ));
                            }
                        }
                        TsTypeElement::TsGetterSignature(_) => todo!(),
                        TsTypeElement::TsSetterSignature(_) => todo!(),
                        TsTypeElement::TsMethodSignature(_) => todo!(),
                        TsTypeElement::TsIndexSignature(_) => {
                            eprintln!("Index signatures not supported");
                        }
                    }
                }
            }
        }
        Decl::TsEnum(_) | Decl::TsInterface(_) => {
            todo!("{decl:?}")
        }
        Decl::TsModule(module) => {
            let namespace = sanitize_sym(match &module.id {
                TsModuleName::Ident(i) => &i.sym,
                TsModuleName::Str(s) => &s.value,
            });

            match module.body.as_ref().unwrap() {
                TsNamespaceBody::TsModuleBlock(TsModuleBlock { body, .. }) => {
                    let mut namespace_items: Vec<ForeignItem> = vec![];
                    for item in body {
                        match item {
                            ModuleItem::Stmt(Stmt::Decl(decl))
                            | ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                                decl,
                                ..
                            })) => {
                                let mut decl_items = decl_to_items(decl);
                                namespace_items.append(&mut decl_items);
                            }
                            ModuleItem::ModuleDecl(_) | ModuleItem::Stmt(_) => {}
                        }
                    }
                    items.extend(namespace_items.into_iter().map(|item| {
                        parse_quote! {
                            #[wasm_bindgen(js_namespace = #namespace)]
                            #item
                        }
                    }));
                    namespaces.push(namespace);
                }
                TsNamespaceBody::TsNamespaceDecl(_) => {
                    eprintln!("TS namespaces unsupported: {namespace}");
                }
            }
        }
    }
    items
}

fn class_to_binding(
    ClassDecl {
        ident: Ident {
            sym: class_name, ..
        },
        class,
        ..
    }: &ClassDecl,
) -> Vec<ForeignItem> {
    let mut items = vec![];
    let raw_class_name: &str = class_name;
    let class_name = sanitize_sym(class_name.as_ref());

    let generics: Vec<syn::Ident> = class
        .type_params
        .as_ref()
        .iter()
        .flat_map(|tp| tp.params.iter())
        .map(|t| sanitize_sym(&t.name.sym))
        .collect();
    let mut cleaner = BindingsCleaner(generics);

    let mut clazz: ForeignItemType = parse_quote! {
        pub type #class_name;
    };
    if let Some(Ident { sym, .. }) = class.super_class.as_ref().and_then(|c| c.as_ident()) {
        let sup = sanitize_sym(sym.as_ref());
        clazz
            .attrs
            .push(parse_quote!(#[wasm_bindgen(extends = #sup)]));
    }
    if class_name != raw_class_name {
        clazz
            .attrs
            .push(parse_quote!(#[wasm_bindgen(js_name = #raw_class_name)]))
    }
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
                let name: &str = &key.as_ident().unwrap().sym;
                if name != "constructor" {
                    todo!("{name}");
                }
                let mut syn_params: Punctuated<FnArg, Comma> = Punctuated::new();
                for param in params.iter() {
                    syn_params.push(FnArg::Typed(pat_to_pat_type(
                        &param.as_param().unwrap().pat,
                    )));
                }
                let mut sig = parse_quote! {
                    fn new(#syn_params) -> #class_name
                };
                cleaner.visit_signature_mut(&mut sig);
                items.push(ForeignItem::Fn(parse_quote! {
                    #[wasm_bindgen(constructor)]
                    pub #sig;
                }));
            }
            ClassMember::Method(ClassMethod {
                key,
                function,
                kind,
                is_static,
                ..
            }) => {
                let raw_method_name: &str = &key.as_ident().unwrap().sym;
                let method_name = match kind {
                    MethodKind::Method => sanitize_sym(&key.as_ident().unwrap().sym),
                    MethodKind::Getter => sanitize_sym(&format!(
                        "get_{}",
                        sanitize_sym(&key.as_ident().unwrap().sym)
                    )),
                    MethodKind::Setter => sanitize_sym(&format!(
                        "set_{}",
                        sanitize_sym(&key.as_ident().unwrap().sym)
                    )),
                };
                let mut sig = function_signature(&method_name, function);
                cleaner.visit_signature_mut(&mut sig);

                if !*is_static {
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
                f.attrs.push(if *is_static {
                    parse_quote!(#[wasm_bindgen(static_method_of = #class_name)])
                } else {
                    match kind {
                        MethodKind::Method => parse_quote!(#[wasm_bindgen(method)]),
                        MethodKind::Getter => parse_quote!(#[wasm_bindgen(method, getter)]),
                        MethodKind::Setter => parse_quote!(#[wasm_bindgen(method, setter)]),
                    }
                });
                if method_name != raw_method_name {
                    f.attrs
                        .push(parse_quote!(#[wasm_bindgen(js_name = #raw_method_name)]))
                }

                items.push(ForeignItem::Fn(f));
            }
            ClassMember::ClassProp(ClassProp {
                key,
                type_ann,
                is_static,
                ..
            }) => {
                let raw_prop_name: &str = &key.as_ident().unwrap().sym;

                items.push(
                    prop_to_binding(
                        &class_name,
                        Some(&mut cleaner),
                        raw_prop_name,
                        *is_static,
                        type_ann.as_ref(),
                    )
                    .into(),
                );
            }
        }
    }

    items
}

fn prop_to_binding(
    class_name: &syn::Ident,
    cleaner: Option<&mut BindingsCleaner>,
    raw_prop_name: &str,
    is_static: bool,
    type_ann: Option<&Box<TsTypeAnn>>,
) -> ForeignItem {
    let prop_name = sanitize_sym(raw_prop_name);
    let ty = if let Some(ann) = type_ann.as_ref() {
        ts_type_to_type(&ann.type_ann)
    } else {
        parse_quote!(JsValue)
    };
    let mut sig: Signature = parse_quote! {
        fn #prop_name(this: &#class_name) -> #ty
    };
    if let Some(cleaner) = cleaner {
        cleaner.visit_signature_mut(&mut sig);
    }
    let mut f: ForeignItemFn = parse_quote! {
        pub #sig;
    };
    f.attrs.push(if is_static {
        parse_quote!(#[wasm_bindgen(static_method_of = #class_name)])
    } else {
        parse_quote!(#[wasm_bindgen(method)])
    });
    if prop_name != raw_prop_name {
        f.attrs
            .push(parse_quote!(#[wasm_bindgen(js_name = #raw_prop_name)]))
    }
    f.into()
}
