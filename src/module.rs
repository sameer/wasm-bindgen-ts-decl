use std::collections::HashMap;

use swc_ecma_ast::{
    Decl, ExportDecl, ExportDefaultExpr, ExportDefaultSpecifier, ExportNamedSpecifier,
    ExportSpecifier, Ident, ImportDecl, ImportDefaultSpecifier, ImportNamedSpecifier,
    ImportSpecifier, ModuleDecl, ModuleExportName, ModuleItem, NamedExport, Stmt,
    TsNamespaceExportDecl,
};
use syn::{
    parse_quote,
    punctuated::Punctuated,
    token::{Brace, Comma},
    visit_mut::VisitMut,
    Expr, ExprArray, ExprAssign, ForeignItem, Item, ItemForeignMod, ItemUse, Token, UseGroup,
    UsePath, UseTree,
};

use crate::{
    decl::{decl_ident, decl_to_items, ts_module_to_binding},
    util::{import_prefix_to_idents, sanitize_sym, ModuleBindingsCleaner},
};

pub fn imports_to_uses(body: &[ModuleItem]) -> Vec<ItemUse> {
    let mut uses = vec![];
    for item in body {
        match item {
            ModuleItem::ModuleDecl(ModuleDecl::Import(ImportDecl {
                specifiers, src, ..
            })) => {
                let prefix = import_prefix_to_idents(&src.value);
                let mut leaves: Punctuated<UseTree, Comma> = Punctuated::new();
                for spec in specifiers {
                    match spec {
                        ImportSpecifier::Named(ImportNamedSpecifier {
                            local: Ident { sym, .. },
                            imported,
                            ..
                        }) => {
                            let name = sanitize_sym(sym);
                            if let Some(imported) = imported {
                                let rename = sanitize_sym(match imported {
                                    ModuleExportName::Ident(Ident { sym, .. }) => sym,
                                    ModuleExportName::Str(s) => &s.value,
                                });
                                leaves.push(parse_quote!(#name as #rename));
                            } else {
                                leaves.push(parse_quote!(#name));
                            }
                        }
                        ImportSpecifier::Default(ImportDefaultSpecifier {
                            local: Ident { sym, .. },
                            ..
                        }) => {
                            let rename = sanitize_sym(sym);
                            leaves.push(parse_quote!(default as #rename));
                        }
                        ImportSpecifier::Namespace(_) => {
                            continue;
                        }
                    }
                }
                if leaves.is_empty() {
                    continue;
                }
                let leaf = if leaves.len() > 1 {
                    UseTree::Group(UseGroup {
                        brace_token: Brace::default(),
                        items: leaves,
                    })
                } else {
                    leaves.pop().unwrap().into_value()
                };
                let use_tree = use_path_to_use_tree(prefix, leaf);
                uses.push(parse_quote! {
                    pub use #use_tree;
                })
            }
            ModuleItem::ModuleDecl(ModuleDecl::ExportDefaultExpr(ExportDefaultExpr {
                expr,
                ..
            })) => {
                let name = sanitize_sym(&expr.as_ident().unwrap().sym);
                uses.push(parse_quote! {
                    pub use self::#name as default;
                });
            }
            ModuleItem::ModuleDecl(ModuleDecl::ExportNamed(NamedExport {
                specifiers,
                src,
                ..
            })) => {
                let prefix = if let Some(src) = src {
                    import_prefix_to_idents(&src.value)
                } else {
                    let fake_use: UseTree = parse_quote!(self);
                    let fake_use = match fake_use {
                        UseTree::Name(path) => path.ident,
                        _ => unreachable!(),
                    };
                    vec![fake_use]
                };
                let mut leaves: Punctuated<UseTree, Comma> = Punctuated::new();
                for spec in specifiers {
                    match spec {
                        ExportSpecifier::Named(ExportNamedSpecifier { orig, exported, .. }) => {
                            let name = sanitize_sym(match orig {
                                ModuleExportName::Ident(Ident { sym, .. }) => sym,
                                ModuleExportName::Str(s) => &s.value,
                            });
                            if let Some(exported) = exported {
                                let rename = sanitize_sym(match exported {
                                    ModuleExportName::Ident(Ident { sym, .. }) => sym,
                                    ModuleExportName::Str(s) => &s.value,
                                });
                                leaves.push(parse_quote!(#name as #rename));
                            } else {
                                leaves.push(parse_quote!(#name));
                            }
                        }
                        ExportSpecifier::Default(ExportDefaultSpecifier {
                            exported: Ident { sym, .. },
                            ..
                        }) => {
                            let rename = sanitize_sym(sym);
                            leaves.push(parse_quote!(default as #rename));
                        }
                        ExportSpecifier::Namespace(n) => {
                            todo!("{n:?}")
                        }
                    }
                }
                let leaf = if leaves.len() > 1 {
                    UseTree::Group(UseGroup {
                        brace_token: Brace::default(),
                        items: leaves,
                    })
                } else {
                    leaves.pop().unwrap().into_value()
                };
                let use_tree = use_path_to_use_tree(prefix, leaf);
                uses.push(parse_quote! {
                    pub use #use_tree;
                })
            }
            _ => {}
        }
    }
    uses
}

fn use_path_to_use_tree(mut prefix: Vec<syn::Ident>, leaf: UseTree) -> UseTree {
    let mut tree = leaf;
    while let Some(ident) = prefix.pop() {
        tree = UseTree::Path(UsePath {
            ident,
            colon2_token: <Token!(::)>::default(),
            tree: Box::new(tree),
        });
    }
    tree
}

/// Converts a JS module to an extern binding
///
/// If this is a namespace, assume everything inside it is exported.
pub fn module_as_binding(body: &[ModuleItem], namespace: Option<&str>) -> Vec<Item> {
    let mut items = vec![];

    let mut enclosing_ns: Option<&str> = None;
    let mut foreign_items = vec![];
    let mut default_ident = None;
    let mut declared_bodies: HashMap<String, &Decl> = HashMap::new();
    for item in body {
        match item {
            ModuleItem::Stmt(Stmt::Decl(decl)) if namespace.is_none() => {
                if let Some(ident) = decl_ident(decl) {
                    declared_bodies.insert(ident.to_string(), decl);
                }
            }
            ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl {
                decl: Decl::TsModule(tsm),
                ..
            }))
            | ModuleItem::Stmt(Stmt::Decl(Decl::TsModule(tsm))) => {
                let mod_extern = ts_module_to_binding(&tsm);
                items.extend(mod_extern.into_iter());
            }
            ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl { decl, .. }))
            | ModuleItem::Stmt(Stmt::Decl(decl)) => {
                let mut decl_foreign_items = decl_to_items(decl);
                foreign_items.append(&mut decl_foreign_items);
            }
            ModuleItem::ModuleDecl(ModuleDecl::ExportDefaultExpr(export_default))
                if namespace.is_none() =>
            {
                default_ident = export_default.expr.as_ident().map(|i| i.sym.to_string());
                continue;
            }
            ModuleItem::ModuleDecl(ModuleDecl::TsNamespaceExport(TsNamespaceExportDecl {
                id: Ident { sym, .. },
                ..
            })) => enclosing_ns = Some(sym),
            ModuleItem::Stmt(_) => {
                eprintln!("Didn't expect non decl statement");
            }
            ModuleItem::ModuleDecl(
                ModuleDecl::ExportNamed(_)
                | ModuleDecl::Import(_)
                | ModuleDecl::TsImportEquals(_)
                | ModuleDecl::ExportDefaultDecl(_)
                | ModuleDecl::ExportAll(_)
                | ModuleDecl::ExportDefaultExpr(_)
                | ModuleDecl::TsExportAssignment(_),
            ) => {}
        }
    }

    if let Some(decl) = default_ident.as_ref().and_then(|i| declared_bodies.get(i)) {
        let mut decl_foreign_items = decl_to_items(decl);
        foreign_items.append(&mut decl_foreign_items);
    }

    let mut dedupe = ModuleBindingsCleaner::default();
    foreign_items
        .iter_mut()
        .for_each(|i| dedupe.visit_foreign_item_mut(i));

    if !foreign_items.is_empty() {
        if namespace.is_some() {
            items.push(parse_quote! {
                use super::*;
            });
        } else {
            items.push(parse_quote! {
                use wasm_bindgen::prelude::wasm_bindgen;
            });
        }

        items.push(
            ItemForeignMod {
                attrs: vec![parse_quote!(#[wasm_bindgen])],
                abi: parse_quote!(extern "C"),
                brace_token: Brace::default(),
                items: foreign_items,
            }
            .into(),
        );
    }

    if let Some(ns) = namespace.or(enclosing_ns) {
        let mut ans = ApplyNamespace(ns.to_string());
        items.iter_mut().for_each(|i| ans.visit_item_mut(i));
    }

    items
}

struct ApplyNamespace(String);

impl VisitMut for ApplyNamespace {
    fn visit_foreign_item_mut(&mut self, fi: &mut ForeignItem) {
        let attrs = match fi {
            ForeignItem::Fn(f) => &mut f.attrs,
            ForeignItem::Static(s) => &mut s.attrs,
            ForeignItem::Type(t) => &mut t.attrs,
            _ => todo!(),
        };
        let ns = &self.0;
        if let Some((attr, mut array)) = attrs.iter_mut().find_map(|attr| {
            if attr.path.get_ident() == Some(&parse_quote!(wasm_bindgen)) {
                if let Ok(ExprAssign { left, right, .. }) = attr.parse_args::<ExprAssign>() {
                    if left == parse_quote!(js_namespace) {
                        if let Expr::Array(arr @ ExprArray { .. }) = *right {
                            return Some((attr, arr));
                        }
                    }
                }
            }
            None
        }) {
            array.elems.insert(0, parse_quote!(#ns));
            *attr = parse_quote! {
                #[wasm_bindgen(js_namespace = #array)]
            };
        } else {
            attrs.push(parse_quote!(#[wasm_bindgen(js_namespace = [#ns])]))
        }
    }
}
