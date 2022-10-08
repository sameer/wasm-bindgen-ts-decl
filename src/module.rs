use std::collections::HashMap;

use swc_ecma_ast::{
    Decl, ExportDecl, ExportDefaultExpr, ExportDefaultSpecifier, ExportNamedSpecifier,
    ExportSpecifier, Ident, ImportDecl, ImportDefaultSpecifier, ImportNamedSpecifier,
    ImportSpecifier, ModuleDecl, ModuleExportName, ModuleItem, NamedExport, Stmt, TsModuleName,
};
use syn::{
    parse_quote,
    punctuated::Punctuated,
    token::{Brace, Comma},
    ForeignItem, ForeignItemType, Item, ItemForeignMod, ItemUse, Token, UseGroup, UsePath, UseTree,
};

use crate::{
    decl::{decl_ident, decl_to_items},
    util::{import_prefix_to_idents, sanitize_sym},
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

pub fn module_as_binding(module_path: &str, body: &[ModuleItem]) -> Vec<Item> {
    let mut foreign_items = vec![];
    let mut default_ident = None;
    let mut declared_bodies: HashMap<String, &Decl> = HashMap::new();
    for item in body {
        match item {
            ModuleItem::Stmt(Stmt::Decl(decl)) => {
                if let Some(ident) = decl_ident(decl) {
                    declared_bodies.insert(ident.to_string(), decl);
                }
            }
            ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl { decl, .. })) => {
                let mut decl_foreign_items = decl_to_items(decl);
                foreign_items.append(&mut decl_foreign_items);
            }
            ModuleItem::ModuleDecl(ModuleDecl::ExportDefaultExpr(export_default)) => {
                default_ident = export_default.expr.as_ident().map(|i| i.sym.to_string());
                continue;
            }
            ModuleItem::ModuleDecl(
                ModuleDecl::ExportNamed(_)
                | ModuleDecl::Import(_)
                | ModuleDecl::TsImportEquals(_)
                | ModuleDecl::ExportDefaultDecl(_)
                | ModuleDecl::ExportAll(_),
            ) => {}
            ModuleItem::ModuleDecl(_) => todo!("{item:?}"),
            _ => {
                eprintln!("Unknown");
            }
        }
    }

    if let Some(decl) = default_ident.as_ref().and_then(|i| declared_bodies.get(i)) {
        let mut decl_foreign_items = decl_to_items(decl);
        foreign_items.append(&mut decl_foreign_items);
    }

    // Hydrate implicit namespaces
    for decl in body
        .iter()
        .filter_map(|i| match i {
            ModuleItem::ModuleDecl(ModuleDecl::ExportDecl(ExportDecl { decl, .. })) => Some(decl),
            _ => None,
        })
        .chain(
            default_ident
                .as_ref()
                .and_then(|i| declared_bodies.get(i))
                .iter()
                .map(|d| **d),
        )
    {
        if let Decl::TsModule(module) = decl {
            let raw_name: &str = match &module.id {
                TsModuleName::Ident(i) => &i.sym,
                TsModuleName::Str(s) => &s.value,
            };
            let name = sanitize_sym(raw_name);
            let exists = foreign_items.iter().any(|item| match item {
                ForeignItem::Type(ForeignItemType { ident, .. }) => *ident == name,
                _ => false,
            });

            if !exists {
                let mut ty: ForeignItemType = parse_quote! {
                    pub type #name;
                };
                if name != raw_name {
                    ty.attrs
                        .push(parse_quote!(#[wasm_bindgen(js_name = #raw_name)]));
                }
                foreign_items.push(ty.into());
            }
        }
    }

    if foreign_items.is_empty() {
        vec![]
    } else {
        vec![
            parse_quote! {
                use wasm_bindgen::prelude::wasm_bindgen;
            },
            Item::ForeignMod(ItemForeignMod {
                attrs: vec![parse_quote!(#[wasm_bindgen(module = #module_path)])],
                abi: parse_quote!(extern "C"),
                brace_token: Brace::default(),
                items: foreign_items,
            }),
        ]
    }
}
