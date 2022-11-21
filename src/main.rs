use std::collections::{HashMap, HashSet};
use std::fs::{File, OpenOptions};
use std::io::Write as IoWrite;
use std::{env::args, path::PathBuf};

use swc_common::{
    errors::{ColorConfig, Handler},
    sync::Lrc,
    SourceMap,
};
use swc_ecma_parser::{lexer::Lexer, Parser, StringInput, Syntax, TsConfig};
use syn::visit::Visit;
use syn::visit_mut::VisitMut;
use syn::Item;
use walkdir::WalkDir;

use crate::module::{imports_to_uses, module_as_binding};
use crate::ty::wasm_abi_set;
use crate::util::{BindingsCleaner, CollectPubs, SysUseAdder, WasmAbify};

mod decl;
mod func;
mod module;
mod pat;
mod ty;
mod util;
mod wasm;

fn main() -> std::io::Result<()> {
    let typescript_path = PathBuf::from(args().nth(1).expect("No dir specified"));
    let rust_destination = PathBuf::from(args().nth(2).expect("No dest specified"));

    let mut crate_path = typescript_path.as_path();
    while let Some(parent) = crate_path.parent() {
        if crate_path.join("Cargo.toml").exists() {
            break;
        } else {
            crate_path = parent;
        }
    }
    if !crate_path.join("Cargo.toml").exists() {
        panic!("Typescript isn't in a crate");
    }

    let mut dir_mods: HashMap<PathBuf, HashSet<String>> = HashMap::new();

    for entry in WalkDir::new(&typescript_path) {
        let entry = entry.unwrap();

        let mut new_path =
            rust_destination.join(entry.path().strip_prefix(&typescript_path).unwrap());
        if new_path == rust_destination {
            continue;
        } else if entry.file_type().is_dir() {
            std::fs::create_dir_all(&new_path)?;
            dir_mods
                .entry(new_path.parent().unwrap().join("mod.rs"))
                .or_default()
                .insert(entry.file_name().to_str().unwrap().to_string());
        } else if entry.path().to_str().unwrap().ends_with(".d.ts") {
            println!("{}", entry.path().display());
            new_path.pop();
            let filename = entry
                .file_name()
                .to_str()
                .unwrap()
                .split_once('.')
                .unwrap()
                .0;
            dir_mods
                .entry(new_path.join("mod.rs"))
                .or_default()
                .insert(filename.to_string());
            new_path.push(format!("{filename}.rs",));
            let mut f = File::create(&new_path).unwrap();

            let cm: Lrc<SourceMap> = Default::default();
            let handler =
                Handler::with_tty_emitter(ColorConfig::Auto, true, false, Some(cm.clone()));

            let fm = cm.load_file(entry.path())?;
            let lexer = Lexer::new(
                Syntax::Typescript(TsConfig {
                    dts: true,
                    ..Default::default()
                }),
                Default::default(),
                StringInput::from(&*fm),
                None,
            );

            let mut parser = Parser::new_from(lexer);

            for e in parser.take_errors() {
                e.into_diagnostic(&handler).emit();
            }

            let module = parser
                .parse_module()
                .map_err(|e| {
                    // Unrecoverable fatal error occurred
                    e.into_diagnostic(&handler).emit()
                })
                .expect("failed to parser module");

            let mut file: syn::File = syn::File {
                shebang: None,
                attrs: vec![],
                items: vec![],
            };

            let uses = imports_to_uses(&module.body);
            let mut module_items = module_as_binding(&module.body, None);

            let mut cleaner = BindingsCleaner;
            module_items
                .iter_mut()
                .for_each(|i| cleaner.visit_item_mut(i));

            let mut pubs = CollectPubs::default();
            module_items.iter().for_each(|i| pubs.visit_item(i));
            uses.iter().for_each(|u| pubs.visit_item_use(u));

            // All externed types implement JsObject
            // so they can be directly sent back to JS.
            let mut abify = WasmAbify {
                wasm_abi_types: wasm_abi_set(&pubs.0),
            };
            module_items
                .iter_mut()
                .for_each(|i| abify.visit_item_mut(i));
            let mut adder = SysUseAdder {
                pubs: pubs.0,
                uses: HashSet::default(),
            };
            module_items.iter().for_each(|i| adder.visit_item(i));

            file.items.extend(adder.uses.into_iter().map(Item::Use));
            file.items.extend(uses.into_iter().map(Item::Use));
            file.items.append(&mut module_items);

            write!(f, "{}", prettyplease::unparse(&file))?;
        }
    }

    for (path, mods) in &dir_mods {
        let named_parent = path.parent().unwrap().with_extension("rs");
        let named_parent_exists = named_parent.exists();
        let mut f = if named_parent_exists {
            OpenOptions::new().append(true).open(&named_parent)?
        } else {
            File::create(path)?
        };

        for m in mods {
            if named_parent_exists {
                let name_rs_exists = path
                    .parent()
                    .unwrap()
                    .join(m)
                    .with_extension("rs")
                    .exists();
                let mod_rs_exists = path.parent().unwrap().join(m).join("mod.rs").exists();
                if name_rs_exists {
                    writeln!(
                        f,
                        "#[path = \"{}/{m}.rs\"]",
                        path.parent()
                            .unwrap()
                            .file_name()
                            .unwrap()
                            .to_str()
                            .unwrap()
                    )?;
                } else if mod_rs_exists {
                    writeln!(
                        f,
                        "#[path = \"{}/{m}/mod.rs\"]",
                        path.parent()
                            .unwrap()
                            .file_name()
                            .unwrap()
                            .to_str()
                            .unwrap()
                    )?;
                } else {
                    continue;
                }
            } else {
                let name_rs_exists = path
                    .parent()
                    .unwrap()
                    .join(m)
                    .with_extension("rs")
                    .exists();
                let mod_rs_exists = path.parent().unwrap().join(m).join("mod.rs").exists();
                if name_rs_exists {
                    writeln!(f, "#[path = \"{m}.rs\"]")?;
                } else if mod_rs_exists {
                    writeln!(f, "#[path = \"{m}/mod.rs\"]")?;
                } else {
                    continue;
                }
            }
            writeln!(f, "#[allow(non_snake_case)]")?;
            writeln!(f, "pub mod {m}Mod;")?;
        }
    }
    Ok(())
}
