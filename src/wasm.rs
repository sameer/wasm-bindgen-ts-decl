//! Various wasm_bindgen helpers

use std::cmp::Ordering;

use syn::{
    parse_quote,
    punctuated::Punctuated,
    token::{Bang, Bracket, Comma, Pound},
    AttrStyle, Attribute, Expr, ExprAssign, ExprPath, FnArg, ForeignItem, ForeignItemFn, Ident,
    Pat, PatType, Path, ReturnType, Type, TypePath, TypeReference,
};

pub fn merge_attrs(fi: &mut ForeignItem) {
    let attrs = match fi {
        ForeignItem::Fn(ff) => &mut ff.attrs,
        ForeignItem::Static(fs) => &mut fs.attrs,
        ForeignItem::Type(ft) => &mut ft.attrs,
        _ => return,
    };

    let not_wasm_attr =
        |attr: &Attribute| attr.path.get_ident() != Some(&parse_quote!(wasm_bindgen));
    attrs.sort_by(|a, b| {
        let a = not_wasm_attr(a);
        let b = not_wasm_attr(b);
        if a == b {
            Ordering::Equal
        } else if a {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    });

    let mut wasm_attrs: Punctuated<Expr, Comma> = Punctuated::new();
    let partition_point = attrs.partition_point(not_wasm_attr);
    while attrs.len() > partition_point {
        wasm_attrs.push(attrs.pop().unwrap().parse_args::<Expr>().unwrap())
    }

    if !wasm_attrs.is_empty() {
        attrs.push(Attribute {
            pound_token: Pound::default(),
            style: AttrStyle::Inner(Bang::default()),
            bracket_token: Bracket::default(),
            path: parse_quote!(wasm_bindgen),
            tokens: parse_quote!(),
        });
    }
    *fi = parse_quote! {
        #[wasm_bindgen(#wasm_attrs)]
        #fi
    }
}

pub fn extends(attr: &Attribute) -> Option<ExprPath> {
    if attr.path.get_ident() == Some(&parse_quote!(wasm_bindgen)) {
        if let Ok(ExprAssign { left, right, .. }) = attr.parse_args::<ExprAssign>() {
            if left == parse_quote!(extends) {
                if let Expr::Path(path) = right.as_ref() {
                    return Some(path.clone());
                }
            }
        }
    }
    None
}

pub fn method_of(ff: &ForeignItemFn) -> Option<Path> {
    for attr in &ff.attrs {
        if attr.path.get_ident() == Some(&parse_quote!(wasm_bindgen)) {
            if let Ok(ExprAssign { left, right, .. }) = attr.parse_args::<ExprAssign>() {
                if left == parse_quote!(static_method_of) {
                    if let Expr::Path(path) = right.as_ref() {
                        return Some(path.path.clone());
                    }
                }
            } else if let Ok(ident) = attr.parse_args::<Ident>() {
                if ident == "constructor" {
                    if let ReturnType::Type(_, t) = &ff.sig.output {
                        if let Type::Path(TypePath { path, .. }) = t.as_ref() {
                            return Some(path.clone());
                        }
                    }
                }
            }
        }
    }
    if let Some(FnArg::Typed(PatType { pat, ty, .. })) = ff.sig.inputs.first() {
        if let (Pat::Ident(ident), Type::Reference(TypeReference { elem, .. })) =
            (pat.as_ref(), ty.as_ref())
        {
            if let Type::Path(TypePath { path, .. }) = elem.as_ref() {
                if ident.ident == "this" {
                    return Some(path.clone());
                }
            }
        }
    }
    None
}

pub fn js_value() -> TypePath {
    thread_local! {
        static JS_VALUE: TypePath = parse_quote!(::wasm_bindgen::JsValue);
    }

    JS_VALUE.with(Clone::clone)
}
