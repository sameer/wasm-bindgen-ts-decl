# wasm-bindgen-ts-decl

Generate low-level Rust bindings to JavaScript using [wasm-bindgen](https://rustwasm.github.io/docs/wasm-bindgen/) & [Typescript Type Declarations](https://www.typescriptlang.org/docs/handbook/2/type-declarations.html).

There are some rough edges, but the bindings should compile with few to no manual changes.

## Usage

```bash
cargo run --release ./node_modules/@types/geojson/ dist
```

## TODOs

- [ ] OR types
- [ ] AND types
- [ ] Variadic function support
- [ ] Some TS features
- [ ] Proper namespace/modules support
- [ ] Rust style names: screaming camel case for statics
