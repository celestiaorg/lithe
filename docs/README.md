# Lithe docs

The Lithe documentation site, built with [Vocs](https://vocs.dev). Pages are MDX files in `src/pages`.

```bash
npm install
npm run dev     # local server
npm run build   # checks every example, builds the playground, then writes a static site to dist/public
npm run playground  # builds the compiler to WebAssembly for /playground (needs the wasm32-unknown-unknown target)
npm run check   # compiles every ```lithe block against ../target/release/lithe
```

Every ```lithe block must compile. Mark a block `fragment` to skip it, `rejects` when it must fail (a following ```text block holds the expected error), or `[file.lithe]` to make it one file of a multi-file example. See `check.mjs`.
