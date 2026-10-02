// Compiles each Lithe file with the WebAssembly build and the native compiler, and fails if
// their bytecode differs: the browser has 32-bit pointers and no threads.
//
//   node playground/check.mjs examples/*.lithe
//   LITHE_OPTIONS="evm-version=prague" node playground/check.mjs examples/*.lithe
//
// LITHE_OPTIONS holds build options, a `key=value` line each, given to both as the
// playground and `lithe compile --key value` take them.
// Files with relative imports are skipped, as the playground has one file.

import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { join } from "node:path";

const root = join(import.meta.dirname, "..");
const wasm = new WebAssembly.Module(readFileSync(join(root, "docs/public/play/lithe.wasm")));
const lithe = process.env.LITHE ?? join(root, "target/release/lithe");
const options = process.env.LITHE_OPTIONS ?? "";
const flags = options.split("\n").filter((l) => l.trim()).flatMap((l) => {
  const [key, ...value] = l.split("=");
  return [`--${key.trim()}`, value.join("=").trim()];
});

function write(x, buffer, text) {
  const bytes = new TextEncoder().encode(text);
  const at = x[buffer](bytes.length);
  new Uint8Array(x.memory.buffer, at, bytes.length).set(bytes);
}

function playground(source) {
  const x = new WebAssembly.Instance(wasm).exports;
  write(x, "options", options);
  write(x, "input", source);
  try {
    x.compile();
  } catch {}
  const text = new TextDecoder().decode(new Uint8Array(x.memory.buffer, x.output(), x.output_len()));
  return text ? JSON.parse(text) : { panic: "trapped without a message" };
}

function native(file) {
  try {
    const out = execFileSync(lithe, ["compile", ...flags, file], { env: { ...process.env, LITHE_CACHE_DIR: "" }, stdio: "pipe" });
    return out.toString().trim();
  } catch {
    return undefined;
  }
}

let checked = 0, failed = 0;
for (const file of process.argv.slice(2)) {
  const source = readFileSync(file, "utf8");
  if (/import "\.\.?\//.test(source)) continue;
  const ours = playground(source);
  // `lithe compile` prints one contract's bytecode, so files with several are not compared.
  const theirs = native(file);
  const problem = ours.panic ? `panicked: ${ours.panic}`
    : ours.contracts.length > 1 ? false
    : (theirs === undefined) !== (ours.errors.length > 0) ? `builds ${theirs === undefined ? "only in wasm" : "only natively"}`
    : theirs !== undefined && theirs !== `0x${ours.contracts[0].bytecode}` && "bytecode differs";
  checked++;
  if (problem) {
    failed++;
    console.log(`${file}: ${problem}`);
  }
}
console.log(`${checked - failed} of ${checked} match`);
process.exit(failed ? 1 : 0);
