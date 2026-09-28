// Compiles every Lithe program in the docs so examples cannot drift from the compiler.
//
// Each ```lithe block in a page must compile on its own. Words after the language
// change that:
//   ```lithe fragment         not a whole program; skipped
//   ```lithe rejects          must fail to compile; when the next block is ```text,
//                             the compiler's error must contain that text
//   ```lithe [path.lithe]     a file of a multi-file example, written under that path
//                             next to the page's other named files; every named file
//                             not under lib/ must compile. A named `x.spec.lithe` holds
//                             spec blocks: `lithe specs x.lithe` must accept it

import { execFileSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, relative } from "node:path";

const docs = import.meta.dirname;
const pages = join(docs, "src", "pages");
const lithe = process.env.LITHE ?? join(docs, "..", "target", "release", "lithe");
if (!existsSync(lithe)) {
  console.error(`no compiler at ${lithe}; run \`cargo build --release\` or set LITHE`);
  process.exit(1);
}

function walk(dir, out = []) {
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const path = join(dir, entry.name);
    if (entry.isDirectory()) walk(path, out);
    else if (/\.mdx?$/.test(path)) out.push(path);
  }
  return out;
}

function run(args, cwd) {
  try {
    execFileSync(lithe, args, { stdio: "pipe", cwd });
    return { ok: true, message: "" };
  } catch (err) {
    return { ok: false, message: String(err.stderr) };
  }
}

// A file with several contracts builds one bytecode per contract, so it compiles as a directory.
function compile(file) {
  const result = run(["compile", file]);
  if (result.ok || !result.message.includes("one bytecode needs a single contract")) return result;
  const dir = mkdtempSync(join(scratch, "contracts-"));
  writeFileSync(join(dir, "main.lithe"), readFileSync(file));
  return run(["compile", dir], dir);
}

function blocks(text) {
  const lines = text.split("\n");
  const out = [];
  for (let i = 0; i < lines.length; i++) {
    const open = lines[i].match(/^\s*```(\w+)\s*(.*)$/);
    if (!open) continue;
    const line = i + 1;
    const body = [];
    for (i++; i < lines.length && !/^\s*```\s*$/.test(lines[i]); i++) body.push(lines[i]);
    out.push({ lang: open[1], meta: open[2], line, code: body.join("\n") + "\n" });
  }
  return out;
}

const scratch = mkdtempSync(join(tmpdir(), "lithe-docs-"));
const failures = [];
let checked = 0;

for (const [p, page] of walk(pages).entries()) {
  const found = blocks(readFileSync(page, "utf8"));
  const dir = join(scratch, `page${p}`);
  const named = [];
  found.forEach((block, n) => {
    if (block.lang !== "lithe" || /\bfragment\b/.test(block.meta)) return;
    const where = `${relative(docs, page)}:${block.line}`;
    const title = block.meta.match(/\[(.+\.lithe)\]/);
    if (title) {
      const file = join(dir, title[1]);
      mkdirSync(dirname(file), { recursive: true });
      writeFileSync(file, block.code);
      if (title[1].endsWith(".spec.lithe")) {
        named.push({ file: file.replace(/\.spec\.lithe$/, ".lithe"), where, specs: true });
      } else if (!title[1].split("/").includes("lib")) named.push({ file, where });
      return;
    }
    const file = join(scratch, `block${checked++}.lithe`);
    writeFileSync(file, block.code);
    const result = compile(file);
    if (/\brejects\b/.test(block.meta)) {
      const next = found[n + 1];
      const expected = next?.lang === "text" ? next.code.trim() : "";
      if (result.ok) failures.push(`${where}: expected a compile error`);
      else if (!result.message.includes(expected))
        failures.push(`${where}: expected\n${expected}\ngot\n${result.message}`);
    } else if (!result.ok) {
      failures.push(`${where}:\n${result.message}`);
    }
  });
  for (const { file, where, specs } of named) {
    checked++;
    const result = specs ? run(["specs", file]) : compile(file);
    if (!result.ok) failures.push(`${where}:\n${result.message}`);
  }
}

if (failures.length) {
  console.error(failures.join("\n\n"));
  console.error(`\n${failures.length} of ${checked} programs failed`);
  process.exit(1);
}
console.log(`${checked} programs compile as documented`);
