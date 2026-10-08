"use client";

import type { EditorState } from "@codemirror/state";
import type { EditorView } from "@codemirror/view";
import { type MouseEvent, type ReactNode, useCallback, useEffect, useMemo, useRef, useState } from "react";
import { createEditor, fileState, goTo, replace, setDark, showErrors, tokens } from "./editor";
import * as examples from "./examples";
import { type Contract, Run, RUN_CSS } from "./Run";

const DEFAULT = `(* Edit me. The output follows as you type. *)

storage is record {
  count : uint;
}

external view function get() : uint is
  storage.count

external function inc() is {
  storage.count := storage.count + 1;
}

external function dec() is {
  storage.count := storage.count - 1;
}
`;
const SAVED = "lithe-playground";
const SAVED_OPTIONS = "lithe-playground-options";

/** The build options, keyed as `lithe.toml`'s `[build]` is. An option left empty takes its default. */
const BUILD = [
  { key: "evm-version", label: "EVM version", default: "osaka", choices: ["prague"] },
  { key: "size-limit", label: "Size limit", default: "24576" },
  { key: "create2-deployer", label: "CREATE2 deployer", default: "0x4e59b44847b379578588920cA78FbF26c0B4956C" },
] as const;
type Options = Partial<Record<(typeof BUILD)[number]["key"], string>>;
const lines = (options: Options) =>
  Object.entries(options)
    .filter(([, value]) => value)
    .map(([key, value]) => `${key}=${value}`)
    .join("\n");

type Diagnostic = { line: number; column: number; file: string | null; message: string; text: string };
type Result = { contracts: Contract[]; errors: Diagnostic[]; panic?: string };
type Project = examples.Project;

const SAVED_PROJECT = "lithe-playground-project";
const single = (text: string): Project => ({ files: [["main.lithe", text]], entry: "main.lithe" });

/** The project saved last, or the one-file program saved before projects. */
function savedProject(): Project {
  try {
    const p = JSON.parse(localStorage.getItem(SAVED_PROJECT) ?? "null");
    if (Array.isArray(p?.files) && p.files.length && p.entry) return p;
  } catch {}
  return single(localStorage.getItem(SAVED) ?? DEFAULT);
}

/** What a new file starts as: how to import it. */
const stub = (name: string, entry: string) =>
  `(* Import this file from ${entry} with: import "./${name.replace(/\.lithe$/, "")}"; *)\n`;

/** A file path a user typed, made a `.lithe` path inside the project, or why it can't be one. */
function filePath(typed: string, taken: string[]) {
  let path = typed.trim().replace(/^\.\//, "");
  if (!path.endsWith(".lithe")) path += ".lithe";
  if (!/^[A-Za-z0-9_-]+(\/[A-Za-z0-9_-]+)*\.lithe$/.test(path))
    return { error: "use letters, digits, - and _, with / between folders" };
  if (taken.includes(path)) return { error: `${path} already exists` };
  return { path };
}

function Highlighted({ code, dark }: { code: string; dark?: boolean }) {
  const lines = useMemo(() => (dark === undefined ? undefined : tokens(code, "json", dark)), [code, dark]);
  if (!lines) return code;
  return lines.map((line, i) => (
    <span key={i}>
      {line.map((token, j) => (
        <span key={j} style={{ color: token.color }}>
          {token.content}
        </span>
      ))}
      {i + 1 < lines.length && "\n"}
    </span>
  ));
}

/** Whether the docs show their dark theme, once the page has loaded. */
function useDark() {
  const [dark, setDark] = useState<boolean>();
  useEffect(() => {
    const root = document.documentElement;
    const read = () => setDark(root.dataset.vocsTheme === "dark");
    const observer = new MutationObserver(read);
    observer.observe(root, { attributeFilter: ["data-vocs-theme"] });
    read();
    return () => observer.disconnect();
  }, []);
  return dark;
}

async function pack(text: string) {
  const stream = new Blob([text]).stream().pipeThrough(new CompressionStream("deflate-raw"));
  const bytes = new Uint8Array(await new Response(stream).arrayBuffer());
  return btoa(String.fromCharCode(...bytes))
    .replace(/\+/g, "-")
    .replace(/\//g, "_")
    .replace(/=+$/, "");
}

async function unpack(code: string) {
  const bytes = Uint8Array.from(atob(code.replace(/-/g, "+").replace(/_/g, "/")), (c) => c.charCodeAt(0));
  const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("deflate-raw"));
  return new Response(stream).text();
}

export function Playground() {
  const [project, setProject] = useState<Project>(single(DEFAULT));
  const [active, setActive] = useState("main.lithe");
  // What an example replaced, until it is put back.
  const [previous, setPrevious] = useState<Project>();
  const [result, setResult] = useState<Result>();
  const [status, setStatus] = useState("");
  const [tab, setTab] = useState<"output" | "run">("output");
  const host = useRef<HTMLDivElement>(null);
  const editor = useRef<EditorView>(undefined);
  // Each file's editor state, with its own undo history; the editor shows the active one.
  const states = useRef(new Map<string, EditorState>());
  // Each state's file, by the name it has now: a rename changes the name, not the state.
  const named = useRef(new Map<string, { name: string }>());
  const [options, setOptions] = useState<Options>({});
  const worker =
    useRef<(cmd: "compile" | "format" | "session" | "storage_diff", source: string, options: string) => Promise<never>>(
      undefined,
    );
  const latest = useRef(project);
  const activeNow = useRef(active);
  activeNow.current = active;
  const resultNow = useRef(result);
  resultNow.current = result;
  const latestOptions = useRef(options);
  latestOptions.current = options;
  // A shared project is the page's, not the reader's, until they edit it.
  const persist = useRef(true);
  const dark = useDark();
  const darkNow = useRef(dark);
  darkNow.current = dark;

  const commit = (next: Project) => {
    latest.current = next;
    setProject(next);
    if (persist.current) localStorage.setItem(SAVED_PROJECT, JSON.stringify(next));
  };

  const errorsIn = (file: string) =>
    (resultNow.current?.errors ?? []).filter((e) => (e.file ?? latest.current.entry) === file);

  const stateFor = (name: string, text: string) => {
    const file = { name };
    named.current.set(name, file);
    return fileState({
      doc: text,
      label: `Lithe source, ${name}`,
      change: (next, kept) => {
        if (kept) persist.current = true;
        commit({ ...latest.current, files: latest.current.files.map(([n, t]) => [n, n === file.name ? next : t]) });
      },
      compile: () => compile(),
      format: () => format(),
    });
  };

  /** Gives a file a new name, keeping its state. */
  const move = (from: string, to: string) => {
    const file = named.current.get(from)!;
    file.name = to;
    named.current.delete(from);
    named.current.set(to, file);
    if (states.current.has(from)) {
      states.current.set(to, states.current.get(from)!);
      states.current.delete(from);
    }
    if (activeNow.current === from) {
      activeNow.current = to;
      setActive(to);
    }
  };

  /** Shows a file in the editor, as it was left. */
  const open = (name: string) => {
    const view = editor.current!;
    if (name !== activeNow.current) {
      states.current.set(activeNow.current, view.state);
      view.setState(states.current.get(name)!);
      activeNow.current = name;
      setActive(name);
    }
    if (darkNow.current !== undefined) setDark(view, darkNow.current);
    showErrors(view, errorsIn(name));
  };

  /** Replaces the whole project, each file with a fresh history. */
  const show = (next: Project) => {
    named.current = new Map();
    states.current = new Map(next.files.map(([n, t]) => [n, stateFor(n, t)]));
    editor.current!.setState(states.current.get(next.entry)!);
    activeNow.current = next.entry;
    setActive(next.entry);
    commit(next);
    if (darkNow.current !== undefined) setDark(editor.current!, darkNow.current);
  };

  useEffect(() => {
    const w = new Worker("/play/worker.js");
    const waiting = new Map<number, (result: never) => void>();
    let next = 0;
    w.onmessage = ({ data }) => {
      waiting.get(data.id)?.(data.result as never);
      waiting.delete(data.id);
    };
    worker.current = (cmd, source, options) =>
      new Promise((resolve) => {
        waiting.set(++next, resolve);
        w.postMessage({ id: next, cmd, source, options });
      });
    const view = createEditor(host.current!, stateFor("main.lithe", ""));
    editor.current = view;
    const params = new URLSearchParams(location.hash.slice(1));
    const shared = params.get("project") ?? params.get("code");
    if (shared) {
      persist.current = false;
      unpack(shared).then(
        (text) => show(params.has("project") ? JSON.parse(text) : single(text)),
        () => show(single(DEFAULT)),
      );
      setOptions(Object.fromEntries(BUILD.flatMap(({ key }) => (params.get(key) ? [[key, params.get(key)]] : []))));
    } else {
      show(savedProject());
      setOptions(JSON.parse(localStorage.getItem(SAVED_OPTIONS) ?? "{}"));
    }
    return () => {
      w.terminate();
      view.destroy();
    };
  }, []);

  useEffect(() => {
    if (dark !== undefined && editor.current) setDark(editor.current, dark);
  }, [dark]);

  useEffect(() => {
    if (editor.current) showErrors(editor.current, errorsIn(active));
  }, [result, active]);

  // One compile at a time: edits during one wait for it, and only the latest runs.
  const busy = useRef(false);
  const again = useRef(false);
  const compile = useCallback(async () => {
    if (busy.current) return void (again.current = true);
    busy.current = true;
    setStatus("Compiling…");
    let result: Result, ms: number;
    do {
      again.current = false;
      const start = performance.now();
      const { files, entry } = latest.current;
      result = await worker.current!(
        "compile",
        JSON.stringify({ files: Object.fromEntries(files), entry }),
        lines(latestOptions.current),
      );
      ms = Math.round(performance.now() - start);
    } while (again.current);
    busy.current = false;
    setResult(result);
    const errors = result.errors?.length ?? 0;
    setStatus(
      result.panic
        ? "The compiler crashed"
        : errors
          ? `${errors} error${errors > 1 ? "s" : ""}`
          : `Compiled in ${ms} ms`,
    );
  }, []);

  useEffect(() => {
    const timer = setTimeout(compile, 400);
    return () => clearTimeout(timer);
  }, [project, options, compile]);

  const setOption = (key: string, value: string) => {
    const next = { ...options, [key]: value.trim() };
    setOptions(next);
    localStorage.setItem(SAVED_OPTIONS, JSON.stringify(next));
  };

  const format = useCallback(async () => {
    const text = latest.current.files.find(([n]) => n === activeNow.current)?.[1] ?? "";
    const result: { source?: string; errors?: Diagnostic[] } = await worker.current!("format", text, "");
    if (result.source === undefined) {
      const errors = (result.errors ?? []).map((e) => ({ ...e, file: activeNow.current }));
      return setResult({ contracts: [], errors });
    }
    if (result.source !== text) replace(editor.current!, result.source, { stay: true });
  }, []);

  const load = async (key: string) => {
    const pick = examples.all.find((p) => examples.key(p) === key);
    if (!pick) return;
    const next = await examples.project(pick);
    const now = latest.current;
    persist.current = true;
    if (now.files.length === 1 && next.files.length === 1) {
      // One file for another: an edit of it, which undo takes back.
      const [name, text] = next.files[0];
      move(now.files[0][0], name);
      commit({ files: [[name, now.files[0][1]]], entry: name });
      replace(editor.current!, text);
      setPrevious(undefined);
    } else {
      setPrevious(now);
      show(next);
    }
    editor.current!.focus();
  };

  const restore = () => {
    if (previous) show(previous);
    setPrevious(undefined);
  };

  const share = async () => {
    const { files, entry } = latest.current;
    const params =
      files.length === 1 && entry === "main.lithe"
        ? new URLSearchParams({ code: await pack(files[0][1]) })
        : new URLSearchParams({ project: await pack(JSON.stringify(latest.current)) });
    for (const [key, value] of Object.entries(options)) if (value) params.set(key, value);
    history.replaceState(null, "", `#${params}`);
    await navigator.clipboard.writeText(location.href);
    setStatus("Link copied");
  };

  const jump = (file: string, line: number, column: number) => {
    open(file);
    goTo(editor.current!, line, column);
  };

  const addFile = () => {
    const taken = latest.current.files.map(([n]) => n);
    let name = "lib/module.lithe";
    for (let i = 2; taken.includes(name); i++) name = `lib/module${i}.lithe`;
    const text = stub(name, latest.current.entry);
    states.current.set(name, stateFor(name, text));
    commit({ ...latest.current, files: [...latest.current.files, [name, text]] });
    open(name);
    return name;
  };

  const renameFile = (from: string, typed: string) => {
    const taken = latest.current.files.map(([n]) => n).filter((n) => n !== from);
    const { path, error } = filePath(typed, taken);
    if (!path) return error;
    if (path === from) return;
    const view = editor.current!;
    const shown = from === activeNow.current;
    const old = (shown ? view.state : states.current.get(from)!).doc.toString();
    const { files, entry } = latest.current;
    move(from, path);
    commit({ files: files.map(([n, t]) => [n === from ? path : n, t]), entry: entry === from ? path : entry });
    // A file still as it started gets the starting text for its new name.
    if (old === stub(from, entry)) {
      const text = stub(path, entry === from ? path : entry);
      if (shown) replace(view, text, { kept: false });
      else {
        const state = states.current.get(path)!;
        states.current.set(path, state.update({ changes: { from: 0, to: state.doc.length, insert: text } }).state);
        commit({ ...latest.current, files: latest.current.files.map(([n, t]) => [n, n === path ? text : t]) });
      }
    }
  };

  const deleteFile = (name: string) => {
    const text = latest.current.files.find(([n]) => n === name)?.[1] ?? "";
    if (text.trim() && !confirm(`Delete ${name}?`)) return;
    if (name === activeNow.current) open(latest.current.entry);
    states.current.delete(name);
    named.current.delete(name);
    commit({ ...latest.current, files: latest.current.files.filter(([n]) => n !== name) });
  };

  // The editor binds these keys itself; this is for when it does not have focus.
  useEffect(() => {
    const onKey = (ev: KeyboardEvent) => {
      if (ev.defaultPrevented) return;
      const mod = ev.ctrlKey || ev.metaKey;
      if (mod && ev.key === "Enter") {
        ev.preventDefault();
        compile();
      } else if (mod && ev.shiftKey && ev.key.toLowerCase() === "f") {
        ev.preventDefault();
        format();
      }
    };
    document.addEventListener("keydown", onKey);
    return () => document.removeEventListener("keydown", onKey);
  }, [compile, format]);

  const names = project.files.map(([n]) => n);

  return (
    <div className="lp">
      <style>{CSS + RUN_CSS}</style>
      <div className="lp-bar">
        <button type="button" className="lp-primary" title="Ctrl+Enter" onClick={compile}>
          Compile
        </button>
        <button type="button" title="Ctrl+Shift+F" onClick={format}>
          Format
        </button>
        <button type="button" onClick={share}>
          Share
        </button>
        <select className="lp-examples" aria-label="Load an example" value="" onChange={(ev) => load(ev.target.value)}>
          <option value="" disabled>
            Examples
          </option>
          {examples.PICKS.map(([group, picks]) => (
            <optgroup key={group} label={group}>
              {picks.map((p) => (
                <option key={examples.key(p)} value={examples.key(p)}>
                  {p.title}
                </option>
              ))}
            </optgroup>
          ))}
        </select>
        <BuildOptions
          options={options}
          set={setOption}
          reset={() => {
            setOptions({});
            localStorage.removeItem(SAVED_OPTIONS);
          }}
        />
        {previous && (
          <button type="button" className="lp-quiet" onClick={restore}>
            Restore previous files
          </button>
        )}
        <span className="lp-status" role="status">
          {status}
        </span>
      </div>
      <div className="lp-main">
        <div className="lp-editor-pane">
          <Files
            names={names}
            entry={project.entry}
            active={active}
            errors={(name) => (result?.errors ?? []).filter((e) => (e.file ?? project.entry) === name).length}
            open={open}
            add={addFile}
            rename={renameFile}
            remove={deleteFile}
          />
          <div className="lp-editor" ref={host} />
        </div>
        <section className="lp-output" aria-label="Compiler output">
          <div className="lp-tabs" role="tablist">
            <button type="button" role="tab" aria-selected={tab === "output"} onClick={() => setTab("output")}>
              Output
            </button>
            <button type="button" role="tab" aria-selected={tab === "run"} onClick={() => setTab("run")}>
              Run
            </button>
          </div>
          <div role="tabpanel" hidden={tab !== "output"}>
            {result && <Output result={result} dark={dark} files={names} entry={project.entry} jump={jump} />}
          </div>
          <div role="tabpanel" hidden={tab !== "run"}>
            <Run
              contracts={result?.errors?.length ? [] : (result?.contracts ?? [])}
              project={project}
              evm={options["evm-version"] || "osaka"}
              session={(request) => worker.current!("session", JSON.stringify(request), "")}
              diff={(before, after) =>
                worker.current!(
                  "storage_diff",
                  JSON.stringify({
                    before: { files: Object.fromEntries(before.files), entry: before.entry },
                    after: { files: Object.fromEntries(after.files), entry: after.entry },
                  }),
                  "",
                )
              }
            />
          </div>
        </section>
      </div>
    </div>
  );
}

/** The project's files as tabs: the entry first and kept; others renamed with a double-click. */
function Files({
  names,
  entry,
  active,
  errors,
  open,
  add,
  rename,
  remove,
}: {
  names: string[];
  entry: string;
  active: string;
  errors: (name: string) => number;
  open: (name: string) => void;
  add: () => string;
  rename: (from: string, to: string) => string | undefined;
  remove: (name: string) => void;
}) {
  const [renaming, setRenaming] = useState<string>();
  const [problem, setProblem] = useState<string>();
  const finish = (from: string, to: string) => {
    const error = rename(from, to);
    if (error) return setProblem(error);
    setProblem(undefined);
    setRenaming(undefined);
  };
  return (
    <div className="lp-files" role="tablist" aria-label="Files">
      {names.map((name) => (
        <div key={name} className={`lp-file${name === active ? " lp-file-active" : ""}`}>
          {renaming === name ? (
            <input
              className="lp-file-name"
              aria-label={`Rename ${name}`}
              defaultValue={name}
              autoFocus
              spellCheck={false}
              onFocus={(ev) => ev.target.setSelectionRange(name.lastIndexOf("/") + 1, name.length - ".lithe".length)}
              onBlur={(ev) => finish(name, ev.target.value)}
              onKeyDown={(ev) => {
                if (ev.key === "Enter") finish(name, ev.currentTarget.value);
                if (ev.key === "Escape") {
                  setProblem(undefined);
                  setRenaming(undefined);
                }
              }}
            />
          ) : (
            <button
              type="button"
              role="tab"
              aria-selected={name === active}
              title={
                name === entry
                  ? `${name}: the file that is compiled. Double-click to rename.`
                  : "Double-click to rename"
              }
              onClick={() => open(name)}
              onDoubleClick={() => setRenaming(name)}
            >
              {name}
              {errors(name) > 0 && <span className="lp-file-errors">{errors(name)}</span>}
            </button>
          )}
          {name !== entry && renaming !== name && (
            <button
              type="button"
              className="lp-file-close"
              aria-label={`Delete ${name}`}
              title={`Delete ${name}`}
              onClick={() => remove(name)}
            >
              ×
            </button>
          )}
        </div>
      ))}
      <button
        type="button"
        className="lp-file-add"
        aria-label="Add a file"
        title="Add a file"
        onClick={() => setRenaming(add())}
      >
        +
      </button>
      {problem && <span className="lp-file-problem">{problem}</span>}
    </div>
  );
}

function BuildOptions({
  options,
  set,
  reset,
}: {
  options: Options;
  set: (key: string, value: string) => void;
  reset: () => void;
}) {
  const menu = useRef<HTMLDetailsElement>(null);
  useEffect(() => {
    const close = (ev: PointerEvent) => {
      if (!menu.current?.contains(ev.target as Node)) menu.current?.removeAttribute("open");
    };
    document.addEventListener("pointerdown", close);
    return () => document.removeEventListener("pointerdown", close);
  }, []);
  const changed = Object.values(options).filter(Boolean).length;
  return (
    <details className="lp-menu" ref={menu}>
      <summary>Options{changed > 0 && ` (${changed})`}</summary>
      <div className="lp-panel">
        {BUILD.map((option) => (
          <label key={option.key}>
            {option.label}
            {"choices" in option ? (
              <select value={options[option.key] ?? ""} onChange={(ev) => set(option.key, ev.target.value)}>
                <option value="">{option.default} (default)</option>
                {option.choices.map((choice) => (
                  <option key={choice}>{choice}</option>
                ))}
              </select>
            ) : (
              <input
                value={options[option.key] ?? ""}
                placeholder={option.default}
                onChange={(ev) => set(option.key, ev.target.value)}
                spellCheck={false}
                autoComplete="off"
              />
            )}
          </label>
        ))}
        <button type="button" onClick={reset} disabled={changed === 0}>
          Reset to defaults
        </button>
      </div>
    </details>
  );
}

function Output({
  result,
  dark,
  files,
  entry,
  jump,
}: {
  result: Result;
  dark?: boolean;
  files: string[];
  entry: string;
  jump: (file: string, line: number, column: number) => void;
}) {
  if (result.panic)
    return <p className="lp-panic">{`The compiler crashed. This is a bug in Lithe.\n\n${result.panic}`}</p>;
  const bytes = (hex: string) => (hex.length / 2).toLocaleString();
  return (
    <>
      {result.errors.map((e, i) =>
        files.includes(e.file ?? entry) && e.line > 0 ? (
          <button type="button" key={i} className="lp-error" onClick={() => jump(e.file ?? entry, e.line, e.column)}>
            {e.text}
          </button>
        ) : (
          <p key={i} className="lp-error">
            {e.text}
          </p>
        ),
      )}
      {result.contracts.map((c) => (
        <div key={c.name}>
          <h2>{c.name}</h2>
          <p className="lp-sizes">
            {bytes(c.deployed)} bytes runtime · {bytes(c.bytecode)} bytes creation
            {c.facets > 0 && ` · ${c.facets} facet${c.facets > 1 ? "s" : ""}`}
          </p>
          {c.warnings.map((w, i) => (
            <p key={i} className="lp-warning">
              {w}
            </p>
          ))}
          <Section title="ABI" text={JSON.stringify(c.abi, null, 2)} open>
            <Highlighted code={JSON.stringify(c.abi, null, 2)} dark={dark} />
          </Section>
          <Section title="Selectors" text={c.methods.map(([sig, sel]) => `0x${sel}  ${sig}`).join("\n")} />
          <Section title="Runtime bytecode" text={`0x${c.deployed}`} hex />
          <Section title="Creation bytecode" text={`0x${c.bytecode}`} hex />
        </div>
      ))}
    </>
  );
}

function Section({
  title,
  text,
  open,
  hex,
  children,
}: {
  title: string;
  text: string;
  open?: boolean;
  hex?: boolean;
  children?: ReactNode;
}) {
  const [copied, setCopied] = useState(false);
  const copy = async (ev: MouseEvent) => {
    ev.preventDefault();
    await navigator.clipboard.writeText(text);
    setCopied(true);
    setTimeout(() => setCopied(false), 1200);
  };
  return (
    <details className="lp-section" open={open}>
      <summary>
        {title}
        <button type="button" onClick={copy}>
          {copied ? "Copied" : "Copy"}
        </button>
      </summary>
      <pre className={hex ? "lp-hex" : undefined}>{children ?? text}</pre>
    </details>
  );
}

const CSS = `
.lp {
  position: fixed;
  inset: calc(var(--vocs-spacing-topNav) + var(--vocs-spacing-banner, 0px)) 0 0 0;
  display: flex;
  flex-direction: column;
  background: var(--vocs-background-color-primary);
  color: var(--vocs-text-color-primary);
  --lp-line: var(--vocs-border-color-primary);
}
.lp button { font: inherit; font-size: .875rem; padding: .3rem .8rem; border: 1px solid var(--lp-line); border-radius: .375rem; background: transparent; color: inherit; cursor: pointer; }
.lp button:hover, .lp button:focus-visible { border-color: var(--vocs-color-accent); }
.lp .lp-primary { background: var(--vocs-color-accent); border-color: var(--vocs-color-accent); color: light-dark(#fff, #000); }
.lp-bar { display: flex; align-items: center; gap: .5rem; padding: .5rem 1rem; border-bottom: 1px solid var(--lp-line); flex-wrap: wrap; }
.lp select, .lp input { font: inherit; font-size: .875rem; padding: .3rem .5rem; border: 1px solid var(--lp-line); border-radius: .375rem; background: var(--vocs-background-color-primary); color: inherit; }
.lp-menu { position: relative; }
.lp-menu > summary { list-style: none; font-size: .875rem; padding: .3rem .8rem; border: 1px solid var(--lp-line); border-radius: .375rem; cursor: pointer; }
.lp-menu > summary::-webkit-details-marker { display: none; }
.lp-menu > summary:hover, .lp-menu > summary:focus-visible, .lp-menu[open] > summary { border-color: var(--vocs-color-accent); }
.lp-panel { position: absolute; z-index: 10; top: calc(100% + .375rem); left: 0; display: grid; gap: .75rem; padding: .75rem; min-width: 27rem; border: 1px solid var(--lp-line); border-radius: .5rem; background: var(--vocs-background-color-surface); box-shadow: 0 8px 24px rgb(0 0 0 / .15); }
.lp-panel label { display: grid; gap: .25rem; font-size: .8125rem; color: var(--vocs-text-color-secondary); }
.lp-panel input { font-family: var(--vocs-font-mono); }
.lp-panel button { justify-self: start; }
.lp button:disabled { opacity: .5; cursor: default; }
.lp-status { margin-left: auto; color: var(--vocs-text-color-muted); font-size: .875rem; }
.lp-main { flex: 1; display: grid; grid-template-columns: 1fr 1fr; min-height: 0; }
.lp-editor-pane { display: flex; flex-direction: column; min-height: 0; min-width: 0; border-right: 1px solid var(--lp-line); }
.lp-editor { flex: 1; min-height: 0; overflow: hidden; }
.lp-files { display: flex; align-items: stretch; gap: 0; border-bottom: 1px solid var(--lp-line); overflow-x: auto; flex: none; }
.lp-file { display: flex; align-items: center; border-right: 1px solid var(--lp-line); }
.lp .lp-file > button[role="tab"] { border: 0; border-radius: 0; padding: .35rem .75rem; font: .8125rem var(--vocs-font-mono); color: var(--vocs-text-color-secondary); display: inline-flex; align-items: center; gap: .4rem; white-space: nowrap; border-bottom: 2px solid transparent; }
.lp .lp-file-active > button[role="tab"] { color: var(--vocs-text-color-heading); border-bottom-color: var(--vocs-color-accent); }
.lp .lp-file-close { border: 0; padding: 0 .5rem 0 0; color: var(--vocs-text-color-muted); font-size: 1rem; line-height: 1; }
.lp .lp-file-close:hover { color: var(--vocs-text-color-heading); }
.lp .lp-file-name { font: .8125rem var(--vocs-font-mono); margin: .2rem .4rem; padding: .1rem .3rem; width: 14rem; }
.lp .lp-file-add { border: 0; border-radius: 0; padding: .35rem .75rem; color: var(--vocs-text-color-muted); font-size: 1rem; line-height: 1; }
.lp .lp-file-add:hover { color: var(--vocs-text-color-heading); }
.lp-file-errors { font: 500 .6875rem/1 var(--vocs-font-sans, system-ui); padding: .15rem .35rem; border-radius: 999px; background: var(--vocs-color-red); color: #fff; }
.lp-file-problem { align-self: center; padding: 0 .75rem; font-size: .75rem; color: var(--vocs-color-red); white-space: nowrap; }
.lp-output { overflow: auto; padding: 1rem; }
.lp-output h2 { font-size: 1.125rem; font-weight: 600; margin: 0 0 .25rem; }
.lp-output div + div h2 { margin-top: 1.5rem; }
.lp-sizes { color: var(--vocs-text-color-muted); font-size: .875rem; margin: 0 0 .75rem; }
.lp .lp-error, .lp-warning, .lp-panic { display: block; width: 100%; text-align: left; font: .8125rem/1.5 var(--vocs-font-mono); white-space: pre-wrap; margin: 0 0 .5rem; padding: .5rem .75rem; border: 0; border-left: 3px solid var(--vocs-color-red); border-radius: 0; }
.lp button.lp-error:hover, .lp button.lp-error:focus-visible { background: var(--vocs-background-color-surface); border-color: var(--vocs-color-red); }
.lp-warning { border-left-color: var(--vocs-color-yellow); }
.lp-section { border: 1px solid var(--lp-line); border-radius: .375rem; margin-bottom: .5rem; }
.lp-section > summary { padding: .4rem .75rem; cursor: pointer; display: flex; align-items: center; }
.lp-section > summary button { margin-left: auto; padding: 0 .5rem; font-size: .8125rem; }
.lp-section > pre { font: .8125rem/1.5 var(--vocs-font-mono); margin: 0; padding: .5rem .75rem; border-top: 1px solid var(--lp-line); overflow: auto; max-height: 24rem; }
.lp-section > pre.lp-hex { white-space: pre-wrap; word-break: break-all; }
@media (max-width: 800px) {
  .lp-main { grid-template-columns: 1fr; grid-template-rows: 1fr 1fr; }
  .lp-editor-pane { border-right: 0; border-bottom: 1px solid var(--lp-line); }
  .lp-bar { position: relative; }
  .lp-menu { position: static; }
  .lp-panel { left: 1rem; right: 1rem; top: calc(100% - .25rem); min-width: 0; }
}
`;
