import { indentWithTab, isolateHistory } from "@codemirror/commands";
import { setDiagnostics } from "@codemirror/lint";
import { Compartment, EditorState, Prec, RangeSetBuilder, Transaction } from "@codemirror/state";
import { Decoration, type DecorationSet, EditorView, keymap, ViewPlugin, type ViewUpdate } from "@codemirror/view";
import { basicSetup } from "codemirror";
import { createHighlighterCoreSync, type HighlighterCore } from "shiki/core";
import { createJavaScriptRegexEngine } from "shiki/engine/javascript";
import json from "shiki/langs/json.mjs";
import githubDark from "shiki/themes/github-dark-dimmed.mjs";
import githubLight from "shiki/themes/github-light.mjs";
import lithe from "../../../extensions/lithe.tmLanguage.json";

let highlighter: HighlighterCore | undefined;

/** `code`'s tokens, a list a line, colored as the docs' code blocks are. */
export function tokens(code: string, lang: "lithe" | "json", dark: boolean) {
  highlighter ??= createHighlighterCoreSync({
    themes: [githubLight, githubDark],
    langs: [lithe as never, json],
    engine: createJavaScriptRegexEngine(),
  });
  return highlighter.codeToTokensBase(code, { lang, theme: dark ? "github-dark-dimmed" : "github-light" });
}

const marks = new Map<string, Decoration>();

function decorate(state: EditorState): DecorationSet {
  const builder = new RangeSetBuilder<Decoration>();
  let at = 0;
  for (const line of tokens(state.doc.toString(), "lithe", state.facet(EditorView.darkTheme))) {
    for (const { content, color } of line) {
      if (content && color) {
        let mark = marks.get(color);
        if (!mark) marks.set(color, (mark = Decoration.mark({ attributes: { style: `color: ${color}` } })));
        builder.add(at, at + content.length, mark);
      }
      at += content.length;
    }
    at += 1;
  }
  return builder.finish();
}

// simplify: the whole text is tokenized on every change, about 10 ms per 250 lines. Past a few
// thousand lines typing lags; tokenizing only the changed lines, from the grammar state before
// them, would fix that.
const highlighting = ViewPlugin.fromClass(
  class {
    decorations: DecorationSet;
    constructor(view: EditorView) {
      this.decorations = decorate(view.state);
    }
    update(update: ViewUpdate) {
      const retheme = update.startState.facet(EditorView.darkTheme) !== update.state.facet(EditorView.darkTheme);
      if (update.docChanged || retheme) this.decorations = decorate(update.state);
    }
  },
  { decorations: (plugin) => plugin.decorations },
);

const scheme = new Compartment();

const theme = EditorView.theme({
  "&": { height: "100%", fontSize: ".875rem", backgroundColor: "transparent" },
  "&.cm-focused": { outline: "none" },
  ".cm-scroller": { fontFamily: "var(--vocs-font-mono)", lineHeight: "1.5" },
  ".cm-content": { padding: ".75rem 0", caretColor: "var(--vocs-text-color-heading)" },
  ".cm-cursor, .cm-dropCursor": { borderLeftColor: "var(--vocs-text-color-heading)" },
  ".cm-gutters": { backgroundColor: "transparent", border: "none", color: "var(--vocs-text-color-muted)" },
  ".cm-lineNumbers .cm-gutterElement": { padding: "0 .75rem 0 1rem" },
  // Folding needs a parser; the TextMate grammar only colors.
  ".cm-foldGutter": { display: "none !important" },
});

type File = {
  doc: string;
  label: string;
  /** Each change to the text. `kept` is whether it is one the undo history holds. */
  change: (text: string, kept: boolean) => void;
  compile: () => void;
  format: () => void;
};

/** A file's editor state: its text, undo history, selection, and errors. One editor shows one at a time. */
export function fileState({ doc, label, change, compile, format }: File) {
  return EditorState.create({
    doc,
    extensions: [
      Prec.highest(
        keymap.of([
          { key: "Mod-Enter", run: () => (compile(), true) },
          { key: "Mod-Shift-f", run: () => (format(), true) },
        ]),
      ),
      basicSetup,
      keymap.of([indentWithTab]),
      highlighting,
      scheme.of(EditorView.darkTheme.of(document.documentElement.dataset.vocsTheme === "dark")),
      theme,
      EditorView.contentAttributes.of({ "aria-label": label }),
      EditorView.updateListener.of((update) => {
        if (!update.docChanged) return;
        const kept = update.transactions.every((tr) => tr.annotation(Transaction.addToHistory) !== false);
        change(update.state.doc.toString(), kept);
      }),
    ],
  });
}

export const createEditor = (parent: HTMLElement, state: EditorState) => new EditorView({ parent, state });

export function setDark(view: EditorView, dark: boolean) {
  view.dispatch({ effects: scheme.reconfigure(EditorView.darkTheme.of(dark)) });
}

/** Replaces the text, as an undoable edit of its own unless `kept` is false, with the cursor at the top or on its line. */
export function replace(view: EditorView, text: string, { kept = true, stay = false } = {}) {
  const line = view.state.doc.lineAt(view.state.selection.main.head).number;
  view.dispatch({
    changes: { from: 0, to: view.state.doc.length, insert: text },
    annotations: kept ? isolateHistory.of("full") : Transaction.addToHistory.of(false),
  });
  const doc = view.state.doc;
  view.dispatch({ selection: { anchor: stay ? doc.line(Math.min(line, doc.lines)).from : 0 }, scrollIntoView: true });
}

function place(state: EditorState, line: number, column: number) {
  const at = state.doc.line(Math.min(Math.max(line, 1), state.doc.lines));
  return Math.min(at.from + Math.max(column - 1, 0), at.to);
}

export function goTo(view: EditorView, line: number, column: number) {
  view.dispatch({ selection: { anchor: place(view.state, line, column) }, scrollIntoView: true });
  view.focus();
}

/** Underlines each error at its place, through the word that starts there. */
export function showErrors(view: EditorView, errors: { line: number; column: number; message: string }[]) {
  const { state } = view;
  const diagnostics = errors
    .filter((e) => e.line > 0 && e.line <= state.doc.lines)
    .map((e) => {
      const from = place(state, e.line, e.column);
      const end = state.wordAt(from)?.to ?? from + 1;
      return { from, to: Math.min(end, state.doc.lineAt(from).to), severity: "error" as const, message: e.message };
    });
  view.dispatch(setDiagnostics(state, diagnostics));
}
