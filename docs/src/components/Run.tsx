"use client";

import { type ReactNode, useEffect, useState } from "react";
import type { Project } from "./examples";

export type Contract = {
  name: string;
  bytecode: string;
  deployed: string;
  abi: Item[];
  methods: [string, string][];
  warnings: string[];
  storage: unknown[];
  facets: number;
  plan: unknown;
  /** An upgradeable contract's migrations, as ABI functions. */
  migrations: Item[];
};
type Param = { name: string; type: string; components?: Param[] };
type Item = { type: string; name?: string; inputs?: Param[]; outputs?: Param[]; stateMutability?: string };
type Entry = { slot: string; domain: string | null; name: string; value: string; shown: string };
type Account = { address: string; name: string | null; balance: string; entries: Entry[] };
type Outcome = {
  ok?: boolean;
  gas?: number;
  error?: string;
  returns?: { name: string; type: string; value: string }[];
  events?: { from: string; text: string }[];
  address?: string;
  storage?: Account[];
  panic?: string;
  reset?: boolean;
  block?: number;
  time?: number;
  /** The facets a deploy put on the chain first, or found there. */
  facets?: { name: string; address: string; gas?: number; ok?: boolean; there?: boolean }[];
  /** The code behind an upgradeable contract's proxy. */
  implementation?: { address: string; gas: number };
};
type Request =
  | { op: "deploy"; contract: string; args: string[]; value: string; caller: string }
  | { op: "call"; to: string; function: string; args: string[]; value: string; caller: string }
  | { op: "upgrade"; to: string; contract: string; migration: string; args: string[]; value: string; caller: string };
/** A storage entry a transaction changed: `from` is gone when it set a new one, `to` when it cleared one. */
type Change = { account: string; label: string; from?: string; to?: string };
type Tx = Outcome & { n: number; title: string; request: Request; changes: Change[] };
/** A view's last answer, and the arguments it was asked with, which it is asked again after each transaction. */
type Read = { args: string[]; out: Outcome };

/** The chain's funded callers, as `playground/src/session.rs` makes them. */
const CALLERS = [
  { name: "Alice", address: "0x1111111111111111111111111111111111111111" },
  { name: "Bob", address: "0x2222222222222222222222222222222222222222" },
  { name: "Carol", address: "0x3333333333333333333333333333333333333333" },
];

const same = (a: string, b: string) => a.toLowerCase() === b.toLowerCase();
const short = (address: string) => `${address.slice(0, 6)}…${address.slice(-4)}`;

/** `text` with the callers' and contracts' addresses named: `balances[Bob]`. */
function named(text: string, accounts: Account[]) {
  const names = [
    { name: "0x0", address: "0x0000000000000000000000000000000000000000" },
    ...CALLERS,
    ...accounts.filter((a) => a.name).map((a) => ({ name: a.name!, address: a.address })),
  ];
  return names.reduce((out, { name, address }) => out.replace(new RegExp(address, "gi"), name), text);
}

/** A parameter's type as the session reads its text: tuples as `(a,b)`. */
const typeOf = (p: Param): string =>
  p.type.startsWith("tuple") ? `(${(p.components ?? []).map(typeOf).join(",")})${p.type.slice(5)}` : p.type;
const signature = (f: Item) => `${f.name}(${(f.inputs ?? []).map(typeOf).join(",")})`;
const reads = (f: Item) => f.stateMutability === "view" || f.stateMutability === "pure";
/** An upgradeable contract's code is an implementation behind a proxy, and its `deploy` the proxy's initializer. */
const upgradeable = (c: Contract) => ["proxiableUUID", "upgradeToAndCall"].every((n) => c.abi.some((i) => i.type === "function" && i.name === n));
const initializer = (c: Contract) =>
  upgradeable(c) ? c.abi.find((i) => i.type === "function" && i.name === "deploy") : c.abi.find((i) => i.type === "constructor");
const hint = (p: Param) => {
  const ty = typeOf(p);
  if (ty === "bool") return "true or false";
  if (ty.endsWith("]")) return `${ty}: [a, b]`;
  if (ty.startsWith("(")) return `${ty}: (a, b)`;
  return ty;
};

function ether(wei: string) {
  const n = BigInt(wei);
  const whole = n / 10n ** 18n;
  const rest = (n % 10n ** 18n).toString().padStart(18, "0").replace(/0+$/, "").slice(0, 6);
  return `${whole}${rest ? `.${rest}` : ""} ETH`;
}

const entryKey = (address: string, e: Entry) => `${address}|${e.slot}|${e.name}`;

export function Run({
  contracts,
  project,
  evm,
  session,
  diff,
}: {
  contracts: Contract[];
  /** The files the contracts were compiled from. */
  project: Project;
  evm: string;
  session: (request: object) => Promise<Outcome>;
  /** What upgrading from one version of the files to another does to storage. */
  diff: (before: Project, after: Project) => Promise<{ text?: string; compatible?: boolean; errors?: { text: string }[] }>;
}) {
  const [caller, setCaller] = useState(CALLERS[0].address);
  const [accounts, setAccounts] = useState<Account[]>([]);
  // What each entry showed before the last transaction, for those it changed or cleared.
  const [before, setBefore] = useState<Map<string, Entry | null>>(new Map());
  // The contracts deployed, by name, as they were compiled then: later edits don't change them.
  const [deployedFrom, setDeployedFrom] = useState<Record<string, Contract>>({});
  // The files each contract on the chain was compiled from, to check an upgrade against.
  const [sources, setSources] = useState<Record<string, Project>>({});
  const [history, setHistory] = useState<Tx[]>([]);
  const [results, setResults] = useState<Record<string, Tx>>({});
  const [views, setViews] = useState<Record<string, Read>>({});
  const [busy, setBusy] = useState(false);
  const [pick, setPick] = useState(0);
  const [tabs, setTabs] = useState<Record<string, string>>({});

  // The chain's time is the page's clock.
  const [chain, setChain] = useState<{ block: number; time: number }>();
  const ask = async (request: object, from = caller) => {
    const out = await session({ ...request, caller: from, evm, now: Math.floor(Date.now() / 1000) });
    if (out.block !== undefined && out.time !== undefined) setChain({ block: out.block, time: out.time });
    return out;
  };

  /** Asks every view again: those that take nothing, and those asked before, with their arguments. */
  const refresh = async (now: Account[], from: Record<string, Contract>, asked: Record<string, Read>) => {
    const next: Record<string, Read> = {};
    for (const account of now) {
      const contract = account.name ? from[account.name] : undefined;
      for (const f of contract?.abi.filter((i) => i.type === "function" && reads(i)) ?? []) {
        const key = `${account.address}:${signature(f)}`;
        const args = asked[key]?.args ?? (f.inputs?.length ? undefined : []);
        if (!args) continue;
        next[key] = { args, out: await ask({ op: "call", to: account.address, function: signature(f), args, value: "" }) };
      }
    }
    setViews(next);
  };

  /** Runs one transaction, and shows what it did to every account. */
  const transact = async (
    request: Request,
    title: string,
    state: { accounts: Account[]; from: Record<string, Contract>; history: Tx[] },
  ) => {
    const out = await ask(
      request.op === "call" ? request : { ...request, contract: state.from[request.contract], family: Object.values(state.from) },
      request.caller,
    );
    // A request the chain could not run, as for an argument that does not parse, is no transaction.
    const ran = out.ok !== undefined;
    const tx: Tx = { ...out, n: ran ? state.history.length + 1 : 0, title, request, changes: [] };
    if (out.reset) tx.error = `The chain crashed and starts over. This is a bug in the playground.\n\n${out.panic}`;
    const now = out.reset ? [] : (out.storage ?? state.accounts);
    if (out.storage) {
      const was = new Map(state.accounts.flatMap((a) => a.entries.map((e) => [entryKey(a.address, e), e] as const)));
      const is = new Set(now.flatMap((a) => a.entries.map((e) => entryKey(a.address, e))));
      const moved = new Map<string, Entry | null>();
      for (const a of now) for (const e of a.entries) if (was.get(entryKey(a.address, e))?.value !== e.value) moved.set(entryKey(a.address, e), was.get(entryKey(a.address, e)) ?? null);
      for (const [key, e] of was) if (!is.has(key)) moved.set(key, e);
      setBefore(moved);
      const label = (e: Entry) => (e.domain ? `${e.domain}.${e.name}` : short(e.slot));
      for (const a of now)
        for (const e of a.entries)
          if (moved.has(entryKey(a.address, e))) tx.changes.push({ account: a.address, label: label(e), from: moved.get(entryKey(a.address, e))?.shown, to: e.shown });
      for (const [key, e] of moved) if (e && !is.has(key)) tx.changes.push({ account: key.split("|")[0], label: label(e), from: e.shown });
    }
    setAccounts(now);
    return { tx, accounts: now, history: ran ? [...state.history, tx] : state.history };
  };

  const run = async (key: string, request: Request, title: string) => {
    setBusy(true);
    // A deploy or an upgrade puts the code as it is now on the chain.
    const now = request.op === "call" ? [] : request.op === "deploy" ? contracts : contracts.filter((c) => c.name === request.contract);
    const from = { ...deployedFrom, ...Object.fromEntries(now.map((c) => [c.name, c])) };
    const done = await transact(request, title, { accounts, from, history });
    // An upgrade that reverts leaves the proxy on the code it had.
    const kept = request.op === "upgrade" && !done.tx.ok ? deployedFrom : from;
    if (request.op !== "call" && done.tx.ok) setSources((all) => ({ ...all, ...Object.fromEntries(now.map((c) => [c.name, project])) }));
    setDeployedFrom(kept);
    setHistory(done.history);
    setResults((all) => ({ ...all, [key]: done.tx }));
    await refresh(done.accounts, kept, views);
    setBusy(false);
  };

  const query = async (key: string, to: string, f: Item, args: string[]) => {
    const out = await ask({ op: "call", to, function: signature(f), args, value: "" });
    setViews((all) => ({ ...all, [key]: { args, out } }));
  };

  const reset = async () => {
    await session({ op: "reset" });
    setAccounts([]);
    setBefore(new Map());
    setHistory([]);
    setResults({});
    setViews({});
    setDeployedFrom({});
    setSources({});
    setChain(undefined);
  };

  /** Starts the chain over, and runs every transaction again on the code as it is now. */
  const replay = async () => {
    setBusy(true);
    await session({ op: "reset" });
    const from = Object.fromEntries(contracts.map((c) => [c.name, c]));
    let state = { accounts: [] as Account[], from, history: [] as Tx[] };
    const last: Record<string, Tx> = {};
    for (const tx of history) {
      const done = await transact(tx.request, tx.title, state);
      state = { ...state, accounts: done.accounts, history: done.history };
      last[resultKey(tx.request)] = done.tx;
    }
    setDeployedFrom(from);
    setSources(Object.fromEntries(contracts.map((c) => [c.name, project])));
    setHistory(state.history);
    setResults(last);
    setBefore(new Map());
    await refresh(state.accounts, from, views);
    setBusy(false);
  };


  const contract = contracts[Math.min(pick, contracts.length - 1)];
  const constructor = contract && initializer(contract);
  const instances = accounts.filter((a) => a.name && deployedFrom[a.name]);
  const others = accounts.filter((a) => !instances.includes(a));
  const stale = Object.values(deployedFrom).filter((d) => contracts.find((c) => c.name === d.name && c.bytecode !== d.bytecode));
  const callRequest = (to: string, f: Item, args: string[], value: string): Request => ({ op: "call", to, function: signature(f), args, value, caller });

  return (
    <div className="lp-run" aria-busy={busy}>
      <datalist id="lp-addresses">
        {[...CALLERS, ...instances.map((a) => ({ name: a.name!, address: a.address }))].map((a) => (
          <option key={a.address} value={a.address}>
            {a.name}
          </option>
        ))}
      </datalist>

      <div className="lp-run-bar">
        <div className="lp-segmented" role="radiogroup" aria-label="Call as">
          <span className="lp-muted">Call as</span>
          {CALLERS.map((c) => (
            <button type="button" role="radio" key={c.address} aria-checked={same(caller, c.address)} title={c.address} onClick={() => setCaller(c.address)}>
              <Avatar address={c.address} />
              {c.name}
            </button>
          ))}
        </div>
        {chain && chain.time > 0 && (
          <span className="lp-muted lp-chain" title={new Date(chain.time * 1000).toString()}>
            block {chain.block} · {new Date(chain.time * 1000).toLocaleTimeString()}
          </span>
        )}
        <button type="button" className="lp-quiet" onClick={reset} disabled={busy || history.length === 0}>
          Reset chain
        </button>
      </div>

      {stale.length > 0 && history.length > 0 && (
        <div className="lp-banner">
          <span>
            {stale.map((c) => c.name).join(", ")} changed since you deployed {stale.length > 1 ? "them" : "it"}.
            {stale.some(upgradeable) && " An upgradeable contract can also be upgraded in place, below, keeping its address and storage."}
          </span>
          <button type="button" className="lp-primary" onClick={replay} disabled={busy || contracts.length === 0}>
            Replay {history.length} transaction{history.length > 1 ? "s" : ""} on the new code
          </button>
        </div>
      )}

      <section className="lp-card">
        <header className="lp-card-head">
          <h3>Deploy</h3>
          {contracts.length > 1 && (
            <select aria-label="Contract to deploy" value={pick} onChange={(ev) => setPick(Number(ev.target.value))}>
              {contracts.map((c, i) => (
                <option key={c.name} value={i}>
                  {c.name}
                </option>
              ))}
            </select>
          )}
        </header>
        {!contract ? (
          <p className="lp-muted">Fix the errors to deploy.</p>
        ) : (
          <Form
            key={contract.name}
            params={constructor?.inputs ?? []}
            payable={constructor?.stateMutability === "payable"}
            action={`Deploy ${contract.name}`}
            primary
            busy={busy}
            run={(args, value) => run("deploy", { op: "deploy", contract: contract.name, args, value, caller }, `deploy ${contract.name}(${args.join(", ")})`)}
          >
            {results.deploy && <Outcome tx={results.deploy} accounts={accounts} />}
          </Form>
        )}
      </section>

      {instances.map((account) => {
        const functions = deployedFrom[account.name!].abi.filter((i) => i.type === "function");
        const made = history.find((tx) => tx.address && same(tx.address, account.address));
        const txs = history.filter((tx) => (tx.address && same(tx.address, account.address)) || (tx.request.op === "call" && same(tx.request.to, account.address)));
        const moved = [...before.keys()].filter((key) => key.startsWith(`${account.address}|`)).length;
        const tab = tabs[account.address] ?? "write";
        const values = functions.filter((f) => reads(f) && !f.inputs?.length);
        const queries = functions.filter((f) => reads(f) && f.inputs?.length);
        // The initializer runs once, as the proxy is created; through the proxy it only reverts.
        const writes = functions.filter((f) => !reads(f) && !(upgradeable(deployedFrom[account.name!]) && f.name === "deploy"));
        const panel = (id: string, label: ReactNode) => (
          <button type="button" role="tab" aria-selected={tab === id} onClick={() => setTabs((all) => ({ ...all, [account.address]: id }))}>
            {label}
          </button>
        );
        return (
          <section className="lp-card" key={account.address}>
            <header className="lp-card-head">
              <Avatar address={account.address} size={20} />
              <h3>{account.name}</h3>
              <Address address={account.address} />
              <span className="lp-muted lp-right">
                {ether(account.balance)}
                {made && ` · deployed in #${made.n}`}
              </span>
            </header>
            {upgradeable(deployedFrom[account.name!]) && stale.some((c) => c.name === account.name) && (
              <Upgrade
                key={contracts.find((c) => c.name === account.name)?.bytecode}
                next={contracts.find((c) => c.name === account.name)!}
                before={sources[account.name!]}
                after={project}
                diff={diff}
                busy={busy}
                result={results[`${account.address}:upgrade`]}
                accounts={accounts}
                run={(migration, args) =>
                  run(
                    `${account.address}:upgrade`,
                    { op: "upgrade", to: account.address, contract: account.name!, migration, args, value: "", caller },
                    `upgrade ${account.name}${migration ? ` with ${migration}(${args.join(", ")})` : ""}`,
                  )
                }
              />
            )}
            <div className="lp-subtabs" role="tablist" aria-label={`${account.name} views`}>
              {panel("state", <>State{moved > 0 && <span className="lp-badge">{moved}</span>}</>)}
              {panel("read", <>Read<span className="lp-count">{values.length + queries.length}</span></>)}
              {panel("write", <>Write<span className="lp-count">{writes.length}</span></>)}
              {panel("history", <>History{txs.length > 0 && <span className="lp-count">{txs.length}</span>}</>)}
            </div>

            {/* Every panel stays mounted, so a form keeps what was typed in it across tabs. */}
            <div role="tabpanel" hidden={tab !== "state"}>
              <State account={account} accounts={accounts} before={before} />
            </div>

            <div role="tabpanel" hidden={tab !== "read"}>
              <>
                {values.length > 0 && (
                  <dl className="lp-values">
                    {values.map((f) => {
                      const view = views[`${account.address}:${signature(f)}`];
                      return (
                        <div key={signature(f)}>
                          <dt>{f.name}</dt>
                          <dd>{view ? <Answer out={view.out} accounts={accounts} /> : <span className="lp-muted">…</span>}</dd>
                          <dd className="lp-gas">{view && <Gas out={view.out} />}</dd>
                        </div>
                      );
                    })}
                  </dl>
                )}
                {queries.map((f) => {
                  const key = `${account.address}:${signature(f)}`;
                  const view = views[key];
                  return (
                    <Fn key={key} f={f} summary={view && <Asked f={f} view={view} accounts={accounts} />}>
                      <Form params={f.inputs ?? []} payable={false} action="Query" busy={busy} run={(args) => query(key, account.address, f, args)} />
                    </Fn>
                  );
                })}
                {values.length + queries.length === 0 && <p className="lp-muted">No view functions.</p>}
              </>
            </div>

            <div role="tabpanel" hidden={tab !== "write"}>
              <>
                {writes.map((f) => {
                  const key = `${account.address}:${signature(f)}`;
                  const send = (args: string[], value: string) => run(key, callRequest(account.address, f, args, value), `${account.name}.${f.name}(${args.join(", ")})`);
                  const bare = !f.inputs?.length && f.stateMutability !== "payable";
                  return (
                    <Fn
                      key={key}
                      f={f}
                      bare={bare}
                      summary={
                        bare && (
                          <button type="button" className="lp-primary lp-small" disabled={busy} onClick={() => send([], "")}>
                            Send
                          </button>
                        )
                      }
                      footer={results[key] && <Outcome tx={results[key]} accounts={accounts} />}
                    >
                      {!bare && <Form params={f.inputs ?? []} payable={f.stateMutability === "payable"} action="Send" primary busy={busy} run={send} />}
                    </Fn>
                  );
                })}
                {writes.length === 0 && <p className="lp-muted">No functions that change state.</p>}
              </>
            </div>

            <div role="tabpanel" hidden={tab !== "history"}>
              <>
                {txs.length === 0 && <p className="lp-muted">No transactions yet.</p>}
                {[...txs].reverse().map((tx) => (
                  <details key={tx.n} className="lp-tx">
                    <summary>
                      <span className={tx.ok ? "lp-ok" : "lp-fail"}>{tx.ok ? "✓" : "✗"}</span>
                      <span className="lp-muted">#{tx.n}</span>
                      <Avatar address={tx.request.caller} />
                      <code>{named(tx.title, accounts)}</code>
                      {tx.gas !== undefined && <span className="lp-muted lp-right">{tx.gas.toLocaleString()} gas</span>}
                    </summary>
                    <Outcome tx={tx} accounts={accounts} bare />
                  </details>
                ))}
              </>
            </div>
          </section>
        );
      })}

      {others.length > 0 && (
        <section className="lp-card">
          <header className="lp-card-head">
            <h3>Other accounts</h3>
          </header>
          {others.map((account) => (
            <div key={account.address} className="lp-other">
              <header className="lp-card-head">
                <Avatar address={account.address} />
                <Address address={account.address} />
                <span className="lp-muted">{ether(account.balance)}</span>
              </header>
              <State account={account} accounts={accounts} before={before} />
            </div>
          ))}
        </section>
      )}
    </div>
  );
}

const resultKey = (request: Request) =>
  request.op === "deploy" ? "deploy" : request.op === "upgrade" ? `${request.to}:upgrade` : `${request.to}:${request.function}`;

/** 32 bits of `text`, FNV-1a. */
function hash(text: string) {
  let h = 0x811c9dc5;
  for (const c of text.toLowerCase()) h = Math.imul(h ^ c.charCodeAt(0), 0x01000193);
  return h >>> 0;
}

/** A mirrored 5×5 pattern and a hue, both from the address, so each account looks its own. Hues skip
 * red and green, which mark failure and success. */
function Avatar({ address, size = 16 }: { address: string; size?: number }) {
  let seed = hash(address);
  const next = () => ((seed = Math.imul(seed ^ (seed >>> 15), 0x2c1b3c6d) >>> 0), seed);
  const hues = [35, 50, 190, 210, 230, 255, 280, 300, 320];
  const hue = hues[next() % hues.length];
  const cells: [number, number][] = [];
  for (let y = 0; y < 5; y++)
    for (let x = 0; x < 3; x++) if (next() % 2) cells.push([x, y], ...(x < 2 ? [[4 - x, y] as [number, number]] : []));
  return (
    <svg className="lp-avatar" width={size} height={size} viewBox="0 0 5 5" aria-hidden="true">
      <rect width="5" height="5" fill={`hsl(${hue} 70% 88%)`} />
      {cells.map(([x, y]) => (
        <rect key={`${x},${y}`} x={x} y={y} width="1" height="1" fill={`hsl(${hue} 55% 42%)`} />
      ))}
    </svg>
  );
}

/** The new version of an upgradeable contract: what it does to storage, and the upgrade, with a migration if it has any. */
function Upgrade({
  next,
  before,
  after,
  diff,
  busy,
  result,
  accounts,
  run,
}: {
  next: Contract;
  before?: Project;
  after: Project;
  diff: (before: Project, after: Project) => Promise<{ text?: string; compatible?: boolean; errors?: { text: string }[] }>;
  busy: boolean;
  result?: Tx;
  accounts: Account[];
  run: (migration: string, args: string[]) => void;
}) {
  const [layout, setLayout] = useState<{ text?: string; compatible?: boolean; errors?: { text: string }[] }>();
  const [migration, setMigration] = useState(next.migrations[0]?.name ?? "");
  useEffect(() => {
    let live = true;
    if (before) diff(before, after).then((answer) => live && setLayout(answer));
    return () => {
      live = false;
    };
  }, [before, after]);
  const chosen = next.migrations.find((m) => m.name === migration);
  return (
    <div className="lp-upgrade">
      <p className="lp-upgrade-head">
        <strong>New code for {next.name}.</strong> Upgrading keeps the proxy's address and storage, and runs the upgrade guard as the caller.
      </p>
      {layout && (
        <details className="lp-layout">
          <summary>
            {layout.errors ? (
              <span className="lp-fail">The storage check failed: {layout.errors[0]?.text}</span>
            ) : layout.compatible ? (
              <span>
                <span className="lp-ok">✓</span> Storage layout compatible
              </span>
            ) : (
              <span className="lp-fail">✗ Storage layout incompatible: the new code reads the old storage wrongly</span>
            )}
          </summary>
          {layout.text && <pre>{layout.text.trim()}</pre>}
        </details>
      )}
      {next.migrations.length > 0 && (
        <label className="lp-upgrade-migration">
          <span className="lp-muted">Migration</span>
          <select value={migration} onChange={(ev) => setMigration(ev.target.value)}>
            <option value="">none</option>
            {next.migrations.map((m) => (
              <option key={m.name} value={m.name}>
                {m.name}({(m.inputs ?? []).map((p) => `${typeOf(p)} ${p.name}`).join(", ")})
              </option>
            ))}
          </select>
        </label>
      )}
      <Form
        key={migration}
        params={chosen?.inputs ?? []}
        payable={false}
        action={layout && layout.compatible === false ? "Upgrade anyway" : "Upgrade"}
        primary
        busy={busy}
        run={(args) => run(migration, args)}
      >
        {result && <Outcome tx={result} accounts={accounts} />}
      </Form>
    </div>
  );
}

function Address({ address }: { address: string }) {
  const [copied, setCopied] = useState(false);
  return (
    <button
      type="button"
      className="lp-address"
      title={`${address}, click to copy`}
      onClick={async () => {
        await navigator.clipboard.writeText(address);
        setCopied(true);
        setTimeout(() => setCopied(false), 1000);
      }}
    >
      {copied ? "copied" : short(address)}
    </button>
  );
}

/** An account's storage, by the storage domain each entry is in, a map's entries under the map. */
function State({ account, accounts, before }: { account: Account; accounts: Account[]; before: Map<string, Entry | null> }) {
  const cleared = [...before]
    .filter(([key, e]) => e && key.startsWith(`${account.address}|`) && !account.entries.some((x) => entryKey(account.address, x) === key))
    .map(([, e]) => ({ ...e!, cleared: true }));
  const entries = [...account.entries, ...cleared];
  if (entries.length === 0) return <p className="lp-muted">Every slot is zero.</p>;
  const domains = Object.entries(Object.groupBy(entries, (e) => e.domain ?? "")).sort(([a], [b]) => (!a ? 1 : !b ? -1 : a.localeCompare(b)));
  return (
    <div className="lp-state">
      {domains.map(([domain, list]) => {
        const fields = Object.entries(Object.groupBy(list!, (e) => (domain ? e.name.split(/[[ ]/)[0] : e.slot)));
        return (
          <div key={domain} className="lp-domain">
            <div className="lp-domain-name">{domain || "unknown slots"}</div>
            {fields.map(([field, items]) => {
              const nested = items!.length > 1 || items![0].name !== field;
              const row = (e: Entry & { cleared?: boolean }, label: ReactNode) => {
                const key = entryKey(account.address, e);
                const was = before.get(key);
                const moved = before.has(key);
                return (
                  <div key={key} className={`lp-entry${moved ? " lp-moved" : ""}`} title={`slot ${e.slot}\n${e.value}`}>
                    <span className="lp-entry-name">{label}</span>
                    <span className="lp-entry-value">
                      {e.cleared ? (
                        <>
                          <s>{named(e.shown, accounts)}</s> <span className="lp-muted">cleared</span>
                        </>
                      ) : (
                        <>
                          {moved && (was ? <s>{named(was.shown, accounts)}</s> : <span className="lp-new">new</span>)} {named(e.shown, accounts)}
                        </>
                      )}
                    </span>
                  </div>
                );
              };
              if (!domain) return row(items![0], short(items![0].slot));
              if (!nested) return row(items![0], field);
              return (
                <div key={field}>
                  <div className="lp-entry">
                    <span className="lp-entry-name">{field}</span>
                    <span className="lp-muted">
                      {items!.length} {items!.length > 1 ? "entries" : "entry"}
                    </span>
                  </div>
                  <div className="lp-nested">{items!.map((e) => row(e, named(e.name.slice(field.length), accounts)))}</div>
                </div>
              );
            })}
          </div>
        );
      })}
    </div>
  );
}

/** A function, folded to its signature until opened. One that takes nothing shows its action on the fold. */
function Fn({ f, bare, summary, footer, children }: { f: Item; bare?: boolean; summary?: ReactNode; footer?: ReactNode; children?: ReactNode }) {
  const head = (
    <>
      <code className="lp-fn-name">{f.name}</code>
      <code className="lp-fn-sig">
        (
        {(f.inputs ?? []).map((p, i) => (
          <span key={i}>
            {i > 0 && ", "}
            {typeOf(p)}
            {p.name && <span className="lp-muted"> {p.name}</span>}
          </span>
        ))}
        )
      </code>
      {f.stateMutability === "payable" && <span className="lp-tag">payable</span>}
      <span className="lp-fn-summary">{summary}</span>
    </>
  );
  if (bare)
    return (
      <div className="lp-fn">
        <div className="lp-fn-head">{head}</div>
        {footer}
      </div>
    );
  return (
    <details className="lp-fn">
      <summary className="lp-fn-head">{head}</summary>
      <div className="lp-fn-body">{children}</div>
      {footer}
    </details>
  );
}

/** A form: a labeled input for each parameter, and for the value a payable call sends. */
function Form({
  params,
  payable,
  action,
  primary,
  busy,
  run,
  children,
}: {
  params: Param[];
  payable: boolean;
  action: string;
  primary?: boolean;
  busy: boolean;
  run: (args: string[], value: string) => void;
  children?: ReactNode;
}) {
  const [args, setArgs] = useState<string[]>(() => params.map(() => ""));
  const [value, setValue] = useState("");
  const go = () => !busy && run(args, value);
  const field = (label: string, type: string, input: ReactNode, i: number | string) => (
    <label key={i} className="lp-field">
      <span className="lp-field-name">{label}</span>
      <span className="lp-field-type">{type}</span>
      {input}
    </label>
  );
  return (
    <form
      className="lp-form"
      onSubmit={(ev) => {
        ev.preventDefault();
        go();
      }}
    >
      {params.map((p, i) =>
        field(
          p.name || `argument ${i + 1}`,
          typeOf(p),
          <input
            placeholder={hint(p)}
            value={args[i] ?? ""}
            list={p.type === "address" ? "lp-addresses" : undefined}
            spellCheck={false}
            autoComplete="off"
            onChange={(ev) => setArgs((all) => all.map((a, j) => (j === i ? ev.target.value : a)))}
          />,
          i,
        ),
      )}
      {payable &&
        field(
          "value",
          "wei",
          <input placeholder="0, or 1.5 ether" value={value} spellCheck={false} autoComplete="off" onChange={(ev) => setValue(ev.target.value)} />,
          "value",
        )}
      <div className="lp-form-actions">
        <button type="submit" className={primary ? "lp-primary" : undefined} disabled={busy}>
          {action}
        </button>
      </div>
      {children}
    </form>
  );
}

/** The arguments a view was last asked with, and its answer, which follows every transaction. */
function Asked({ f, view, accounts }: { f: Item; view: Read; accounts: Account[] }) {
  return (
    <span className="lp-asked">
      <span className="lp-muted">({view.args.map((a) => named(a, accounts)).join(", ")}) →</span> <Answer out={view.out} accounts={accounts} />{" "}
      <Gas out={view.out} />
    </span>
  );
}

/** The gas a call to a view would cost as a transaction. */
function Gas({ out }: { out: Outcome }) {
  return out.gas === undefined ? null : <span className="lp-muted lp-gas">{out.gas.toLocaleString()} gas</span>;
}

/** A view's answer: its values, or why it failed. */
function Answer({ out, accounts }: { out: Outcome; accounts: Account[] }) {
  if (!out.ok) return <span className="lp-fail">{named(out.error ?? out.panic ?? "", accounts)}</span>;
  return (
    <span className="lp-answer">
      {out.returns?.map((r, i) => (
        <span key={i} title={`${r.type}: ${r.value}`}>
          {r.name && <span className="lp-muted">{r.name} = </span>}
          {named(r.value, accounts)}
        </span>
      ))}
    </span>
  );
}

/** What a transaction did: what it returned, its events, and the storage it changed, under whether it went
 * through and its gas unless `bare`, as where a history row already shows them. */
function Outcome({ tx, accounts, bare }: { tx: Tx; accounts: Account[]; bare?: boolean }) {
  if (!tx.n) return <p className="lp-outcome lp-fail">{tx.error ?? tx.panic}</p>;
  const quiet = !tx.error && !tx.returns?.length && !tx.events?.length && !tx.changes.length;
  return (
    <div className="lp-outcome">
      {!bare && (
        <p>
          <span className={tx.ok ? "lp-ok" : "lp-fail"}>{tx.ok ? "✓" : "✗"}</span> #{tx.n}
          {tx.gas !== undefined && <span className="lp-muted"> · {tx.gas.toLocaleString()} gas</span>}
        </p>
      )}
      {bare && quiet && <p className="lp-muted">No return value, events, or storage changes.</p>}
      {tx.error && <p className="lp-fail">{named(tx.error, accounts)}</p>}
      {tx.returns?.map((r, i) => (
        <p key={i}>
          <span className="lp-muted">returned</span> {r.name && `${r.name} = `}
          {named(r.value, accounts)}
        </p>
      ))}
      {tx.events?.map((e, i) => (
        <p key={i} title={e.text}>
          <span className="lp-muted">emitted</span> {named(e.text, accounts)}
        </p>
      ))}
      {tx.implementation && (
        <p>
          <span className="lp-muted">implementation at {short(tx.implementation.address)} · {tx.implementation.gas.toLocaleString()} gas, behind an ERC-1967 proxy</span>
        </p>
      )}
      {tx.facets?.map((f) => (
        <p key={f.address}>
          <span className="lp-muted">facet</span> {f.name} <span className="lp-muted">at {short(f.address)}</span>{" "}
          {f.there ? <span className="lp-muted">already on the chain</span> : <span className="lp-muted">· {f.gas?.toLocaleString()} gas</span>}
        </p>
      ))}
      {tx.changes.map((c, i) => (
        <p key={i}>
          <span className="lp-muted">set</span> {named(c.label, accounts)}{" "}
          {c.from !== undefined && <s className="lp-muted">{named(c.from, accounts)}</s>} {c.to !== undefined ? named(c.to, accounts) : <span className="lp-muted">cleared</span>}
        </p>
      ))}
    </div>
  );
}

export const RUN_CSS = `
.lp-tabs { display: flex; gap: .25rem; margin-bottom: 1rem; }
.lp .lp-tabs button[aria-selected="true"] { border-color: var(--vocs-color-accent); color: var(--vocs-text-color-heading); }
.lp-run-bar { display: flex; align-items: center; gap: .75rem; flex-wrap: wrap; margin-bottom: .75rem; }
.lp-segmented { display: inline-flex; align-items: center; gap: .25rem; flex-wrap: wrap; }
.lp-segmented > .lp-muted { margin-right: .25rem; }
.lp .lp-segmented button { display: inline-flex; align-items: center; gap: .4rem; padding: .25rem .65rem .25rem .4rem; }
.lp .lp-segmented button[aria-checked="true"] { border-color: var(--vocs-color-accent); background: var(--vocs-background-color-surface); color: var(--vocs-text-color-heading); }
.lp-avatar { border-radius: 4px; flex: none; display: block; }
.lp-chain { margin-left: auto; font-variant-numeric: tabular-nums; }
.lp .lp-quiet { color: var(--vocs-text-color-secondary); }
.lp-segmented + .lp-quiet { margin-left: auto; }
.lp-banner { display: flex; align-items: center; gap: .75rem; flex-wrap: wrap; padding: .625rem .75rem; margin-bottom: .75rem; border: 1px solid var(--vocs-color-yellow); border-radius: .5rem; font-size: .875rem; background: light-dark(rgb(250 204 21 / .1), rgb(250 204 21 / .06)); }
.lp-card { border: 1px solid var(--lp-line); border-radius: .5rem; padding: .75rem .875rem; margin-bottom: .75rem; }
.lp-card-head { display: flex; align-items: center; gap: .5rem; flex-wrap: wrap; margin-bottom: .5rem; }
.lp-card h3 { font-size: 1rem; font-weight: 600; margin: 0; }
.lp-right { margin-left: auto; }
.lp-muted { color: var(--vocs-text-color-muted); font-weight: 400; font-size: .8125rem; }
p.lp-muted { margin: .25rem 0; }
.lp .lp-address { font: .75rem var(--vocs-font-mono); padding: .1rem .4rem; color: var(--vocs-text-color-secondary); }
.lp-subtabs { display: flex; gap: 1rem; border-bottom: 1px solid var(--lp-line); margin: .25rem 0 .5rem; }
.lp .lp-subtabs button { border: 0; border-bottom: 2px solid transparent; border-radius: 0; padding: .35rem 0; margin-bottom: -1px; color: var(--vocs-text-color-secondary); display: inline-flex; align-items: center; gap: .35rem; }
.lp .lp-subtabs button:hover { color: var(--vocs-text-color-heading); }
.lp .lp-subtabs button[aria-selected="true"] { border-bottom-color: var(--vocs-color-accent); color: var(--vocs-text-color-heading); }
.lp-badge, .lp-count { font: 500 .6875rem/1 var(--vocs-font-sans, system-ui); padding: .15rem .4rem; border-radius: 999px; font-variant-numeric: tabular-nums; }
.lp-badge { background: var(--vocs-color-yellow); color: light-dark(#fff, #000); }
.lp-count { background: var(--vocs-background-color-surface); border: 1px solid var(--lp-line); color: var(--vocs-text-color-muted); }
.lp-fn { border-bottom: 1px solid var(--lp-line); }
.lp-fn:last-child { border-bottom: 0; }
.lp-fn-head { display: flex; align-items: baseline; gap: .35rem; padding: .45rem .25rem; min-height: 2.25rem; font-size: .8125rem; }
summary.lp-fn-head { cursor: pointer; list-style: none; }
summary.lp-fn-head::-webkit-details-marker { display: none; }
summary.lp-fn-head::before { content: "›"; color: var(--vocs-text-color-muted); width: .75rem; transition: transform .1s; display: inline-block; }
div.lp-fn-head::before { content: ""; width: .75rem; }
details[open] > summary.lp-fn-head::before { transform: rotate(90deg); }
summary.lp-fn-head:hover .lp-fn-name { color: var(--vocs-color-accent); }
.lp .lp-fn-name, .lp .lp-fn-sig, .lp .lp-tx code { padding: 0; border: 0; background: none; font-family: var(--vocs-font-mono); font-size: .8125rem; }
.lp-fn-name { font-weight: 600; color: var(--vocs-text-color-heading); }
.lp-fn-name { flex: none; }
.lp-fn-sig { color: var(--vocs-text-color-secondary); overflow-wrap: anywhere; flex: 0 1 auto; min-width: 0; }
.lp-tag { font-size: .6875rem; padding: .05rem .35rem; border-radius: .25rem; border: 1px solid var(--lp-line); color: var(--vocs-text-color-muted); }
.lp-fn-summary { margin-left: auto; padding-left: .5rem; display: inline-flex; align-items: center; flex: 0 1 auto; min-width: 0; max-width: 55%; justify-content: flex-end; }
.lp-fn-summary:empty { display: none; }
.lp .lp-small { padding: .15rem .7rem; font-size: .8125rem; }
.lp-fn-body { padding: 0 .25rem .5rem 1.1rem; }
.lp-form { display: grid; grid-template-columns: minmax(5rem, max-content) max-content 1fr; gap: .375rem .75rem; align-items: center; padding: .25rem 0; }
.lp-field { display: contents; }
.lp-field-name { font: .8125rem var(--vocs-font-mono); color: var(--vocs-text-color-heading); }
.lp-field-type { font: .75rem var(--vocs-font-mono); color: var(--vocs-text-color-muted); }
.lp .lp-field input { font: .8125rem var(--vocs-font-mono); width: 100%; min-width: 0; }
.lp-form-actions { grid-column: 1 / -1; display: flex; }
.lp-form:has(> .lp-field) > .lp-form-actions { justify-content: flex-end; }
.lp-form > .lp-outcome { grid-column: 1 / -1; }
.lp-fn > .lp-outcome { margin: 0 .25rem .5rem 1.1rem; }
.lp-values { display: grid; grid-template-columns: max-content 1fr max-content; gap: .1rem 1.25rem; margin: 0 0 .5rem; padding: .25rem .25rem .5rem 1.1rem; border-bottom: 1px solid var(--lp-line); font: .8125rem/1.7 var(--vocs-font-mono); }
.lp-values > div { display: contents; }
.lp-values dt { color: var(--vocs-text-color-secondary); }
.lp-values dd { margin: 0; overflow-wrap: anywhere; min-width: 0; }
.lp-gas { font-size: .75rem; white-space: nowrap; text-align: right; }
.lp-values dd.lp-gas { color: var(--vocs-text-color-muted); }
.lp-answer { font: .8125rem var(--vocs-font-mono); display: inline-flex; gap: .75rem; flex-wrap: wrap; overflow-wrap: anywhere; }
.lp-asked { font: .8125rem var(--vocs-font-mono); overflow-wrap: anywhere; text-align: right; }
.lp-outcome { font: .8125rem/1.55 var(--vocs-font-mono); margin: .25rem 0; overflow-wrap: anywhere; }
.lp-outcome p { margin: 0; }
.lp-outcome s { margin-right: .25rem; }
.lp-ok { color: var(--vocs-color-green, #16a34a); }
.lp-fail { color: var(--vocs-color-red); font: .8125rem var(--vocs-font-mono); overflow-wrap: anywhere; }
.lp-state { font: .8125rem/1.6 var(--vocs-font-mono); }
.lp-domain + .lp-domain { margin-top: .5rem; }
.lp-domain-name { font-size: .75rem; color: var(--vocs-text-color-muted); }
.lp-entry { display: flex; gap: 1rem; padding: .05rem .5rem; border-radius: .25rem; }
.lp-entry-name { color: var(--vocs-text-color-secondary); min-width: 35%; overflow-wrap: anywhere; }
.lp-entry-value { overflow-wrap: anywhere; min-width: 0; }
.lp-entry-value s { color: var(--vocs-text-color-muted); margin-right: .25rem; }
.lp-nested { margin-left: 1rem; border-left: 1px solid var(--lp-line); }
.lp-moved { background: light-dark(rgb(250 204 21 / .2), rgb(250 204 21 / .1)); }
.lp-new { font-size: .6875rem; text-transform: uppercase; letter-spacing: .04em; color: var(--vocs-color-accent); margin-right: .25rem; }
.lp-other + .lp-other { margin-top: .75rem; }
.lp-upgrade { border: 1px solid var(--vocs-color-yellow); border-radius: .5rem; padding: .625rem .75rem; margin: .25rem 0 .75rem; background: light-dark(rgb(250 204 21 / .07), rgb(250 204 21 / .04)); }
.lp-upgrade-head { margin: 0 0 .5rem; font-size: .8125rem; }
.lp-layout { margin-bottom: .5rem; font-size: .8125rem; }
.lp-layout > summary { cursor: pointer; }
.lp-layout pre { font: .75rem/1.5 var(--vocs-font-mono); margin: .375rem 0 0; padding: .5rem; border: 1px solid var(--lp-line); border-radius: .375rem; overflow: auto; }
.lp-upgrade-migration { display: flex; align-items: center; gap: .5rem; margin-bottom: .25rem; }
.lp-tx { border-bottom: 1px solid var(--lp-line); }
.lp-tx:last-child { border-bottom: 0; }
.lp-tx > summary { display: flex; align-items: center; gap: .5rem; padding: .4rem .25rem; cursor: pointer; font-size: .8125rem; list-style: none; }
.lp-tx > summary::-webkit-details-marker { display: none; }
.lp-tx > summary code { overflow-wrap: anywhere; }
.lp-tx > .lp-outcome { margin: 0 .25rem .5rem 1.6rem; }
.lp-run[aria-busy="true"] { cursor: progress; }
@media (max-width: 800px) {
  .lp-form { grid-template-columns: 1fr; gap: .125rem; }
  .lp-field-type { margin-bottom: .125rem; }
}
`;
