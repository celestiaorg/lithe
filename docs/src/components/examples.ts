/** The programs the playground offers: ones worth running, from pages of these docs, whose check
 * keeps every program on them compiling. A pick is a named file on its page, `file` or a page of Lithe
 * by Example's own, with the files it imports; or the first unnamed program on its page that contains
 * `find`. A page loads only when picked. */
type Pick = { page: string; title: string; find?: string; file?: string };

export const PICKS: [string, Pick[]][] = [
  [
    "Start here",
    [
      { page: "by-example/hello-world", title: "Hello world" },
      { page: "by-example/counter", title: "Counter" },
      { page: "by-example/state", title: "Reading and writing state" },
      { page: "by-example/errors", title: "Errors" },
      { page: "by-example/events", title: "Events" },
    ],
  ],
  [
    "Apps",
    [
      { page: "by-example/erc20", title: "ERC-20 token" },
      { page: "by-example/erc721", title: "ERC-721 NFT" },
      { page: "by-example/crowdfund", title: "Crowdfund" },
      { page: "by-example/dutch-auction", title: "Dutch auction" },
      { page: "by-example/english-auction", title: "English auction" },
      { page: "by-example/escrow", title: "Escrow" },
      { page: "by-example/ether-wallet", title: "Ether wallet" },
      { page: "by-example/multisig", title: "Multi-sig wallet" },
      { page: "by-example/time-lock", title: "Time lock" },
      { page: "by-example/vesting", title: "Vesting" },
      { page: "by-example/hashing", title: "Commit-reveal game" },
    ],
  ],
  [
    "Language",
    [
      { page: "by-example/maps", title: "Maps" },
      { page: "by-example/lists", title: "Lists" },
      { page: "by-example/records", title: "Records" },
      { page: "by-example/variants", title: "Variants" },
      { page: "by-example/options", title: "Options" },
      { page: "by-example/iterable-set", title: "Iterable set" },
      { page: "by-example/guards", title: "Guards" },
      { page: "by-example/payable", title: "Payable" },
      { page: "by-example/generics", title: "Generic modules" },
    ],
  ],
  [
    "Standard library",
    [
      { page: "stdlib/tokens", find: "contract Token is", title: "Pausable ERC-20" },
      { page: "stdlib/tokens", find: "contract Collection is", title: "ERC-721 collection" },
      { page: "stdlib/access", find: "contract Minter is", title: "Roles" },
    ],
  ],
  [
    "Contracts",
    [
      { page: "by-example/modules", title: "Modules" },
      { page: "by-example/imports", title: "Imports" },
      { page: "by-example/upgradeable", title: "Upgradeable contract" },
      { page: "tooling/size-limit", file: "bank.lithe", title: "Bank with a facet" },
      { page: "tooling/size-limit", file: "shop.lithe", title: "Shop with a facet" },
      { page: "language/modules", file: "app.lithe", title: "App with two facets" },
    ],
  ],
];

const PAGES = import.meta.glob(
  [
    "../pages/by-example/*.mdx",
    "../pages/stdlib/*.mdx",
    "../pages/tooling/size-limit.mdx",
    "../pages/language/modules.mdx",
  ],
  {
    query: "?raw",
    import: "default",
  },
) as Record<string, () => Promise<string>>;

export const key = (pick: Pick) => `${pick.page}#${pick.file ?? pick.find ?? ""}`;

async function page(pick: Pick) {
  const load = PAGES[`../pages/${pick.page}.mdx`];
  if (!load) throw new Error(`no page ${pick.page}`);
  return load();
}

/** Files by path, in order, and the one to compile. */
export type Project = { files: [string, string][]; entry: string };

/** `import "./rel"` in `from`, as the path of the file it reads. */
function resolve(from: string, rel: string) {
  const parts = from.split("/").slice(0, -1);
  for (const part of `${rel}.lithe`.split("/")) {
    if (part === "..") parts.pop();
    else if (part !== ".") parts.push(part);
  }
  return parts.join("/");
}

/** A pick's program: its `file` on its page, or on a page of Lithe by Example `[name.lithe]` for page
 * `name`, with the files it imports from the page; or the unnamed program on a page that contains `find`. */
export async function project(pick: Pick): Promise<Project> {
  const blocks = [...(await page(pick)).matchAll(/```lithe([^\n]*)\n([\s\S]*?)```/g)]
    .filter(([, info]) => !/fragment|rejects/.test(info))
    .map(([, info, body]) => ({ name: info.match(/\[([^\]]+)\]/)?.[1], body }));
  if (pick.find) {
    const found = blocks.find((b) => b.body.includes(pick.find!));
    if (!found) throw new Error(`no program on ${pick.page}`);
    return { files: [["main.lithe", found.body]], entry: "main.lithe" };
  }
  const named = new Map(blocks.flatMap((b) => (b.name ? [[b.name, b.body] as const] : [])));
  const slug = pick.page.split("/").at(-1);
  const entry =
    pick.file ?? (named.has(`${slug}.lithe`) ? `${slug}.lithe` : [...named.keys()].find((n) => !n.includes("/")));
  if (entry && !named.has(entry)) throw new Error(`no ${entry} on ${pick.page}`);
  if (!entry) throw new Error(`no program on ${pick.page}`);
  const files: [string, string][] = [];
  const add = (path: string) => {
    if (files.some(([p]) => p === path) || !named.has(path)) return;
    files.push([path, named.get(path)!]);
    for (const [, rel] of named.get(path)!.matchAll(/import\s+"(\.\.?\/[^"]+)"/g)) add(resolve(path, rel));
  };
  add(entry);
  return { files, entry };
}

export const all = PICKS.flatMap(([, picks]) => picks);
