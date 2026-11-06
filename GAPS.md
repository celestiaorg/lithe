# Gaps

Open bugs, gaps and doc fixes found by auditing the old PRDs (lithe-prd, lithe-positioning, lithe-builtins, lithe-stdlib, upgrade-prd, upgrade-prd-2, codegen-prd, hooks-prd, split-prd) and ports-ignore/modularium/GAPS.md against main at 0ec5ffdd0 (2026-11-05). Everything else in those files shipped, is documented, or was superseded.

## Codegen

- **Calldata list into storage.** Assigning a calldata list parameter to a storage list decodes it into memory first; the `Stmt::Assign` arm counts it as an "other" use (`src/gen/decode.rs:437-446`). Could copy from calldata in place.
- **Hash whole calldata `bytes`/`string` in place.** `Crypto.keccak256(data)` on a whole parameter copies it to memory (`src/gen/tree.rs:2424-2486`); slices are already hashed in place.

## Upgrades

- **ABI diff in `upgrade-check`.** It compares only storage and facets (`src/lib.rs:1584-1640`). Report selectors added, removed, and changed payability.
- **Renames in `upgrade-check`.** `format_diff` (`src/lib.rs:1825`) calls a same-type, same-position name change incompatible, and a named domain renamed with the same id shows as removed + added. Staying strict is defensible (a swap of two same-type fields looks like two renames), but a lone rename or a same-id domain rename could be a warning, which would also allow retiring a field by renaming it.
- **Variant gaining a case.** Stored types compare by strict equality (`src/lib.rs:1842`), so a stored variant that gains a case probably reports incompatible even when the representation is unchanged. Unverified.
- **Storage layout in artifacts.** Standard JSON output has no storage layout, namespaces or field types (`src/standard_json.rs:232`), so `upgrade-check` always needs the old source.
- **Unreachable-field lint.** Warn when a storage field is no longer read or written (`src/lint.rs`).

## Splitting and modules

- **Pinned facet addresses.** A compiler upgrade can move every facet's address. A lockfile of facet addresses would keep deployed facets reusable; `src/config.rs` pins packages only.
- **Generic modules with externals** are still rejected (`src/check/compose.rs:173`).
- **Interfaces that embed interfaces.** Not supported; std interfaces list methods flat (`std/interfaces/erc721.lithe:51`).

## Lints

- **`txOrigin` for authorization.** The docs warn (`docs/src/pages/language/builtins.mdx:66`) but no lint flags `Evm.txOrigin()` compared against an address.

## Docs

- **Operations as values** (`language/effects.mdx`, `defer` section; a line in `language/types.mdx`). `const p : operation := storage.token.transfer(to, amount); defer p;` works, as does an internal function returning `operation` used as `defer payout(...)`, with `then` after a bound operation (`src/check/funcs.rs:1117`, `src/check/stmt.rs:55-71`). Today `operation` appears only in the return-type table at `language/builtins.mdx:101`.
- **ERC-721 internals** (`stdlib/tokens.mdx:475-511`). Document `mint`, `burn`, `approveAs`, `approveAllAs`, `checkReceived` and `authorizedTransfer` (`std/token/erc721.lithe:130-228`) in a table like ERC20/ERC1155/ERC6909, and add a burn recipe: `ERC721.burn` passes zero as `auth`, so it checks no permission (`erc721.lithe:231`).
- **Removal in the upgrade table** (`language/upgrades.mdx:211-215`). Add "remove a field or domain → incompatible" (`src/lib.rs:1849`, `:1865`).
- **Facet addresses** (`tooling/size-limit.mdx:194`). It says a facet moves only when its module or a module it requires changes; a compiler codegen change moves it too.
- **Diamonds** (`guide/coming-from-solidity.mdx`). No page mentions ERC-2535. Map diamond facets to `use M delegated`, and say Lithe can't add a module to a diamond someone else deployed.
- **Stale variant line** (`language/dispatch.mdx:151`). Says variant values "cannot yet be constructed, stored, or returned", contradicting `language/types.mdx:457`, `:521`.
- **Selector collisions** (`guide/why-not-solidity.mdx`). Add a row to the convention → rule table: the compiler rejects colliding selectors, including the proxy's `proxiableUUID` and `upgradeToAndCall` (`src/evm/examples.rs:204`). Today only `language/dispatch.mdx:150` says it.

## Maybe

- **Deque.** No module; `Queue` has `front`, `back`, `push`, `pop` only (`std/collections/queue.lithe:35-53`). The stdlib PRD made it conditional on demand.
- **Release policy.** The stdlib PRD asked each release to note audits, semver, storage-layout and upgrade-compatibility changes, gas figures and effect metadata. Nothing says this today.
