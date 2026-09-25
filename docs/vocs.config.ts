import { defineConfig } from "vocs/config";
import lithe from "../extensions/lithe.tmLanguage.json" with { type: "json" };

const guide = [
  {
    text: "Getting started",
    items: [
      { text: "Introduction", link: "/guide/introduction" },
      { text: "Why now", link: "/guide/why-now" },
      { text: "Why not Solidity?", link: "/guide/why-not-solidity" },
      { text: "Installation and first contract", link: "/guide/getting-started" },
      { text: "The transition model", link: "/guide/transition-model" },
      { text: "Coming from Solidity", link: "/guide/coming-from-solidity" },
      { text: "Bytecode size and gas", link: "/guide/performance" },
    ],
  },
  {
    text: "Language",
    items: [
      { text: "Program structure", link: "/language/structure" },
      { text: "Types", link: "/language/types" },
      { text: "Literals and units", link: "/language/literals" },
      { text: "Expressions and operators", link: "/language/expressions" },
      { text: "Statements", link: "/language/statements" },
      { text: "Functions", link: "/language/functions" },
      { text: "Deployment", link: "/language/deploy" },
      { text: "Storage", link: "/language/storage" },
      { text: "Errors", link: "/language/errors" },
      { text: "Events", link: "/language/events" },
      { text: "Queries and deferred calls", link: "/language/effects" },
      { text: "Continuations", link: "/language/continuations" },
      { text: "Reentrancy", link: "/language/reentrancy" },
      { text: "Entrypoint dispatch", link: "/language/dispatch" },
      { text: "Modules and contracts", link: "/language/modules" },
      { text: "Imports", link: "/language/imports" },
      { text: "Generics", link: "/language/generics" },
      { text: "Upgrades and migrations", link: "/language/upgrades" },
      { text: "Built-ins", link: "/language/builtins" },
    ],
  },
  {
    text: "Standard library",
    items: [
      { text: "Overview", link: "/stdlib" },
      { text: "Access control", link: "/stdlib/access" },
      { text: "Tokens", link: "/stdlib/tokens" },
      { text: "Collections", link: "/stdlib/collections" },
      { text: "Math", link: "/stdlib/math" },
      { text: "Cryptography", link: "/stdlib/crypto" },
      { text: "Utilities", link: "/stdlib/utils" },
      { text: "Interfaces", link: "/stdlib/interfaces" },
    ],
  },
  {
    text: "Tooling",
    items: [
      { text: "Command line", link: "/tooling/cli" },
      { text: "Inspecting contracts", link: "/tooling/inspection" },
      { text: "Contract size limit", link: "/tooling/size-limit" },
    ],
  },
];

const byExample = [
  { text: "Overview", link: "/by-example" },
  {
    text: "Basics",
    items: [
      { text: "Hello world", link: "/by-example/hello-world" },
      { text: "Counter", link: "/by-example/counter" },
      { text: "Primitive types", link: "/by-example/primitive-types" },
      { text: "Variables", link: "/by-example/variables" },
      { text: "Constants", link: "/by-example/constants" },
      { text: "Reading and writing state", link: "/by-example/state" },
      { text: "Ether and time units", link: "/by-example/units" },
      { text: "If / else", link: "/by-example/if-else" },
      { text: "Loops", link: "/by-example/loops" },
    ],
  },
  {
    text: "Data",
    items: [
      { text: "Maps", link: "/by-example/maps" },
      { text: "Lists", link: "/by-example/lists" },
      { text: "Variants", link: "/by-example/variants" },
      { text: "Records", link: "/by-example/records" },
      { text: "Tuples", link: "/by-example/tuples" },
      { text: "Options", link: "/by-example/options" },
      { text: "Nominal types", link: "/by-example/nominal-types" },
    ],
  },
  {
    text: "Functions",
    items: [
      { text: "Functions", link: "/by-example/functions" },
      { text: "View and pure", link: "/by-example/view-and-pure" },
      { text: "Visibility", link: "/by-example/visibility" },
      { text: "Errors", link: "/by-example/errors" },
      { text: "Guards", link: "/by-example/guards" },
      { text: "Events", link: "/by-example/events" },
      { text: "Initialization", link: "/by-example/initialization" },
    ],
  },
  {
    text: "Ether and calls",
    items: [
      { text: "Payable", link: "/by-example/payable" },
      { text: "Sending ether", link: "/by-example/sending-ether" },
      { text: "Interfaces and queries", link: "/by-example/interfaces" },
      { text: "Calling other contracts", link: "/by-example/calling-contracts" },
      { text: "Using call results", link: "/by-example/continuations" },
      { text: "Recovering from failed calls", link: "/by-example/try-catch" },
      { text: "Reentrancy", link: "/by-example/reentrancy" },
    ],
  },
  {
    text: "Contracts and modules",
    items: [
      { text: "Modules", link: "/by-example/modules" },
      { text: "Imports", link: "/by-example/imports" },
      { text: "Generic modules", link: "/by-example/generics" },
      { text: "Named storage", link: "/by-example/named-storage" },
      { text: "Transient storage", link: "/by-example/transient-storage" },
      { text: "Dispatch", link: "/by-example/dispatch" },
      { text: "Upgradeable contract", link: "/by-example/upgradeable" },
    ],
  },
  {
    text: "Encoding and crypto",
    items: [
      { text: "ABI encode and decode", link: "/by-example/abi" },
      { text: "Hashing", link: "/by-example/hashing" },
      { text: "Verifying signatures", link: "/by-example/signatures" },
    ],
  },
  {
    text: "Applications",
    items: [
      { text: "Ether wallet", link: "/by-example/ether-wallet" },
      { text: "ERC-20 token", link: "/by-example/erc20" },
      { text: "ERC-721 NFT", link: "/by-example/erc721" },
      { text: "Multi-sig wallet", link: "/by-example/multisig" },
      { text: "Iterable set", link: "/by-example/iterable-set" },
      { text: "Escrow", link: "/by-example/escrow" },
      { text: "Crowdfund", link: "/by-example/crowdfund" },
      { text: "English auction", link: "/by-example/english-auction" },
      { text: "Dutch auction", link: "/by-example/dutch-auction" },
      { text: "Time lock", link: "/by-example/time-lock" },
      { text: "Vesting", link: "/by-example/vesting" },
      { text: "Order executor", link: "/by-example/order-executor" },
    ],
  },
];

export default defineConfig({
  title: "Lithe",
  description: "A secure-by-construction smart-contract language for the EVM.",
  renderStrategy: "full-static",
  logoUrl: { light: "/logo-light.png", dark: "/logo-dark.png" },
  iconUrl: "/icon.png",
  accentColor: "light-dark(#065F46, #0DF9B3)",
  codeHighlight: {
    langs: ["bash", "json", "solidity", "text", "plaintext", lithe as never],
  },
  topNav: [
    { text: "Guide", link: "/guide/introduction", match: (path) => /^\/(guide|language|tooling|stdlib)(\/|$)/.test(path ?? "") },
    { text: "Lithe by Example", link: "/by-example", match: "/by-example" },
    { text: "Built-ins", link: "/language/builtins" },
  ],
  sidebar: {
    "/guide": guide,
    "/language": guide,
    "/tooling": guide,
    "/stdlib": guide,
    "/by-example": byExample,
  },
});
