// deno-fmt-ignore-file
// biome-ignore format: generated types do not need formatting
// prettier-ignore
import type { PathsForPages } from 'waku/router'

// prettier-ignore
type Page =
  | { path: '/by-example/abi'; render: 'static' }
  | { path: '/by-example/calling-contracts'; render: 'static' }
  | { path: '/by-example/constants'; render: 'static' }
  | { path: '/by-example/continuations'; render: 'static' }
  | { path: '/by-example/counter'; render: 'static' }
  | { path: '/by-example/crowdfund'; render: 'static' }
  | { path: '/by-example/dispatch'; render: 'static' }
  | { path: '/by-example/dutch-auction'; render: 'static' }
  | { path: '/by-example/english-auction'; render: 'static' }
  | { path: '/by-example/erc20'; render: 'static' }
  | { path: '/by-example/erc721'; render: 'static' }
  | { path: '/by-example/errors'; render: 'static' }
  | { path: '/by-example/escrow'; render: 'static' }
  | { path: '/by-example/ether-wallet'; render: 'static' }
  | { path: '/by-example/events'; render: 'static' }
  | { path: '/by-example/functions'; render: 'static' }
  | { path: '/by-example/generics'; render: 'static' }
  | { path: '/by-example/guards'; render: 'static' }
  | { path: '/by-example/hashing'; render: 'static' }
  | { path: '/by-example/hello-world'; render: 'static' }
  | { path: '/by-example/if-else'; render: 'static' }
  | { path: '/by-example/imports'; render: 'static' }
  | { path: '/by-example'; render: 'static' }
  | { path: '/by-example/initialization'; render: 'static' }
  | { path: '/by-example/interfaces'; render: 'static' }
  | { path: '/by-example/iterable-set'; render: 'static' }
  | { path: '/by-example/lists'; render: 'static' }
  | { path: '/by-example/loops'; render: 'static' }
  | { path: '/by-example/maps'; render: 'static' }
  | { path: '/by-example/modules'; render: 'static' }
  | { path: '/by-example/multisig'; render: 'static' }
  | { path: '/by-example/named-storage'; render: 'static' }
  | { path: '/by-example/nominal-types'; render: 'static' }
  | { path: '/by-example/options'; render: 'static' }
  | { path: '/by-example/order-executor'; render: 'static' }
  | { path: '/by-example/payable'; render: 'static' }
  | { path: '/by-example/primitive-types'; render: 'static' }
  | { path: '/by-example/records'; render: 'static' }
  | { path: '/by-example/reentrancy'; render: 'static' }
  | { path: '/by-example/sending-ether'; render: 'static' }
  | { path: '/by-example/signatures'; render: 'static' }
  | { path: '/by-example/state'; render: 'static' }
  | { path: '/by-example/time-lock'; render: 'static' }
  | { path: '/by-example/transient-storage'; render: 'static' }
  | { path: '/by-example/try-catch'; render: 'static' }
  | { path: '/by-example/tuples'; render: 'static' }
  | { path: '/by-example/units'; render: 'static' }
  | { path: '/by-example/upgradeable'; render: 'static' }
  | { path: '/by-example/variables'; render: 'static' }
  | { path: '/by-example/variants'; render: 'static' }
  | { path: '/by-example/vesting'; render: 'static' }
  | { path: '/by-example/view-and-pure'; render: 'static' }
  | { path: '/by-example/visibility'; render: 'static' }
  | { path: '/guide/coming-from-solidity'; render: 'static' }
  | { path: '/guide/getting-started'; render: 'static' }
  | { path: '/guide/introduction'; render: 'static' }
  | { path: '/guide/performance'; render: 'static' }
  | { path: '/guide/transition-model'; render: 'static' }
  | { path: '/guide/why-not-solidity'; render: 'static' }
  | { path: '/guide/why-now'; render: 'static' }
  | { path: '/'; render: 'static' }
  | { path: '/language/builtins'; render: 'static' }
  | { path: '/language/continuations'; render: 'static' }
  | { path: '/language/deploy'; render: 'static' }
  | { path: '/language/dispatch'; render: 'static' }
  | { path: '/language/effects'; render: 'static' }
  | { path: '/language/errors'; render: 'static' }
  | { path: '/language/events'; render: 'static' }
  | { path: '/language/expressions'; render: 'static' }
  | { path: '/language/functions'; render: 'static' }
  | { path: '/language/generics'; render: 'static' }
  | { path: '/language/imports'; render: 'static' }
  | { path: '/language/literals'; render: 'static' }
  | { path: '/language/modules'; render: 'static' }
  | { path: '/language/reentrancy'; render: 'static' }
  | { path: '/language/statements'; render: 'static' }
  | { path: '/language/storage'; render: 'static' }
  | { path: '/language/structure'; render: 'static' }
  | { path: '/language/types'; render: 'static' }
  | { path: '/language/upgrades'; render: 'static' }
  | { path: '/stdlib/access'; render: 'static' }
  | { path: '/stdlib/collections'; render: 'static' }
  | { path: '/stdlib/crypto'; render: 'static' }
  | { path: '/stdlib'; render: 'static' }
  | { path: '/stdlib/interfaces'; render: 'static' }
  | { path: '/stdlib/math'; render: 'static' }
  | { path: '/stdlib/tokens'; render: 'static' }
  | { path: '/stdlib/utils'; render: 'static' }
  | { path: '/tooling/cli'; render: 'static' }
  | { path: '/tooling/inspection'; render: 'static' }
  | { path: '/tooling/size-limit'; render: 'static' }

// prettier-ignore
declare module 'waku/router' {
  interface RouteConfig {
    paths: PathsForPages<Page>
  }
  interface CreatePagesConfig {
    pages: Page
  }
}
