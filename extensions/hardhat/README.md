# @lithe-lang/hardhat

A [Hardhat 3](https://hardhat.org) plugin that compiles Lithe contracts as part of Hardhat's build. Tests then deploy a Lithe contract by name, as they would a Solidity one, from TypeScript or from Solidity tests.

## Install

The plugin runs the `lithe` compiler, which has to be installed too: on the `PATH`, or at the path the `lithe.path` option gives.

```bash
npm install --save-dev @lithe-lang/hardhat
```

Add it to `hardhat.config.ts`:

```ts
import { defineConfig } from "hardhat/config";
import hardhatToolboxViem from "@nomicfoundation/hardhat-toolbox-viem";
import hardhatLithe from "@lithe-lang/hardhat";

export default defineConfig({
  plugins: [hardhatToolboxViem, hardhatLithe],
  solidity: "0.8.30",
});
```

## Use

Put `.lithe` files in `contracts/`, or anywhere under Hardhat's source paths. Each `hardhat build`, and the build that `hardhat test` starts with, compiles them once the Solidity contracts are built, and writes their artifacts where Hardhat writes its own. A compile error fails the build.

A TypeScript test deploys a contract by its name, `Vault`, or its full name, `contracts/vault.lithe:Vault`, and gets a contract typed from its ABI:

```ts
const vault = await viem.deployContract("Vault");
await vault.write.deposit({ value: parseEther("1") });
```

A Solidity test deploys it with forge-std's `deployCode`:

```solidity
IVault vault = IVault(deployCode("Vault"));
```

A contract's `deploy` arguments go where a constructor's would: `viem.deployContract("Fees", [owner, 250n])`, or `deployCode("Fees", abi.encode(owner, 250))`.

A contract with `delegated` modules routes to facets at the addresses `lithe` pins for them. Each connection to a simulated network starts with every built facet's code at its address, and the default CREATE2 deployer, so these contracts deploy by name in tests too. Such a contract's artifact keeps the compiler's `facets` field, each facet's module, address, and the selectors the router forwards to it, and its `plan`, the facets to deploy first, those of contracts it creates included.

## Deploy

On any other network, the facets deploy first, through the CREATE2 deployer. Each network connection has a `lithe` helper that does it:

```ts
import { network } from "hardhat";

const { lithe } = await network.create();
const token = await lithe.deploy("Token", [owner]);
```

`lithe.deploy` deploys each facet the network doesn't have yet, then the contract with hardhat-viem's `deployContract`, and returns the typed contract. `lithe.deployFacets("Token")` deploys only the facets, to deploy the contract after with Ignition or ethers. To use a CREATE2 deployer at another address, set `create2-deployer` in the project's `lithe.toml`.

See [Deploying](https://github.com/celestiaorg/lithe/blob/main/docs/src/pages/tooling/deploying.mdx) and [Hardhat](https://github.com/celestiaorg/lithe/blob/main/docs/src/pages/tooling/hardhat.mdx) in the docs.

## Options

```ts
export default defineConfig({
  plugins: [hardhatLithe],
  lithe: {
    path: "/opt/lithe/bin/lithe",
    checkSpecs: true,
  },
});
```

| Option       | Is                                                                                                                                                                                                                                               |
| ------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `path`       | the compiler to run, `lithe` on the `PATH` unless set                                                                                                                                                                                            |
| `checkSpecs` | `true` to build with `lithe compile --check-specs`, so a call that breaks one of a contract's specs reverts with `SpecViolation(string)`; `false` unless set. A build with the `production` profile, which is what deployments build, ignores it |

## Requirements

Hardhat 3.18 or later. Hardhat's simulated chain runs Osaka, the fork Lithe builds for unless its `lithe.toml` says otherwise.
