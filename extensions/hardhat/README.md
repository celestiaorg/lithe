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
