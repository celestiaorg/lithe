import type { HardhatPlugin } from "hardhat/types/plugins";

declare module "hardhat/types/config" {
  interface HardhatUserConfig {
    lithe?: LitheUserConfig;
  }

  interface HardhatConfig {
    lithe: Required<LitheUserConfig>;
  }
}

export interface LitheUserConfig {
  /** The `lithe` executable. Defaults to `lithe` on the `PATH`. */
  path?: string;
  /** Build with `--check-specs`, so a call that breaks a spec reverts. Defaults to `false`. */
  checkSpecs?: boolean;
}

declare module "hardhat/types/network" {
  interface NetworkConnection<ChainTypeT extends ChainType | string = DefaultChainType> {
    lithe: LitheHelpers<NetworkConnection<ChainTypeT>>;
  }
}

export interface LitheHelpers<Connection> {
  /**
   * Deploys each facet the contract's plan lists that the network doesn't have yet, through
   * the CREATE2 deployer, from `from` or the first account.
   */
  deployFacets(contractName: string, options?: { from?: `0x${string}` }): Promise<void>;
  /** Deploys the contract's facets, then the contract with hardhat-viem's `deployContract`. */
  deploy: Connection extends { viem: { deployContract: infer Deploy } } ? Deploy : never;
}

declare const plugin: HardhatPlugin;
export default plugin;
