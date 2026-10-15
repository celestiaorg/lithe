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

declare const plugin: HardhatPlugin;
export default plugin;
