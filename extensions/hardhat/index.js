import { overrideTask } from "hardhat/config";

export default {
  id: "hardhat-lithe",
  npmPackage: "@lithe-lang/hardhat",
  hookHandlers: {
    config: () => import("./config.js"),
    network: () => import("./network.js"),
  },
  tasks: [
    overrideTask("build")
      .setAction(() => import("./build.js"))
      .build(),
  ],
};
