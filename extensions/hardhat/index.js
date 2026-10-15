import { overrideTask } from "hardhat/config";

export default {
  id: "hardhat-lithe",
  npmPackage: "@lithe-lang/hardhat",
  hookHandlers: {
    config: () => import("./config.js"),
  },
  tasks: [
    overrideTask("build")
      .setAction(() => import("./build.js"))
      .build(),
  ],
};
