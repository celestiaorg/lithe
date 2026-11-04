import { readFile } from "node:fs/promises";
import path from "node:path";

import { FACETS_FILE } from "./build.js";

// A contract with delegated modules is a router whose creation code checks that its facets
// exist where `lithe` pinned them: the deterministic CREATE2 deployer's addresses. A simulated
// network starts with every built facet's code there, so the contract deploys by name.
export default async () => ({
  async newConnection(context, next) {
    const connection = await next(context);
    if (connection.networkConfig.type !== "edr-simulated") return connection;
    const file = path.join(await context.solidity.getArtifactsDirectory("contracts"), FACETS_FILE);
    let facets;
    try {
      facets = JSON.parse(await readFile(file, "utf8"));
    } catch (error) {
      if (error.code === "ENOENT") return connection;
      throw error;
    }
    for (const [address, code] of Object.entries(facets)) {
      await connection.provider.request({ method: "hardhat_setCode", params: [address, code] });
    }
    return connection;
  },
});
