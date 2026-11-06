import { readFile } from "node:fs/promises";
import path from "node:path";
import { setTimeout as sleep } from "node:timers/promises";

import { HardhatPluginError } from "hardhat/plugins";

import { FACETS_FILE } from "./build.js";

// The deterministic deployment proxy, `lithe`'s default CREATE2 deployer, which most chains
// have but Hardhat's simulated one lacks.
const DEPLOYER = "0x4e59b44847b379578588920cA78FbF26c0B4956C";
const DEPLOYER_CODE =
  "0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03601600081602082378035828234f58015156039578182fd5b8082525050506014600cf3";

// A contract with delegated modules is a router whose creation code checks that its facets
// exist where `lithe` pinned them: the CREATE2 deployer's addresses. A simulated network
// starts with the default deployer and every built facet's code there, so the contract deploys
// by name; on any other network, `lithe.deployFacets` sends what the contract's plan lists.
export default async () => ({
  async newConnection(context, next) {
    const connection = await next(context);
    connection.lithe = helpers(connection, context.artifacts);
    if (connection.networkConfig.type !== "edr-simulated") return connection;
    const { provider } = connection;
    if ((await provider.request({ method: "eth_getCode", params: [DEPLOYER, "latest"] })) === "0x") {
      await provider.request({ method: "hardhat_setCode", params: [DEPLOYER, DEPLOYER_CODE] });
    }
    const file = path.join(await context.solidity.getArtifactsDirectory("contracts"), FACETS_FILE);
    let facets;
    try {
      facets = JSON.parse(await readFile(file, "utf8"));
    } catch (error) {
      if (error.code === "ENOENT") return connection;
      throw error;
    }
    for (const [address, code] of Object.entries(facets)) {
      await provider.request({ method: "hardhat_setCode", params: [address, code] });
    }
    return connection;
  },
});

function helpers(connection, artifacts) {
  const { provider } = connection;
  const request = (method, ...params) => provider.request({ method, params });
  const hasCode = async (address) => (await request("eth_getCode", address, "latest")) !== "0x";

  // Waits as long as viem's `waitForTransactionReceipt` does for the contract after.
  async function receipt(hash) {
    for (const deadline = Date.now() + 180_000; Date.now() < deadline; await sleep(1000)) {
      const mined = await request("eth_getTransactionReceipt", hash);
      if (mined) return mined;
    }
  }

  async function sendFacets(name, send) {
    const { plan } = await artifacts.readArtifact(name);
    for (const facet of plan?.facets ?? []) {
      if (await hasCode(facet.address)) continue;
      if (!(await hasCode(facet.to))) {
        throw new HardhatPluginError(
          "hardhat-lithe",
          `${name} needs the facet ${facet.name}, which deploys through the CREATE2 deployer at ${facet.to}, but ${connection.networkName} has no code there. Deploy it, or set \`create2-deployer\` in lithe.toml to the one this network has.`,
        );
      }
      const hash = await send(facet);
      const mined = await receipt(hash);
      if (!mined) {
        throw new HardhatPluginError(
          "hardhat-lithe",
          `The facet ${facet.name}'s transaction ${hash} wasn't mined within 3 minutes`,
        );
      }
      if (mined.status !== "0x1" || !(await hasCode(facet.address))) {
        throw new HardhatPluginError(
          "hardhat-lithe",
          `Deploying the facet ${facet.name} to ${facet.address} failed, in transaction ${hash}`,
        );
      }
    }
  }

  async function deployFacets(name, { from } = {}) {
    await sendFacets(name, async ({ to, data }) => {
      from ??= (await request("eth_accounts"))[0];
      return request("eth_sendTransaction", { from, to, data });
    });
  }

  return {
    deployFacets,
    async deploy(name, args, config) {
      if (connection.viem === undefined) {
        throw new HardhatPluginError(
          "hardhat-lithe",
          "`lithe.deploy` deploys through hardhat-viem, which isn't loaded. Call `lithe.deployFacets` and then deploy the contract with your library.",
        );
      }
      const wallet = config?.client?.wallet ?? (await connection.viem.getWalletClients())[0];
      // The fee fields hardhat-viem passes for the contract, gasPrice winning as it does there.
      const { gasPrice, maxFeePerGas, maxPriorityFeePerGas } = config ?? {};
      const fees = gasPrice !== undefined ? { gasPrice } : { maxFeePerGas, maxPriorityFeePerGas };
      await sendFacets(name, ({ to, data }) => wallet.sendTransaction({ to, data, ...fees }));
      return connection.viem.deployContract(name, args, config);
    },
  };
}
