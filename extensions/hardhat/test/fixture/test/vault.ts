import assert from "node:assert/strict";
import { describe, it } from "node:test";
import hre, { network } from "hardhat";
import { createWalletClient, custom, parseEther } from "viem";
import { generatePrivateKey, privateKeyToAccount } from "viem/accounts";

describe("Vault", async () => {
  const { viem } = await network.create();
  const publicClient = await viem.getPublicClient();
  const [wallet] = await viem.getWalletClients();

  it("withdraws", async () => {
    const vault = await viem.deployContract("Vault");
    await vault.write.deposit({ value: parseEther("1") });
    await vault.write.withdraw([parseEther("0.4")]);
    assert.equal(await publicClient.getBalance({ address: vault.address }), parseEther("0.6"));
  });

  it("refuses an overdraw", async () => {
    const vault = await viem.deployContract("Vault");
    await vault.write.deposit({ value: parseEther("1") });
    await viem.assertions.revertWithCustomError(vault.write.withdraw([parseEther("2")]), vault, "Insufficient");
  });

  it("passes deploy arguments", async () => {
    const fees = await viem.deployContract("Fees", [wallet.account.address, 250n]);
    assert.equal((await fees.read.owner()).toLowerCase(), wallet.account.address.toLowerCase());
  });

  it("deploys a contract with a delegated module", async () => {
    const counter = await viem.deployContract("Tally");
    await counter.write.bump([3n]);
    assert.equal(await counter.read.count(), 3n);
    const { facets, plan } = await hre.artifacts.readArtifact("Tally");
    assert.equal(facets[0].name, "Counter");
    assert.equal(plan.facets[0].address, facets[0].address);
  });

  it("deploys a contract's facets through the CREATE2 deployer", async () => {
    const { lithe, provider } = await network.create();
    const { plan } = await hre.artifacts.readArtifact("Tally");
    const setCode = (address: string, code: string) =>
      provider.request({ method: "hardhat_setCode", params: [address, code] });
    await setCode(plan.facets[0].address, "0x");
    const counter = await lithe.deploy("Tally");
    await counter.write.bump([3n]);
    assert.equal(await counter.read.count(), 3n);
    await setCode(plan.facets[0].address, "0x");
    await setCode(plan.facets[0].to, "0x");
    await assert.rejects(lithe.deploy("Tally"), /no code there/);
  });

  it("deploys facets from a wallet client's local account", async () => {
    const { lithe, provider } = await network.create();
    const { plan } = await hre.artifacts.readArtifact("Tally");
    await provider.request({ method: "hardhat_setCode", params: [plan.facets[0].address, "0x"] });
    const account = privateKeyToAccount(generatePrivateKey());
    await provider.request({ method: "hardhat_setBalance", params: [account.address, "0xde0b6b3a7640000"] });
    const local = createWalletClient({ account, chain: publicClient.chain, transport: custom(provider) });
    const counter = await lithe.deploy("Tally", [], { client: { wallet: local } });
    await counter.write.bump([3n]);
    assert.equal(await counter.read.count(), 3n);
  });
});
