import assert from "node:assert/strict";
import { describe, it } from "node:test";
import { network } from "hardhat";
import { parseEther } from "viem";

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
});
