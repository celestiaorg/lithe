import { defineConfig } from "hardhat/config";
import hardhatToolboxViem from "@nomicfoundation/hardhat-toolbox-viem";
import hardhatLithe from "../../index.js";

export default defineConfig({
  plugins: [hardhatToolboxViem, hardhatLithe],
  solidity: "0.8.30",
  lithe: { path: process.env.LITHE ?? "lithe" },
});
