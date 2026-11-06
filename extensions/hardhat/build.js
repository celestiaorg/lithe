import { execFile } from "node:child_process";
import { mkdir, mkdtemp, readdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { promisify, styleText } from "node:util";

import { createSpinner } from "@nomicfoundation/hardhat-utils/spinner";
import { HardhatPluginError } from "hardhat/plugins";

const run = promisify(execFile);

// Solidity tests read a compiler version out of every artifact's build info id.
const BUILD_INFO_ID = "solc-0_0_0-lithe-0";

export const FACETS_FILE = "lithe-facets.json";

export default async function build(args, hre, runSuper) {
  const result = await runSuper(args);
  // Runs after the Solidity build, whose full builds delete every artifact it didn't write.
  if (!args.noContracts) {
    const profile = hre.globalOptions.buildProfile ?? args.defaultBuildProfile;
    // Deployments build the production profile, and a checked build must not be deployed.
    await buildLithe(hre, hre.config.lithe.checkSpecs && profile !== "production", args.quiet);
  }
  return result;
}

async function buildLithe(hre, checkSpecs, quiet) {
  const artifactsDir = await hre.solidity.getArtifactsDirectory("contracts");
  const facets = {};
  let built = false;
  for (const root of hre.config.paths.sources.solidity) {
    const sources = await findSources(root);
    if (sources.size === 0) continue;
    const files = `${sources.size} Lithe ${sources.size === 1 ? "file" : "files"}`;
    const tmp = await mkdtemp(path.join(tmpdir(), "hardhat-lithe-"));
    const spinner = createSpinner({ text: `Compiling ${files}...` });
    spinner.start();
    let notes;
    try {
      notes = await compile(hre.config.lithe.path, checkSpecs, root, tmp);
      await convert(hre.config.paths.root, root, sources, path.join(tmp, "out"), artifactsDir, facets);
    } finally {
      spinner.stop();
      if (notes) process.stderr.write(notes);
      await rm(tmp, { recursive: true, force: true });
    }
    if (!quiet) console.log(styleText("bold", `Compiled ${files}`));
    built = true;
  }
  if (built) {
    await writeFile(path.join(artifactsDir, FACETS_FILE), JSON.stringify(facets, null, 2));
    await hre.artifacts.clearCache();
  }
}

// Each `.lithe` file under `root` by its file name, which is the name of its folder in
// `out/`. `lithe compile` rejects two files of one name, and skips hidden ones.
async function findSources(root) {
  const sources = new Map();
  let entries;
  try {
    entries = await readdir(root, { recursive: true, withFileTypes: true });
  } catch (error) {
    if (error.code === "ENOENT") return sources;
    throw error;
  }
  for (const entry of entries) {
    const file = path.join(entry.parentPath, entry.name);
    const hidden = path
      .relative(root, file)
      .split(path.sep)
      .some((part) => part.startsWith("."));
    if (entry.isFile() && !hidden && entry.name.endsWith(".lithe") && !entry.name.endsWith(".spec.lithe")) {
      sources.set(entry.name, file);
    }
  }
  return sources;
}

// `lithe compile dir` writes `out/` under the working directory, so it runs in `cwd`.
// Returns the compiler's warnings and notes.
async function compile(compiler, checkSpecs, root, cwd) {
  const args = ["compile", ...(checkSpecs ? ["--check-specs"] : []), root];
  try {
    return (await run(compiler, args, { cwd, maxBuffer: 64 << 20 })).stderr;
  } catch (error) {
    if (error.code === "ENOENT") {
      throw new HardhatPluginError(
        "hardhat-lithe",
        `Can't run the Lithe compiler \`${compiler}\`. Install it, or set \`lithe.path\` in the Hardhat config.`,
      );
    }
    throw new HardhatPluginError("hardhat-lithe", `Lithe build failed:\n${error.stderr || error.message}`);
  }
}

// `out/<file>.lithe/<Contract>.json` becomes `artifacts/<path of file>.lithe/<Contract>.json`,
// and `out/facets/` becomes `artifacts/<root>/facets/`. The runtime code of every facet a
// contract delegates to goes into `facets`, by the address the contract routes to.
async function convert(projectRoot, root, sources, outDir, artifactsDir, facets) {
  // A root of library files only writes nothing.
  const folders = await readdir(outDir).catch((error) => (error.code === "ENOENT" ? [] : Promise.reject(error)));
  for (const folder of folders) {
    const source = sources.get(folder) ?? path.join(root, folder);
    const sourceName = path.relative(projectRoot, source).split(path.sep).join("/");
    const dest = path.join(artifactsDir, sourceName);
    await rm(dest, { recursive: true, force: true });
    await mkdir(dest, { recursive: true });
    const artifacts = [];
    for (const file of (await readdir(path.join(outDir, folder))).sort()) {
      const lithe = JSON.parse(await readFile(path.join(outDir, folder, file), "utf8"));
      for (const facet of lithe.facets ?? []) {
        facets[facet.address] ??= await facetCode(outDir, facet);
      }
      const artifact = {
        _format: "hh3-artifact-1",
        contractName: lithe.contractName,
        sourceName,
        abi: lithe.abi,
        bytecode: lithe.bytecode.object,
        deployedBytecode: lithe.deployedBytecode.object,
        linkReferences: {},
        deployedLinkReferences: {},
        immutableReferences: {},
        inputSourceName: sourceName,
        buildInfoId: BUILD_INFO_ID,
      };
      artifacts.push(artifact);
      await writeFile(path.join(dest, `${artifact.contractName}.json`), JSON.stringify(artifact, null, 2));
    }
    await writeFile(path.join(dest, "artifacts.d.ts"), declarations(artifacts));
  }
}

// `out/facets/<Module>.json`, or `<Module>-<address prefix>.json` when contracts build the
// module into different facets.
async function facetCode(outDir, facet) {
  const dir = path.join(outDir, "facets");
  const prefix = facet.address.slice(2, 10).toLowerCase();
  for (const file of [`${facet.name}.json`, `${facet.name}-${prefix}.json`]) {
    try {
      return JSON.parse(await readFile(path.join(dir, file), "utf8")).deployedBytecode.object;
    } catch (error) {
      if (error.code !== "ENOENT") throw error;
    }
  }
  throw new HardhatPluginError("hardhat-lithe", `No artifact for the facet ${facet.name} at ${facet.address}`);
}

// The declarations Hardhat writes next to a Solidity file's artifacts, which type
// `readArtifact` and `viem.deployContract` by contract name.
function declarations(artifacts) {
  const types = artifacts.map(
    (artifact) => `export interface ${artifact.contractName}$Type {
  ${Object.entries(artifact)
    .map(([name, value]) => `readonly ${name}: ${JSON.stringify(value)};`)
    .join("\n  ")}
};`,
  );
  return `// This file was autogenerated by @lithe-lang/hardhat, do not edit it.
// prettier-ignore
// tslint:disable
// eslint-disable
// biome-ignore format: see above

${types.join("\n\n")}

import "hardhat/types/artifacts";
declare module "hardhat/types/artifacts" {
  interface ArtifactMap {
    ${artifacts.map((a) => `["${a.contractName}"]: ${a.contractName}$Type`).join("\n    ")};
    ${artifacts.map((a) => `["${a.sourceName}:${a.contractName}"]: ${a.contractName}$Type`).join("\n    ")};
  }
}
`;
}
