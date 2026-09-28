const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

exports.activate = () => {
  const command = vscode.workspace.getConfiguration("lithe").get("path");
  client = new LanguageClient(
    "lithe",
    "Lithe",
    { command, args: ["lsp"] },
    { documentSelector: [{ language: "lithe" }] }
  );
  return client.start();
};

exports.deactivate = () => client?.stop();
