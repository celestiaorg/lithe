// Runs the compiler off the page's thread, and the chain contracts run on in an instance of
// its own, so the chain keeps its state when the compiler crashes. A panic traps, and leaves
// the instance unusable, so the next request gets a fresh one.
const module = WebAssembly.compileStreaming(fetch("lithe.wasm"));
const instances = {};

function write(x, buffer, text) {
  const bytes = new TextEncoder().encode(text);
  const at = x[buffer](bytes.length);
  new Uint8Array(x.memory.buffer, at, bytes.length).set(bytes);
}

onmessage = async ({ data: { id, cmd, source, options } }) => {
  const role = cmd === "session" ? "chain" : "compiler";
  instances[role] ??= await WebAssembly.instantiate(await module);
  const x = instances[role].exports;
  write(x, "options", options ?? "");
  write(x, "input", source);
  let trapped = false;
  try {
    x[cmd]();
  } catch {
    trapped = true;
  }
  const text = new TextDecoder().decode(new Uint8Array(x.memory.buffer, x.output(), x.output_len()));
  if (trapped) delete instances[role];
  let result;
  try {
    result = JSON.parse(text);
  } catch {
    result = { panic: "the compiler ran out of stack or memory" };
  }
  if (trapped && role === "chain") result.reset = true;
  postMessage({ id, result });
};
