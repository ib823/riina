// Copyright (c) 2026 The RIINA Authors. All rights reserved.
// RIINA Playground Web Worker
// Loads riina_wasm.wasm and exposes compile functions via postMessage.

let wasmInstance = null;
let wasmMemory = null;

async function initWasm() {
  if (wasmInstance) return;
  try {
    // Derive base path from worker URL (handles /riina/ on GitHub Pages)
    const base = self.location.href.replace(/\/assets\/.*$/, '/');
    const response = await fetch(base + 'riina_wasm.wasm');
    const bytes = await response.arrayBuffer();
    const { instance } = await WebAssembly.instantiate(bytes, {
      env: { memory: new WebAssembly.Memory({ initial: 256 }) }
    });
    wasmInstance = instance;
    wasmMemory = instance.exports.memory;
    postMessage({ type: 'ready' });
  } catch (err) {
    postMessage({ type: 'error', error: 'Failed to load WASM: ' + err.message });
  }
}

function writeString(str) {
  const encoder = new TextEncoder();
  const encoded = encoder.encode(str);
  const ptr = wasmInstance.exports.riina_alloc(encoded.length);
  const mem = new Uint8Array(wasmMemory.buffer);
  mem.set(encoded, ptr);
  return { ptr, len: encoded.length };
}

function readResult(ptr) {
  if (ptr === 0) return '{"ok":false,"error":"null pointer"}';
  const mem = new Uint8Array(wasmMemory.buffer);
  const len = mem[ptr] | (mem[ptr + 1] << 8) | (mem[ptr + 2] << 16) | (mem[ptr + 3] << 24);
  const bytes = mem.slice(ptr + 4, ptr + 4 + len);
  const decoder = new TextDecoder();
  const result = decoder.decode(bytes);
  wasmInstance.exports.riina_free(ptr, len + 4);
  return result;
}

function callExport(exportName, source) {
  const { ptr, len } = writeString(source);
  const resultPtr = wasmInstance.exports[exportName](ptr, len);
  wasmInstance.exports.riina_free(ptr, len);
  return readResult(resultPtr);
}

onmessage = async function(e) {
  const { type, source, id } = e.data;

  if (type === 'init') {
    await initWasm();
    return;
  }

  if (!wasmInstance) {
    postMessage({ id, type: 'result', error: 'WASM not loaded' });
    return;
  }

  try {
    let exportName;
    switch (type) {
      case 'check': exportName = 'riina_check'; break;
      case 'emitC': exportName = 'riina_emit_c'; break;
      case 'emitIR': exportName = 'riina_emit_ir'; break;
      default:
        postMessage({ id, type: 'result', error: 'Unknown command: ' + type });
        return;
    }

    const raw = callExport(exportName, source);
    const result = JSON.parse(raw);
    postMessage({ id, type: 'result', result });
  } catch (err) {
    postMessage({ id, type: 'result', error: err.message });
  }
};

// Auto-init on load
initWasm();
