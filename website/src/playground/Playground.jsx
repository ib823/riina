// SPDX-License-Identifier: MPL-2.0
// RIINA Playground — In-Browser Compiler
// Zero external dependencies (no Monaco, no CodeMirror).

import React, { useState, useEffect, useRef, useCallback } from 'react';

// Pre-loaded examples
const EXAMPLES = [
  {
    name: 'Hello Dunia',
    code: `// Hello World in RIINA (Bahasa Melayu)
biar nama = "Dunia";
biar mesej = "Selamat datang, " + nama + "!";
mesej`
  },
  {
    name: 'Arithmetic',
    code: `// Arithmetic with variables
biar x = 5;
biar y = 10;
biar hasil = x + y * 2;
hasil`
  },
  {
    name: 'Functions',
    code: `// Multi-parameter functions (curried)
fungsi tambah(x: Nombor, y: Nombor) -> Nombor {
  x + y
}
fungsi ganda(x: Nombor) -> Nombor {
  x * 2
}
biar h = tambah(3, 4);
ganda h`
  },
  {
    name: 'Conditionals',
    code: `// Conditional expressions (kalau / lain)
biar umur = 20;
kalau umur >= 18 {
  "Dewasa"
} lain {
  "Kanak-kanak"
}`
  },
  {
    name: 'Builtins',
    code: `// Built-in functions (bilingual)
biar nama = "RIINA";
biar p = panjang(nama);
biar mesej = ke_teks(p) + " aksara";
mesej`
  }
];

const PlaygroundPage = ({ onNavigate }) => {
  const [source, setSource] = useState(EXAMPLES[0].code);
  const [activeTab, setActiveTab] = useState('Type Check');
  const [diagnostics, setDiagnostics] = useState('');
  const [cOutput, setCOutput] = useState('');
  const [irOutput, setIrOutput] = useState('');
  const [wasmReady, setWasmReady] = useState(false);
  const [wasmError, setWasmError] = useState(null);
  const workerRef = useRef(null);
  const debounceRef = useRef(null);
  const reqIdRef = useRef(0);

  // Initialize Web Worker
  useEffect(() => {
    try {
      const worker = new Worker(new URL('./worker.js', import.meta.url));
      workerRef.current = worker;

      worker.onmessage = (e) => {
        const { type, result, error, id } = e.data;
        if (type === 'ready') {
          setWasmReady(true);
          return;
        }
        if (type === 'error') {
          setWasmError(error);
          return;
        }
        if (type === 'result') {
          if (error) {
            setDiagnostics('Error: ' + error);
            return;
          }
          if (result) {
            if (result.ok) {
              if (id && id.startsWith('chk_')) {
                setDiagnostics(result.diagnostics || 'OK');
              } else if (id && id.startsWith('c_')) {
                setCOutput(result.output || '');
              } else if (id && id.startsWith('ir_')) {
                setIrOutput(result.output || '');
              }
            } else {
              const errMsg = result.error || 'Unknown error';
              if (id && id.startsWith('chk_')) {
                setDiagnostics(errMsg);
              } else if (id && id.startsWith('c_')) {
                setCOutput(errMsg);
              } else if (id && id.startsWith('ir_')) {
                setIrOutput(errMsg);
              } else {
                setDiagnostics(errMsg);
              }
            }
          }
        }
      };

      return () => worker.terminate();
    } catch {
      setWasmError('Web Workers not supported in this environment');
    }
  }, []);

  // Compile on source change (debounced 300ms)
  const compile = useCallback((src) => {
    if (!workerRef.current || !wasmReady) return;
    const id = ++reqIdRef.current;
    workerRef.current.postMessage({ type: 'check', source: src, id: 'chk_' + id });
    workerRef.current.postMessage({ type: 'emitC', source: src, id: 'c_' + id });
    workerRef.current.postMessage({ type: 'emitIR', source: src, id: 'ir_' + id });
  }, [wasmReady]);

  useEffect(() => {
    if (debounceRef.current) clearTimeout(debounceRef.current);
    debounceRef.current = setTimeout(() => compile(source), 300);
    return () => clearTimeout(debounceRef.current);
  }, [source, compile]);

  const handleExampleChange = (e) => {
    const example = EXAMPLES.find(ex => ex.name === e.target.value);
    if (example) setSource(example.code);
  };

  const tabContent = {
    'Type Check': diagnostics,
    'C Output': cOutput,
    'Verified IR': irOutput,
  };

  const tabs = ['Type Check', 'C Output', 'Verified IR'];

  return (
    <div style={{ paddingTop: '0' }}>
      {/* Page Header - consistent with other pages */}
      <section style={{ padding: '80px 32px 40px', maxWidth: '800px', margin: '0 auto' }}>
        <h1 style={{ fontSize: '48px', fontWeight: 300, marginBottom: '24px' }}>Playground</h1>
        <p style={{ fontSize: '20px', color: '#666', lineHeight: 1.8, marginBottom: '16px' }}>
          Write RIINA code in your browser. Every program that type-checks inherits
          mathematically proven security guarantees.
        </p>
        <p style={{ fontSize: '14px', color: '#999' }}>
          {wasmReady ? '✓ WASM compiler loaded' : wasmError ? `✗ ${wasmError}` : 'Loading WASM compiler...'}
        </p>
      </section>

      {/* Editor section */}
      <div style={{ padding: '0 32px 40px', maxWidth: '1200px', margin: '0 auto' }}>

      {/* Example selector */}
      <div style={{ marginBottom: 12 }}>
        <label style={{ fontSize: 13, marginRight: 8 }}>Example: </label>
        <select
          onChange={handleExampleChange}
          style={{
            fontFamily: 'monospace',
            fontSize: 13,
            padding: '4px 8px',
            border: '1px solid #ccc',
            borderRadius: 4,
            background: '#fff',
          }}
        >
          {EXAMPLES.map(ex => (
            <option key={ex.name} value={ex.name}>{ex.name}</option>
          ))}
        </select>
      </div>

      {/* Split pane */}
      <div style={{ display: 'flex', gap: 16, minHeight: 400 }}>
        {/* Editor */}
        <div style={{ flex: 1, display: 'flex', flexDirection: 'column' }}>
          <div style={{
            fontSize: 12, fontWeight: 600, marginBottom: 4, color: '#333',
            textTransform: 'uppercase', letterSpacing: '0.05em'
          }}>
            Source
          </div>
          <textarea
            value={source}
            onChange={(e) => setSource(e.target.value)}
            spellCheck={false}
            style={{
              flex: 1,
              fontFamily: '"JetBrains Mono", "Fira Code", "Cascadia Code", monospace',
              fontSize: 14,
              lineHeight: 1.6,
              padding: 16,
              border: '1px solid #ddd',
              borderRadius: 6,
              resize: 'none',
              outline: 'none',
              background: '#fafafa',
              tabSize: 2,
            }}
          />
        </div>

        {/* Output */}
        <div style={{ flex: 1, display: 'flex', flexDirection: 'column' }}>
          {/* Tabs */}
          <div style={{ display: 'flex', gap: 0, marginBottom: 4 }}>
            {tabs.map(tab => (
              <button
                key={tab}
                onClick={() => setActiveTab(tab)}
                style={{
                  padding: '6px 16px',
                  fontSize: 12,
                  fontWeight: activeTab === tab ? 600 : 400,
                  background: activeTab === tab ? '#333' : '#eee',
                  color: activeTab === tab ? '#fff' : '#555',
                  border: 'none',
                  borderRadius: tab === tabs[0] ? '6px 0 0 0' : tab === tabs[tabs.length - 1] ? '0 6px 0 0' : 0,
                  cursor: 'pointer',
                  textTransform: 'uppercase',
                  letterSpacing: '0.05em',
                }}
              >
                {tab}
              </button>
            ))}
          </div>
          <pre style={{
            flex: 1,
            fontFamily: '"JetBrains Mono", "Fira Code", monospace',
            fontSize: 13,
            lineHeight: 1.5,
            padding: 16,
            border: '1px solid #ddd',
            borderRadius: '0 6px 6px 6px',
            overflow: 'auto',
            background: '#1e1e1e',
            color: '#d4d4d4',
            margin: 0,
            whiteSpace: 'pre-wrap',
          }}>
            {tabContent[activeTab] || (wasmReady ? 'Compiling...' : 'Loading WASM...')}
          </pre>
        </div>
      </div>

      {/* Footer info */}
      <div style={{ marginTop: 24, fontSize: 12, color: '#999', textAlign: 'center' }}>
        RIINA Compiler v0.2.0 · 6,194 theorems proven · Zero external dependencies · MPL-2.0
      </div>
      </div>
    </div>
  );
};

export default PlaygroundPage;
