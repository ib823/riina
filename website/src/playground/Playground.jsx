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
cetak("Hello, " + nama + "!");`
  },
  {
    name: 'Fibonacci',
    code: `// Fibonacci sequence
fungsi fibonacci(n: Nombor) -> Nombor {
  kalau n <= 1 {
    pulang n;
  }
  pulang fibonacci(n - 1) + fibonacci(n - 2);
}
biar hasil = fibonacci(10);`
  },
  {
    name: 'Secret Type',
    code: `// Secret type demonstration
biar kunci: Rahsia<Teks> = rahsia("kata-laluan-123");
// This would be rejected by the type checker:
// cetak(kunci);  // ERROR: cannot declassify without policy
biar selamat = dedah(kunci, dasar: "audit_log");`
  },
  {
    name: 'Effect Gate',
    code: `// Effect-gated I/O
fungsi baca_fail(nama: Teks) -> Teks kesan IO {
  biar isi = baca(nama);
  pulang isi;
}
// Pure functions cannot call effectful ones
fungsi kira(x: Nombor) -> Nombor bersih {
  pulang x * 2;
}`
  },
  {
    name: 'Pattern Match',
    code: `// Pattern matching
biar bentuk = Bulatan(5.0);
biar luas = padan bentuk {
  Bulatan(r) => 3.14159 * r * r,
  SegiEmpat(w, h) => w * h,
  Segitiga(b, h) => 0.5 * b * h,
};`
  }
];

const PlaygroundPage = ({ onNavigate }) => {
  const [source, setSource] = useState(EXAMPLES[0].code);
  const [activeTab, setActiveTab] = useState('diagnostics');
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
              if (result.diagnostics !== undefined) setDiagnostics(result.diagnostics);
              if (result.output !== undefined) {
                // Determine which tab requested this
                if (id && id.startsWith('c_')) setCOutput(result.output);
                else if (id && id.startsWith('ir_')) setIrOutput(result.output);
                else setDiagnostics(result.diagnostics || 'OK');
              }
            } else {
              setDiagnostics(result.error || 'Unknown error');
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
    diagnostics,
    'C Output': cOutput,
    IR: irOutput,
  };

  const tabs = ['diagnostics', 'C Output', 'IR'];

  return (
    <div style={{ padding: '0 40px 40px' }}>
      <div style={{ marginBottom: 24 }}>
        <h1 style={{ fontSize: 28, fontWeight: 700, marginBottom: 8 }}>
          Playground
        </h1>
        <p style={{ color: '#666', fontSize: 14 }}>
          Write RIINA code and see diagnostics, C output, and IR in real time.
          {!wasmReady && !wasmError && ' Loading WASM compiler...'}
          {wasmError && <span style={{ color: '#c00' }}> {wasmError}</span>}
        </p>
      </div>

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
      <div style={{ marginTop: 16, fontSize: 12, color: '#999' }}>
        RIINA Compiler v0.1.0 · Powered by WebAssembly · Zero server-side processing ·{' '}
        <span style={{ cursor: 'pointer', textDecoration: 'underline' }}
              onClick={() => onNavigate && onNavigate('docs')}>
          Documentation
        </span>
      </div>
    </div>
  );
};

export default PlaygroundPage;
