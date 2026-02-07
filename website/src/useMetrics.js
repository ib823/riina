import { useState, useEffect } from 'react';

// Fallback defaults (used while loading or on fetch error).
// Keep in sync with the *shape* of metrics.json — values here are stale-safe minimums.
const DEFAULTS = {
  version: '0.2.0',
  proofs: { qedActive: 7929, admitted: 0, axioms: 1 },
  coq: { filesActive: 250, filesTotal: 284, prover: 'Coq 8.20.1' },
  lean: { theorems: 7928, files: 255, prover: 'Lean 4' },
  isabelle: { lemmas: 8072, files: 260, prover: 'Isabelle/HOL' },
  multiProver: {
    tripleProverTheorems: 7229,
    totalProofsAllProvers: 82982,
    totalProvers: 10,
    sorry: 0,
  },
  rust: { tests: 852, crates: 15 },
  examples: 130,
  status: { threats: '1231+' },
};

export function useMetrics() {
  const [metrics, setMetrics] = useState(DEFAULTS);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    fetch(import.meta.env.BASE_URL + 'metrics.json')
      .then(r => r.json())
      .then(data => { setMetrics(data); setLoading(false); })
      .catch(() => setLoading(false));
  }, []);

  return { metrics, loading };
}

// Format a number with commas: 82982 → "82,982"
export const fmt = (n) => Number(n).toLocaleString('en-US');
