import { useState, useEffect } from 'react';

// Fallback defaults (used while loading or on fetch error).
// Keep in sync with the *shape* of metrics.json — values here are stale-safe minimums.
const DEFAULTS = {
  version: '0.0.0',
  proofs: { qedActive: 0, admitted: 0, axioms: 0, assumptions: 0 },
  coq: { filesActive: 0, filesTotal: 0, prover: 'Coq 8.20.1' },
  lean: { theorems: 0, files: 0, prover: 'Lean 4', sorry: 0 },
  isabelle: { lemmas: 0, files: 0, prover: 'Isabelle/HOL', sorry: 0 },
  fstar: { lemmas: 0, files: 0, prover: 'F*' },
  tlaplus: { theorems: 0, files: 0, prover: 'TLA+' },
  alloy: { assertions: 0, files: 0, prover: 'Alloy 6' },
  smt: { assertions: 0, files: 0, prover: 'Z3/CVC5 (SMT-LIB)' },
  verus: { proofs: 0, files: 0, prover: 'Verus' },
  kani: { harnesses: 0, files: 0, prover: 'Kani' },
  tv: { validations: 0, files: 0, prover: 'Translation Validation' },
  multiProver: {
    tripleProverTheorems: 0,
    totalProofsAllProvers: 0,
    totalProvers: 10,
    sorry: 0,
    status: 'IN_PROGRESS',
  },
  quality: {
    coqCompiled: false,
    leanCompiled: false,
    isabelleCompiled: false,
    fstarStatus: 'generated',
    tlaplusStatus: 'generated',
    alloyStatus: 'generated',
    smtStatus: 'generated',
    verusStatus: 'generated',
    kaniStatus: 'generated',
    tvStatus: 'generated',
    coqTiers: { core: 0, domain: 0, domainTrivial: 0 },
  },
  claimLevels: {
    legend: ['generated', 'compiled', 'mechanized', 'independently_audited'],
    overall: 'generated',
    independentlyAudited: false,
    coq: 'generated',
    lean: 'generated',
    isabelle: 'generated',
    fstar: 'generated',
    tlaplus: 'generated',
    alloy: 'generated',
    smt: 'generated',
    verus: 'generated',
    kani: 'generated',
    tv: 'generated',
  },
  rust: { tests: 0, crates: 0 },
  examples: 0,
  status: { threats: 'unknown', build: 'unknown', grade: 'unverified' },
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
