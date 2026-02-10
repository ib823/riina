import React, { useState, useEffect } from 'react';
import PlaygroundPage from './playground/Playground.jsx';
import { useMetrics, fmt } from './useMetrics.js';

// ============================================================================
// RIINA WEBSITE — 7-PAGE DARK-MODE REWRITE
// ============================================================================

const RiinaWebsite = () => {
  const [currentPage, setCurrentPage] = useState('home');
  const [mobileMenuOpen, setMobileMenuOpen] = useState(false);
  const { metrics } = useMetrics();

  useEffect(() => { window.scrollTo(0, 0); }, [currentPage]);

  // Release data (auto-updated by scripts/release.sh)
  const releases = [
    // RELEASES_MARKER
    {
      version: '0.2.0',
      date: '2026-02-10',
      highlights: [
        'Production-active proofs: 7,740 Coq Qed, 0 Admitted, 0 active axioms',
        '10-prover metrics published: 82,968 total artifacts across Coq, Lean, Isabelle, F*, TLA+, Alloy, SMT, Verus, Kani, TV',
        'Public quality gates added (artifact hygiene, doc drift checks, metrics alignment, version/tag alignment)',
        'Repository transparency: AXIOMS.md and PROOF_STATUS.md generated and enforced',
      ],
    },
    {
      version: '0.1.0',
      date: '2026-02-01',
      highlights: [
        'Initial RIINA compiler release with Bahasa Melayu syntax',
        'Core formal verification baseline and proof-driven type/effect security',
        'Standard library, package manager, VS Code support, and examples',
      ],
    },
  ];

  const nav = (page) => { setCurrentPage(page); setMobileMenuOpen(false); };

  // Logo
  const Logo = ({ size = 28 }) => (
    <svg viewBox="0 0 100 100" width={size} height={size}>
      <line x1="35" y1="22" x2="35" y2="78" stroke="#e4e4e7" strokeWidth="7" strokeLinecap="square"/>
      <line x1="35" y1="50" x2="72" y2="50" stroke="#e4e4e7" strokeWidth="7" strokeLinecap="square"/>
    </svg>
  );

  // ============================================================================
  // HEADER
  // ============================================================================
  const Header = () => (
    <header className="site-header">
      <div className="header-inner">
        <button className="header-logo" onClick={() => nav('home')}>
          <Logo size={24} />
          <span>RIINA</span>
        </button>

        <button className="hamburger" onClick={() => setMobileMenuOpen(!mobileMenuOpen)} aria-label="Menu">
          <svg width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2">
            <line x1="3" y1="6" x2="21" y2="6"/><line x1="3" y1="12" x2="21" y2="12"/><line x1="3" y1="18" x2="21" y2="18"/>
          </svg>
        </button>

        <nav className="site-nav">
          {['Language', 'Playground', 'Docs', 'Enterprise', 'How'].map(p => (
            <button key={p} onClick={() => nav(p.toLowerCase())} className={`nav-btn${currentPage === p.toLowerCase() ? ' nav-btn--active' : ''}`}>
              {p}
            </button>
          ))}
        </nav>

        <a className="header-github" href="https://github.com/ib823/riina">GitHub</a>
      </div>

      <div className={`mobile-menu${mobileMenuOpen ? ' open' : ''}`}>
        <button className="mobile-menu-close" onClick={() => setMobileMenuOpen(false)}>&#x2715;</button>
        {['Home', 'Language', 'Playground', 'Docs', 'Enterprise', 'How'].map(p => (
          <button key={p} onClick={() => nav(p === 'Home' ? 'home' : p.toLowerCase())}>{p}</button>
        ))}
        <a href="https://github.com/ib823/riina">GitHub</a>
      </div>
    </header>
  );

  // ============================================================================
  // HOME PAGE — 4-Act Conversion Funnel
  // ============================================================================
  const HomePage = () => (
    <div>
      {/* Act 1: Hero */}
      <section className="hero">
        <p className="hero-stat-line">
          <span>{fmt(metrics.multiProver.totalProofsAllProvers)}</span> proofs &middot; <span>{metrics.multiProver.totalProvers}</span> provers &middot; <span>{metrics.proofs.admitted}</span> admits &middot; <span>{metrics.proofs.axioms}</span> axiom &middot; Verified
        </p>
        <h1>
          Security<br/><strong>proven at compile time.</strong>
        </h1>
        <div className="hero-cta">
          <button onClick={() => nav('playground')} className="btn btn--primary">Try It</button>
          <a href="https://github.com/ib823/riina" className="btn btn--outline">GitHub</a>
        </div>
      </section>

      {/* Act 2: Show — Side-by-side code */}
      <section className="act-show">
        <p className="act-show__label">What it looks like</p>
        <div className="code-panels">
          <div className="code-panel">
            <div className="code-panel__label">pengesahan.rii</div>
            <pre>{`// Authentication in RIINA
`}<span className="syn-kw">modul</span>{` pengesahan;

`}<span className="syn-kw">bentuk</span>{` Kelayakan {
    nama_pengguna: `}<span className="syn-ty">Teks</span>{`,
    kata_laluan: `}<span className="syn-ty">Rahsia</span>{`<`}<span className="syn-ty">Teks</span>{`>,
    garam: `}<span className="syn-ty">Bait</span>{`,
}

`}<span className="syn-cm">// Hash with constant-time protection</span>{`
`}<span className="syn-kw">fungsi</span>{` `}<span className="syn-fn">hash_kata_laluan</span>{`(
    kata: `}<span className="syn-ty">Rahsia</span>{`<`}<span className="syn-ty">Teks</span>{`>,
    garam: `}<span className="syn-ty">Bait</span>{`
) -> `}<span className="syn-ty">Rahsia</span>{`<`}<span className="syn-ty">Bait</span>{`> `}<span className="syn-kw">kesan</span>{` Kripto {
    `}<span className="syn-kw">masa_tetap</span>{` {
        `}<span className="syn-kw">biar</span>{` derivasi = kripto::argon2id(kata, garam);
        `}<span className="syn-kw">pulang</span>{` derivasi;
    }
}`}</pre>
          </div>
          <div className="code-panel">
            <div className="code-panel__label">Compiler proof output</div>
            <pre><span className="syn-cm">{`// riinac check pengesahan.rii

`}</span><span className="syn-ty">{`Checking`}</span>{` pengesahan.rii...

`}<span className="syn-cm">{`// Security properties proven:`}</span>{`
`}<span className="syn-kw">{`\u22a2`}</span>{` No secret leakage (`}<span className="syn-ty">{`Rahsia`}</span>{` type enforced)
`}<span className="syn-kw">{`\u22a2`}</span>{` No timing attack (`}<span className="syn-ty">{`masa_tetap`}</span>{` block verified)
`}<span className="syn-kw">{`\u22a2`}</span>{` Effects tracked (`}<span className="syn-ty">{`kesan Kripto`}</span>{` declared)
`}<span className="syn-kw">{`\u22a2`}</span>{` Proof certificate generated

`}<span className="syn-cm">{`// Theorems referenced:`}</span>{`
  NonInterference_v2.fundamental_theorem
  TypeSafety.progress
  TypeSafety.preservation
  EffectSafety.effect_soundness

`}<span className="syn-str">{`All checks passed.`}</span></pre>
          </div>
        </div>
        <p className="act-show__note">
          RIINA uses Bahasa Melayu (Malaysian) keywords. <code style={{color:'var(--text-keyword)'}}>fungsi</code> = fn,{' '}
          <code style={{color:'var(--text-keyword)'}}>biar</code> = let,{' '}
          <code style={{color:'var(--text-keyword)'}}>pulang</code> = return,{' '}
          <code style={{color:'var(--text-accent)'}}>Rahsia</code> = Secret.
        </p>
      </section>

      {/* Vibesafe — The AI-friendly language */}
      <section className="act-vibesafe">
        <div className="act-vibesafe__inner">
          <div className="act-vibesafe__text">
            <div className="act-vibesafe__badge">Vibesafe</div>
            <h2 className="act-vibesafe__title">
              The only language where<br /><strong>vibe coding is safe.</strong>
            </h2>
            <p className="act-vibesafe__desc">
              Let AI write your code. Let the compiler prove it correct. Every function
              an LLM generates gets the same mathematical verification as hand-written code &mdash;
              type safety, non-interference, and effect soundness, checked before a single byte runs.
            </p>
            <ul className="act-vibesafe__points">
              <li>AI-generated code is verified identically to human code</li>
              <li>Security properties cannot be bypassed, even by hallucination</li>
              <li>Proof certificates are machine-checked, not trust-based</li>
              <li>Vibe code. Ship proven.</li>
            </ul>
          </div>
          <div className="act-vibesafe__visual">
            <div className="vibesafe-flow__step">
              <span className="vibesafe-flow__num">1</span>
              <span>You prompt: <span style={{color:'var(--text-string)'}}>"auth endpoint"</span></span>
            </div>
            <div className="vibesafe-flow__step">
              <span className="vibesafe-flow__num">2</span>
              <span>AI generates <code style={{color:'var(--text-keyword)'}}>fungsi</code> code</span>
            </div>
            <div className="vibesafe-flow__arrow">{'\u2193'}</div>
            <div className="vibesafe-flow__step">
              <span className="vibesafe-flow__num">3</span>
              <span><code style={{color:'var(--text-accent)'}}>riinac check</code> runs</span>
            </div>
            <div className="vibesafe-flow__step">
              <span className="vibesafe-flow__num" />
              <span style={{color:'var(--text-muted)',fontSize:12}}>{'\u22a2'} type safety proven</span>
            </div>
            <div className="vibesafe-flow__step">
              <span className="vibesafe-flow__num" />
              <span style={{color:'var(--text-muted)',fontSize:12}}>{'\u22a2'} no secret leakage</span>
            </div>
            <div className="vibesafe-flow__step">
              <span className="vibesafe-flow__num" />
              <span style={{color:'var(--text-muted)',fontSize:12}}>{'\u22a2'} effects declared</span>
            </div>
            <div className="vibesafe-flow__arrow">{'\u2193'}</div>
            <div className="vibesafe-flow__result">
              {'\u2714'} Ship it. It's proven.
            </div>
          </div>
        </div>
      </section>

      {/* Act 3: Proof — Terminal verification */}
      <section className="act-proof">
        <div className="act-proof__header">
          <h2 className="act-proof__title">Don't trust us. <strong>Verify it.</strong></h2>
          <p className="act-proof__subtitle">Every claim has a machine-checked proof. Run them yourself.</p>
        </div>

        <div className="terminal-block">
          <div><span className="prompt">$ </span><span className="cmd">git clone https://github.com/ib823/riina.git && cd riina</span></div>
          <div><span className="prompt">$ </span><span className="cmd">cd 02_FORMAL/coq && make</span></div>
          <div style={{color:'var(--text-string)'}}>Compiling {metrics.coq.filesActive} files... done. 0 errors.</div>
          <div><span className="prompt">$ </span><span className="cmd">grep -c "Qed\." **/*.v</span></div>
          <div style={{color:'var(--text-accent)'}}>{metrics.proofs.qedActive}</div>
          <div><span className="prompt">$ </span><span className="cmd">grep -c "Admitted\." **/*.v</span></div>
          <div style={{color:'var(--text-string)'}}>{metrics.proofs.admitted}</div>
        </div>

        <div className="proof-pillars">
          <div className="proof-pillar">
            <div className="proof-pillar__icon">{'\u22a2'}</div>
            <div className="proof-pillar__name">Type Safety</div>
            <div className="proof-pillar__desc">Progress + Preservation. Well-typed programs do not get stuck.</div>
          </div>
          <div className="proof-pillar">
            <div className="proof-pillar__icon">{'\u22a2'}</div>
            <div className="proof-pillar__name">Non-Interference</div>
            <div className="proof-pillar__desc">Secret data cannot flow to public outputs. Proven via logical relations.</div>
          </div>
          <div className="proof-pillar">
            <div className="proof-pillar__icon">{'\u22a2'}</div>
            <div className="proof-pillar__name">Effect Soundness</div>
            <div className="proof-pillar__desc">Only declared effects can be performed. No hidden side effects.</div>
          </div>
        </div>

        <div className="triple-prover">
          <h3 className="triple-prover__title">{metrics.multiProver.totalProvers} provers. One truth.</h3>
          <p className="triple-prover__desc">
            Core theorems independently verified across {metrics.multiProver.totalProvers} proof systems with different mathematical
            foundations. A bug in one prover cannot compromise the guarantees.
          </p>
          <div className="triple-prover__grid">
            {[
              { prover: metrics.coq.prover, count: fmt(metrics.proofs.qedActive), role: 'Primary', foundation: 'CIC' },
              { prover: metrics.lean.prover, count: fmt(metrics.lean.theorems), role: 'Secondary', foundation: 'DTT' },
              { prover: metrics.isabelle.prover, count: fmt(metrics.isabelle.lemmas), role: 'Tertiary', foundation: 'HOL' },
              { prover: (metrics.fstar || {}).prover || 'F*', count: fmt((metrics.fstar || {}).lemmas || 0), role: 'Dependent types', foundation: 'DTT' },
              { prover: (metrics.tlaplus || {}).prover || 'TLA+', count: fmt((metrics.tlaplus || {}).theorems || 0), role: 'Model checking', foundation: 'TLA' },
              { prover: (metrics.alloy || {}).prover || 'Alloy 6', count: fmt((metrics.alloy || {}).assertions || 0), role: 'Relational logic', foundation: 'FOL' },
              { prover: (metrics.smt || {}).prover || 'Z3/CVC5', count: fmt((metrics.smt || {}).assertions || 0), role: 'SMT solving', foundation: 'SMT-LIB' },
              { prover: (metrics.verus || {}).prover || 'Verus', count: fmt((metrics.verus || {}).proofs || 0), role: 'Rust verification', foundation: 'VIR' },
              { prover: (metrics.kani || {}).prover || 'Kani', count: fmt((metrics.kani || {}).harnesses || 0), role: 'Model checking', foundation: 'CBMC' },
              { prover: (metrics.tv || {}).prover || 'Translation Validation', count: fmt((metrics.tv || {}).validations || 0), role: 'Binary equivalence', foundation: 'TV' },
            ].map((p, i) => (
              <div key={i} className="triple-prover__card">
                <div className="triple-prover__prover">{p.prover}</div>
                <div className="triple-prover__count">{p.count}</div>
                <div className="triple-prover__role">{p.role} &middot; {p.foundation}</div>
              </div>
            ))}
          </div>
          <p className="triple-prover__note">
            {fmt(metrics.multiProver.tripleProverTheorems)} triple-prover theorems &middot; {metrics.multiProver.sorry} sorry &middot; {metrics.proofs.axioms} justified axiom &middot; {metrics.multiProver.totalProvers} provers
          </p>
        </div>
      </section>

      {/* Act 4: Start */}
      <section className="act-start">
        <div className="act-start__header">
          <h2 style={{fontSize:'28px',fontWeight:300}}>Get started</h2>
        </div>
        <div className="start-cards">
          <div className="card card--hover" onClick={() => nav('playground')}>
            <div className="start-card__title">Playground</div>
            <div className="start-card__desc">Write RIINA in your browser. No install.</div>
          </div>
          <div className="card card--hover" onClick={() => nav('docs')}>
            <div className="start-card__title">Install</div>
            <div className="start-card__desc">curl -fsSL ib823.github.io/riina/install.sh | bash</div>
          </div>
          <div className="card card--hover" onClick={() => nav('docs')}>
            <div className="start-card__title">Documentation</div>
            <div className="start-card__desc">Language guide, CLI reference, examples.</div>
          </div>
        </div>
        <p className="act-start__footer">Open source &middot; Proprietary &middot; Zero dependencies</p>
      </section>
    </div>
  );

  // ============================================================================
  // LANGUAGE PAGE — Tabs: Syntax, Types, Effects, Stdlib
  // ============================================================================
  const LanguagePage = () => {
    const [tab, setTab] = useState('syntax');

    const keywords = {
      declarations: [
        { bm: 'fungsi', en: 'fn' }, { bm: 'biar', en: 'let' }, { bm: 'ubah', en: 'mut' },
        { bm: 'tetap', en: 'const' }, { bm: 'bentuk', en: 'struct' }, { bm: 'pilihan', en: 'enum' },
        { bm: 'jenis', en: 'type' }, { bm: 'sifat', en: 'trait' }, { bm: 'laksana', en: 'impl' },
        { bm: 'modul', en: 'mod' }, { bm: 'guna', en: 'use' }, { bm: 'awam', en: 'pub' },
      ],
      controlFlow: [
        { bm: 'kalau', en: 'if' }, { bm: 'lain', en: 'else' }, { bm: 'untuk', en: 'for' },
        { bm: 'selagi', en: 'while' }, { bm: 'ulang', en: 'loop' }, { bm: 'pulang', en: 'return' },
        { bm: 'padan', en: 'match' }, { bm: 'keluar', en: 'break' }, { bm: 'terus', en: 'continue' },
      ],
      types: [
        { bm: 'Nombor', en: 'Int' }, { bm: 'Teks', en: 'String' }, { bm: 'Benar', en: 'Bool' },
        { bm: 'Pecahan', en: 'Float' }, { bm: 'Bait', en: 'Bytes' }, { bm: 'Senarai', en: 'Vec' },
        { bm: 'Peta', en: 'Map' }, { bm: 'Mungkin', en: 'Option' }, { bm: 'Hasil', en: 'Result' },
      ],
      security: [
        { bm: 'rahsia', en: 'secret' }, { bm: 'dedah', en: 'declassify' }, { bm: 'bukti', en: 'prove' },
        { bm: 'masa_tetap', en: 'constant-time' }, { bm: 'kesan', en: 'effect' },
        { bm: 'bahaya', en: 'unsafe' }, { bm: 'selamat', en: 'safe' },
      ],
      effects: [
        { bm: 'Bersih', en: 'Pure' }, { bm: 'Baca', en: 'Read' }, { bm: 'Tulis', en: 'Write' },
        { bm: 'Rangkaian', en: 'Network' }, { bm: 'Kripto', en: 'Crypto' }, { bm: 'Sistem', en: 'System' },
      ],
    };

    const KwSection = ({ title, items }) => (
      <div style={{marginBottom:32}}>
        <h3 style={{fontSize:12,fontFamily:'var(--font-mono)',color:'var(--text-muted)',textTransform:'uppercase',letterSpacing:'0.1em',marginBottom:16}}>{title}</h3>
        <div className="kw-grid">
          {items.map((kw, i) => (
            <div key={i} className="kw-item">
              <span className="kw-item__bm">{kw.bm}</span>
              <span className="kw-item__en">{kw.en}</span>
            </div>
          ))}
        </div>
      </div>
    );

    return (
      <div>
        <section className="section--sm">
          <div className="container--narrow">
            <h1 style={{fontSize:40,fontWeight:300,marginBottom:16}}>Language</h1>
            <p style={{color:'var(--text-secondary)',fontSize:16}}>
              Bahasa Melayu keywords, compile-time security types, and a tracked effect system.
            </p>
          </div>
        </section>

        <section style={{padding:'0 24px 80px'}}>
          <div style={{maxWidth:'var(--max-w-page)',margin:'0 auto'}}>
            <div className="tabs">
              {['Syntax', 'Types', 'Effects', 'Stdlib'].map(t => (
                <button key={t} onClick={() => setTab(t.toLowerCase())} className={`tab-btn${tab === t.toLowerCase() ? ' tab-btn--active' : ''}`}>{t}</button>
              ))}
            </div>

            {tab === 'syntax' && (
              <div style={{maxWidth:'var(--max-w-code)'}}>
                <KwSection title="Declarations" items={keywords.declarations} />
                <KwSection title="Control Flow" items={keywords.controlFlow} />
                <KwSection title="Built-in Types" items={keywords.types} />
                <KwSection title="Security" items={keywords.security} />
                <KwSection title="Effects" items={keywords.effects} />

                <h3 style={{fontSize:12,fontFamily:'var(--font-mono)',color:'var(--text-muted)',textTransform:'uppercase',letterSpacing:'0.1em',marginBottom:16,marginTop:32}}>Example</h3>
                <pre className="code-block">{`// pengesahan.rii — Authentication
modul pengesahan;

bentuk Kelayakan {
    nama_pengguna: Teks,
    kata_laluan: Rahsia<Teks>,
    garam: Bait,
}

fungsi hash_kata_laluan(
    kata: Rahsia<Teks>,
    garam: Bait
) -> Rahsia<Bait> kesan Kripto {
    masa_tetap {
        biar derivasi = kripto::argon2id(kata, garam);
        pulang derivasi;
    }
}`}</pre>
              </div>
            )}

            {tab === 'types' && (
              <div style={{maxWidth:'var(--max-w-text)'}}>
                {[
                  { name: 'Rahsia<T>', en: 'Secret', desc: 'Wraps sensitive values. Cannot be logged, printed, or sent over the network. Must be explicitly declassified with dedah() and a policy proof.' },
                  { name: 'Terbuka<T>', en: 'Public', desc: 'Marks data as public. Can flow anywhere freely. Default for unannotated types.' },
                  { name: 'Tercemar<T,S>', en: 'Tainted', desc: 'Marks data from untrusted sources. Must be sanitized before use in security-sensitive operations.' },
                  { name: 'MasaTetap<T>', en: 'ConstantTime', desc: 'Operations execute in constant time regardless of secret values. Prevents timing side-channel attacks.' },
                  { name: 'Bukti<T>', en: 'Proof', desc: 'Compile-time proof witness. Carries no runtime data. Proves security policies are satisfied.' },
                ].map((t, i) => (
                  <div key={i} className="security-type-card">
                    <h3><code>{t.name}</code> <span style={{fontSize:12,color:'var(--text-muted)',fontFamily:'var(--font-sans)'}}>({t.en})</span></h3>
                    <p>{t.desc}</p>
                  </div>
                ))}

                <h3 style={{fontSize:12,fontFamily:'var(--font-mono)',color:'var(--text-muted)',textTransform:'uppercase',letterSpacing:'0.1em',marginBottom:16,marginTop:40}}>RIINA vs Rust</h3>
                <pre className="code-block">{`// Rust — compiles, but leaks secrets:
fn process(card: String) -> String {
    println!("{}", card);  // secret logged! No error.
    format!("Done")
}

// RIINA — compiler catches the leak:
fungsi proses(kad: Rahsia<Teks>) -> Teks kesan Kripto {
    cetakln(kad);  // COMPILE ERROR
    //  ^ Rahsia<Teks> cannot flow to IO
    //  ^ Non-interference violation
    pulang "Selesai";
}`}</pre>
              </div>
            )}

            {tab === 'effects' && (
              <div style={{maxWidth:'var(--max-w-text)'}}>
                <p style={{color:'var(--text-secondary)',marginBottom:32}}>
                  Every side effect is declared in the function signature and tracked by the compiler.
                </p>
                {[
                  { name: 'Bersih', en: 'Pure', desc: 'No side effects. Default. Provably terminating.' },
                  { name: 'Baca', en: 'Read', desc: 'File system read access.' },
                  { name: 'Tulis', en: 'Write', desc: 'File system write, stdout, logging.' },
                  { name: 'Rangkaian', en: 'Network', desc: 'Network I/O: HTTP, TCP, DNS.' },
                  { name: 'Kripto', en: 'Crypto', desc: 'Cryptographic operations. Implies constant-time.' },
                  { name: 'Sistem', en: 'System', desc: 'System calls, process management.' },
                ].map((e, i) => (
                  <div key={i} style={{display:'flex',gap:16,alignItems:'baseline',padding:'8px 0',borderBottom:'1px solid var(--border)'}}>
                    <code style={{color:'var(--text-keyword)',minWidth:100,fontWeight:500}}>{e.name}</code>
                    <span style={{color:'var(--text-muted)',fontSize:12,minWidth:60}}>({e.en})</span>
                    <span style={{color:'var(--text-secondary)',fontSize:14}}>{e.desc}</span>
                  </div>
                ))}

                <pre className="code-block" style={{marginTop:32}}>{`// Effects compose with +
fungsi muat_dan_nyahsulit(
    laluan: Teks,
    kunci: Rahsia<Bait>
) -> Rahsia<Teks> kesan Baca + Kripto {
    biar data = laku Baca baca_fail(laluan);
    biar teks = laku Kripto nyahsulit(data, kunci);
    pulang teks;
}

// The compiler REJECTS effect violations:
// fungsi bocor() -> Teks kesan Bersih {
//     laku Rangkaian hantar(data);
//     ^ COMPILE ERROR: Rangkaian not in effect set
// }`}</pre>
              </div>
            )}

            {tab === 'stdlib' && (
              <div style={{maxWidth:'var(--max-w-text)'}}>
                <p style={{color:'var(--text-secondary)',marginBottom:32}}>
                  ~38 unique builtins with bilingual names (Bahasa Melayu and English). Effect-gated I/O.
                </p>
                {[
                  { mod: 'teks', en: 'String', fns: 'panjang, gabung, potong, pecah, ganti, mengandungi' },
                  { mod: 'senarai', en: 'List', fns: 'tolak, cabut, peta, tapis, lipat, isih, terbalik, cari' },
                  { mod: 'peta', en: 'Map', fns: 'masuk, dapatkan, buang, kunci, nilai, pasangan' },
                  { mod: 'matematik', en: 'Math', fns: 'mutlak, min, max, kuasa, punca, log, bundar' },
                  { mod: 'penukaran', en: 'Conversion', fns: 'ke_teks, hurai_nombor, hurai_pecahan, ke_bait' },
                  { mod: 'ujian', en: 'Testing', fns: 'tegaskan, tegaskan_sama, tegaskan_tak_sama, panik' },
                  { mod: 'masa', en: 'Time', fns: 'sekarang, cap_masa, tempoh, format, tidur' },
                  { mod: 'fail', en: 'File', fns: 'baca, tulis, wujud, padam, senarai_dir' },
                ].map((m, i) => (
                  <div key={i} style={{padding:'12px 0',borderBottom:'1px solid var(--border)'}}>
                    <div style={{display:'flex',gap:8,alignItems:'baseline',marginBottom:4}}>
                      <code style={{color:'var(--text-accent)',fontWeight:500}}>std::{m.mod}</code>
                      <span style={{color:'var(--text-muted)',fontSize:12}}>({m.en})</span>
                    </div>
                    <div style={{fontSize:13,color:'var(--text-secondary)',fontFamily:'var(--font-mono)'}}>{m.fns}</div>
                  </div>
                ))}
              </div>
            )}
          </div>
        </section>
      </div>
    );
  };

  // ============================================================================
  // DOCS PAGE — Tabs: Quick Start, Reference, Contributing, Releases
  // ============================================================================
  const DocsPage = () => {
    const [tab, setTab] = useState('quickstart');

    return (
      <div>
        <section className="section--sm">
          <div className="container--narrow">
            <h1 style={{fontSize:40,fontWeight:300,marginBottom:16}}>Documentation</h1>
            <p style={{color:'var(--text-secondary)'}}>Install, build, and contribute to RIINA.</p>
          </div>
        </section>

        <section style={{padding:'0 24px 80px'}}>
          <div style={{maxWidth:'var(--max-w-page)',margin:'0 auto'}}>
            <div className="tabs">
              {[['quickstart','Quick Start'],['reference','Reference'],['contributing','Contributing'],['releases','Releases']].map(([id,label]) => (
                <button key={id} onClick={() => setTab(id)} className={`tab-btn${tab === id ? ' tab-btn--active' : ''}`}>{label}</button>
              ))}
            </div>

            {tab === 'quickstart' && (
              <div style={{maxWidth:'var(--max-w-text)'}}>
                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>Install</h2>
                <pre className="code-block" style={{marginBottom:32}}>{`# From source
git clone https://github.com/ib823/riina.git
cd riina/03_PROTO
cargo build --release

# Docker
docker build -t riina .
docker run --rm riina check myfile.rii

# Portable installer
curl -sSf https://ib823.github.io/riina/install.sh | bash

# Nix
nix run github:ib823/riina`}</pre>

                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>Hello World</h2>
                <pre className="code-block" style={{marginBottom:16}}>{`// hello.rii
modul hello;
guna std::io;

awam fungsi utama() -> kesan Tulis {
    biar mesej = "Selamat datang ke RIINA!";
    laku Tulis cetak_baris(mesej);
}`}</pre>
                <pre className="code-block">{`riinac check hello.rii    # Type-check + verify
riinac run hello.rii      # Run directly
riinac build hello.rii    # Compile to native binary`}</pre>
              </div>
            )}

            {tab === 'reference' && (
              <div style={{maxWidth:'var(--max-w-text)'}}>
                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>CLI Commands</h2>
                {[
                  ['riinac check', 'Type-check and verify security properties'],
                  ['riinac run', 'Execute .rii file directly'],
                  ['riinac build', 'Compile to native binary via C backend'],
                  ['riinac emit-c', 'Generate C source code'],
                  ['riinac emit-ir', 'Generate intermediate representation'],
                  ['riinac repl', 'Interactive REPL mode'],
                  ['riinac fmt', 'Format RIINA source code'],
                  ['riinac doc', 'Generate HTML documentation'],
                  ['riinac lsp', 'Language server for editors'],
                  ['riinac verify --fast', 'Quick verification (pre-commit)'],
                  ['riinac verify --full', 'Full verification (pre-push)'],
                  ['riinac pkg init', 'Initialize new package'],
                  ['riinac pkg add', 'Add dependency'],
                  ['riinac pkg build', 'Build package with dependencies'],
                ].map(([cmd, desc], i) => (
                  <div key={i} className="cli-row">
                    <code>{cmd}</code>
                    <span>{desc}</span>
                  </div>
                ))}

                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16,marginTop:40}}>Targets</h2>
                {[
                  ['Native (C)', 'Any platform with a C compiler'],
                  ['WebAssembly', 'Full compiler in-browser'],
                  ['Android', 'JNI bridge generation'],
                  ['iOS', 'Swift bridge generation'],
                ].map(([name, desc], i) => (
                  <div key={i} className="cli-row">
                    <code style={{minWidth:140}}>{name}</code>
                    <span>{desc}</span>
                  </div>
                ))}
              </div>
            )}

            {tab === 'contributing' && (
              <div style={{maxWidth:'var(--max-w-text)'}}>
                <p style={{color:'var(--text-secondary)',marginBottom:24}}>
                  RIINA is open source under Proprietary. Contributions to the compiler, proofs, standard library, and documentation are welcome.
                </p>
                <pre className="code-block" style={{marginBottom:24}}>{`# Setup
git clone https://github.com/ib823/riina.git && cd riina
cd 00_SETUP/scripts
./install_rust.sh && ./install_coq.sh && ./verify_setup.sh

# Build proofs
cd ../../02_FORMAL/coq && make

# Build compiler & run tests
cd ../../03_PROTO && cargo build --all && cargo test --all`}</pre>

                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>Commit format</h2>
                <pre className="code-block" style={{marginBottom:24}}>{`[TRACK_X] TYPE: Brief description

Tracks: A (Proofs), B (Compiler), C (Specs), F (Tooling)
Types:  PROOF, IMPL, FIX, DOCS, REFACTOR`}</pre>

                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>Rules</h2>
                <div style={{fontSize:14,color:'var(--text-secondary)',lineHeight:2}}>
                  {[
                    'All Coq proofs must compile with 0 Admitted',
                    'All Rust tests must pass',
                    'No unsafe Rust without documented justification',
                    'No third-party crypto dependencies',
                    'Use Bahasa Melayu keywords in all .rii examples',
                  ].map((r, i) => <div key={i}>{'\u22a2'} {r}</div>)}
                </div>
              </div>
            )}

            {tab === 'releases' && (
              <div style={{maxWidth:'var(--max-w-text)'}}>
                <pre className="code-block" style={{marginBottom:32}}>{`# Install latest
curl -fsSL https://ib823.github.io/riina/install.sh | bash`}</pre>
                {releases.map((rel, i) => (
                  <div key={i} className="card" style={{marginBottom:16}}>
                    <div style={{display:'flex',justifyContent:'space-between',alignItems:'baseline',marginBottom:12}}>
                      <span style={{fontSize:24,fontWeight:500,fontFamily:'var(--font-mono)'}}>v{rel.version}</span>
                      <span style={{color:'var(--text-muted)',fontSize:13}}>{rel.date}</span>
                    </div>
                    <ul style={{listStyle:'none',padding:0}}>
                      {rel.highlights.map((h, j) => (
                        <li key={j} style={{fontSize:14,color:'var(--text-secondary)',padding:'4px 0'}}>{h}</li>
                      ))}
                    </ul>
                    <a href={`https://github.com/ib823/riina/releases/tag/v${rel.version}`} style={{fontSize:13,marginTop:8,display:'inline-block'}}>
                      Release notes
                    </a>
                  </div>
                ))}
              </div>
            )}
          </div>
        </section>
      </div>
    );
  };

  // ============================================================================
  // ENTERPRISE PAGE — Simplified
  // ============================================================================
  const EnterprisePage = () => (
    <div>
      <section className="section--sm">
        <div className="container--narrow">
          <h1 style={{fontSize:40,fontWeight:300,marginBottom:16}}>Enterprise</h1>
          <p style={{color:'var(--text-secondary)',fontSize:16}}>Compliance, proven at compile time.</p>
        </div>
      </section>

      <section style={{padding:'0 24px 80px'}}>
        <div style={{maxWidth:'var(--max-w-page)',margin:'0 auto'}}>
          <p style={{color:'var(--text-secondary)',maxWidth:'var(--max-w-text)',marginBottom:48,lineHeight:1.8}}>
            RIINA programs carry machine-checkable proof certificates that satisfy regulatory requirements.
            When you compile, the compiler generates a compliance report mapping proven properties to specific
            regulatory controls. No manual audit. Mathematical proof.
          </p>

          <div className="industry-grid" style={{marginBottom:48}}>
            {[
              { name: 'Defence & Military', regs: 'CMMC, ITAR, NIST 800-171', desc: 'Classified data handling with proven compartmentalization. CUI isolation enforced at the type level. Side-channel resistance for signals intelligence.' },
              { name: 'Healthcare', regs: 'HIPAA, HITECH, HL7 FHIR', desc: 'PHI wrapped in security types that prevent unauthorized disclosure. Audit trails proven complete. De-identification verified at compile time.' },
              { name: 'Financial Services', regs: 'PCI-DSS, SOX, BNM RMiT', desc: 'Cardholder data isolation proven by construction. Transaction integrity with formal audit trails. Constant-time operations prevent timing attacks.' },
              { name: 'Aerospace & Aviation', regs: 'DO-178C DAL A, DO-326A', desc: 'Flight-critical software with formal verification evidence satisfying DAL A. Deterministic execution proven. WCET bounds verified.' },
            ].map((ind, i) => (
              <div key={i} className="industry-card">
                <div className="industry-card__name">{ind.name}</div>
                <div className="industry-card__regs">{ind.regs}</div>
                <div className="industry-card__desc">{ind.desc}</div>
              </div>
            ))}
          </div>

          <p style={{color:'var(--text-muted)',fontSize:14,textAlign:'center',marginBottom:48}}>
            + 11 more compliance profiles: Energy, Telecom, Government, Transportation, Manufacturing, Retail, Media, Education, Agriculture, Real Estate, Legal
          </p>

          <h2 style={{fontSize:12,fontFamily:'var(--font-mono)',color:'var(--text-muted)',textTransform:'uppercase',letterSpacing:'0.1em',marginBottom:16}}>Proof certificate</h2>
          <pre className="code-block" style={{maxWidth:'var(--max-w-text)'}}>{`$ riinac verify --compliance hipaa,pci-dss myapp.rii

RIINA COMPLIANCE CERTIFICATE
============================
Program: myapp.rii
Prover:  Coq 8.20.1

HIPAA §164.312(a) — Access Control
  PROVEN: All PHI access gated by role-based authorization
  Theorem: access_control_enforced

HIPAA §164.312(b) — Audit Controls
  PROVEN: Every PHI access logged
  Theorem: audit_trail_complete

PCI-DSS Req 3 — Protect Stored Cardholder Data
  PROVEN: Cardholder data encrypted at rest
  Theorem: stored_data_encrypted`}</pre>

          <div style={{textAlign:'center',marginTop:48}}>
            <a href="https://t.me/ib823" className="btn btn--primary">Contact for enterprise evaluation</a>
          </div>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // HOW PAGE — Architecture + Research
  // ============================================================================
  const HowPage = () => (
    <div>
      <section className="section--sm">
        <div className="container--narrow">
          <h1 style={{fontSize:40,fontWeight:300,marginBottom:16}}>How It Works</h1>
          <p style={{color:'var(--text-secondary)'}}>Architecture, verification pipeline, and research tracks.</p>
        </div>
      </section>

      <section style={{padding:'0 24px'}}>
        <div style={{maxWidth:'var(--max-w-text)',margin:'0 auto',marginBottom:80}}>
          <h2 style={{fontSize:12,fontFamily:'var(--font-mono)',color:'var(--text-muted)',textTransform:'uppercase',letterSpacing:'0.1em',marginBottom:32}}>Compilation Pipeline</h2>
          {[
            { num: '01', title: 'Security as Types', desc: 'Rahsia<T> wraps sensitive data. kesan Kripto marks crypto functions. masa_tetap ensures constant-time execution. These are compiler-enforced, not annotations.' },
            { num: '02', title: 'Effects Track Side Effects', desc: 'Every function declares its effects: kesan Baca + Kripto. The compiler tracks what your code can do. Security-critical code is restricted to specific effects.' },
            { num: '03', title: 'The Compiler Proves Security', desc: 'When you compile, the compiler proves: no information leakage (non-interference), effects are tracked (effect safety), timing-sensitive code runs in constant time, and secrets are zeroed.' },
            { num: '04', title: 'Verified End-to-End', desc: `RIINA's compiler itself is verified with riinac verify. The formal proofs (${metrics.coq.filesActive} Coq files, ${metrics.lean.files} Lean files, ${metrics.isabelle.files} Isabelle files) ship with the compiler. ${metrics.multiProver.totalProvers}-prover verification across Coq, Lean 4, Isabelle/HOL, F*, TLA+, Alloy, Z3/CVC5, Verus, Kani, and Translation Validation.` },
          ].map((step, i) => (
            <div key={i} className="pipeline-step">
              <div className="pipeline-step__num">{step.num}</div>
              <div>
                <div className="pipeline-step__title">{step.title}</div>
                <div className="pipeline-step__desc">{step.desc}</div>
              </div>
            </div>
          ))}
        </div>
      </section>

      <section className="section--alt" style={{padding:'80px 24px'}}>
        <div style={{maxWidth:'var(--max-w-text)',margin:'0 auto'}}>
          <h2 style={{fontSize:12,fontFamily:'var(--font-mono)',color:'var(--text-muted)',textTransform:'uppercase',letterSpacing:'0.1em',marginBottom:24}}>{metrics.multiProver.totalProvers}-Prover Verification</h2>
          <p style={{color:'var(--text-secondary)',marginBottom:32}}>
            {fmt(metrics.multiProver.tripleProverTheorems)} core theorems independently proved across {metrics.multiProver.totalProvers} verification tools using different mathematical
            foundations. {metrics.multiProver.sorry} sorry. {metrics.proofs.admitted} admitted. {metrics.proofs.axioms} justified policy axiom. If the same theorem
            is proved in multiple independent systems, the probability of a shared prover bug is virtually zero.
          </p>
          {[
            { prover: metrics.coq.prover, theorems: `${fmt(metrics.proofs.qedActive)} Qed`, role: 'Primary — authoritative proofs (CIC)' },
            { prover: metrics.lean.prover, theorems: `${fmt(metrics.lean.theorems)} theorems`, role: 'Secondary — independent port (DTT)' },
            { prover: metrics.isabelle.prover, theorems: `${fmt(metrics.isabelle.lemmas)} lemmas`, role: 'Tertiary — third verification (HOL)' },
            { prover: (metrics.fstar || {}).prover || 'F*', theorems: `${fmt((metrics.fstar || {}).lemmas || 0)} lemmas`, role: 'Dependent types (DTT)' },
            { prover: (metrics.tlaplus || {}).prover || 'TLA+', theorems: `${fmt((metrics.tlaplus || {}).theorems || 0)} theorems`, role: 'Model checking (TLA)' },
            { prover: (metrics.alloy || {}).prover || 'Alloy 6', theorems: `${fmt((metrics.alloy || {}).assertions || 0)} assertions`, role: 'Relational logic (FOL)' },
            { prover: (metrics.smt || {}).prover || 'Z3/CVC5', theorems: `${fmt((metrics.smt || {}).assertions || 0)} assertions`, role: 'SMT solving (SMT-LIB)' },
            { prover: (metrics.verus || {}).prover || 'Verus', theorems: `${fmt((metrics.verus || {}).proofs || 0)} proofs`, role: 'Rust verification (VIR)' },
            { prover: (metrics.kani || {}).prover || 'Kani', theorems: `${fmt((metrics.kani || {}).harnesses || 0)} harnesses`, role: 'Model checking (CBMC)' },
            { prover: (metrics.tv || {}).prover || 'Translation Validation', theorems: `${fmt((metrics.tv || {}).validations || 0)} validations`, role: 'Binary equivalence (TV)' },
          ].map((p, i) => (
            <div key={i} className="cli-row">
              <code style={{minWidth:140}}>{p.prover}</code>
              <span style={{minWidth:80}}>{p.theorems}</span>
              <span>{p.role}</span>
            </div>
          ))}
        </div>
      </section>

      <section style={{padding:'80px 24px'}}>
        <div style={{maxWidth:'var(--max-w-page)',margin:'0 auto'}}>
          <h2 style={{fontSize:12,fontFamily:'var(--font-mono)',color:'var(--text-muted)',textTransform:'uppercase',letterSpacing:'0.1em',marginBottom:24}}>26 Research Domains</h2>
          {[
            { id: 'A', name: 'Core Type Theory', desc: 'Type safety, non-interference, logical relations' },
            { id: 'B', name: 'Compiler & Prototype', desc: `${metrics.rust.crates} Rust crates, ${metrics.rust.tests} tests` },
            { id: 'C', name: 'Language Specifications', desc: 'Grammar, AST, type system spec' },
            { id: 'D-Q', name: 'Attack Surface Research', desc: `14 domains, ${metrics.status.threats} threats enumerated` },
            { id: 'R', name: 'Certified Compilation', desc: 'Translation validation' },
            { id: 'S', name: 'Hardware Contracts', desc: 'CPU side-channel models' },
            { id: 'T', name: 'Hermetic Bootstrap', desc: 'Binary bootstrap from hex0' },
            { id: 'U', name: 'Runtime Guardian', desc: 'Verified micro-hypervisor' },
            { id: 'V', name: 'Termination Guarantees', desc: 'Sized types, strong normalization' },
            { id: 'W', name: 'Verified Memory', desc: 'Separation logic, verified allocator' },
            { id: 'X', name: 'Concurrency Model', desc: 'Session types, data-race freedom' },
            { id: 'Y', name: 'Verified Stdlib', desc: 'Every stdlib function proven correct' },
            { id: 'Z', name: 'Declassification Policy', desc: 'Robust declassification with budgets' },
          ].map((d, i) => (
            <div key={i} className="domain-row">
              <span className="domain-row__id">{d.id}</span>
              <span className="domain-row__name">{d.name}</span>
              <span className="domain-row__desc">{d.desc}</span>
            </div>
          ))}
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // LEGAL PAGE — Tabs: License, Privacy, Terms
  // ============================================================================
  const LegalPage = () => {
    const [tab, setTab] = useState('license');

    return (
      <div>
        <section className="section--sm">
          <div className="container--narrow">
            <h1 style={{fontSize:40,fontWeight:300,marginBottom:16}}>Legal</h1>
          </div>
        </section>

        <section style={{padding:'0 24px 80px'}}>
          <div style={{maxWidth:'var(--max-w-text)',margin:'0 auto'}}>
            <div className="tabs">
              {[['license','License'],['privacy','Privacy'],['terms','Terms']].map(([id,label]) => (
                <button key={id} onClick={() => setTab(id)} className={`tab-btn${tab === id ? ' tab-btn--active' : ''}`}>{label}</button>
              ))}
            </div>

            {tab === 'license' && (
              <div>
                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>Proprietary</h2>
                <p style={{color:'var(--text-secondary)',lineHeight:1.8,marginBottom:24}}>
                  RIINA is licensed under the RIINA Proprietary License with the "Incompatible With Secondary Licenses"
                  notice. This means the code cannot be relicensed under GPL, AGPL, or LGPL.
                </p>
                <div style={{display:'grid',gridTemplateColumns:'repeat(3,1fr)',gap:16,marginBottom:24}}>
                  <div className="card">
                    <div style={{fontSize:12,color:'var(--text-string)',fontFamily:'var(--font-mono)',marginBottom:8}}>PERMISSIONS</div>
                    <div style={{fontSize:13,color:'var(--text-secondary)',lineHeight:2}}>
                      Commercial use<br/>Modification<br/>Distribution<br/>Patent use<br/>Private use
                    </div>
                  </div>
                  <div className="card">
                    <div style={{fontSize:12,color:'#fbbf24',fontFamily:'var(--font-mono)',marginBottom:8}}>CONDITIONS</div>
                    <div style={{fontSize:13,color:'var(--text-secondary)',lineHeight:2}}>
                      Disclose source (file-level)<br/>Same license for modified files<br/>Copyright notice preserved
                    </div>
                  </div>
                  <div className="card">
                    <div style={{fontSize:12,color:'#f87171',fontFamily:'var(--font-mono)',marginBottom:8}}>LIMITATIONS</div>
                    <div style={{fontSize:13,color:'var(--text-secondary)',lineHeight:2}}>
                      No liability<br/>No warranty<br/>No trademark rights
                    </div>
                  </div>
                </div>
                <a href="https://github.com/ib823/riina/blob/main/LICENSE">Read full LICENSE on GitHub</a>
              </div>
            )}

            {tab === 'privacy' && (
              <div>
                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>No data collection</h2>
                <div style={{fontSize:14,color:'var(--text-secondary)',lineHeight:2}}>
                  {[
                    'This is a static website. No server-side processing.',
                    'No cookies are set or read.',
                    'No analytics or tracking scripts.',
                    'No user data is collected, stored, or transmitted.',
                    'No third-party services are loaded.',
                    'The RIINA compiler does not phone home or collect telemetry.',
                  ].map((item, i) => <div key={i}>{item}</div>)}
                </div>
              </div>
            )}

            {tab === 'terms' && (
              <div style={{fontSize:14,color:'var(--text-secondary)',lineHeight:1.8}}>
                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16,color:'var(--text-primary)'}}>Software License</h2>
                <p style={{marginBottom:24}}>RIINA is distributed under the RIINA Proprietary License (Proprietary).</p>
                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16,color:'var(--text-primary)'}}>No Warranty</h2>
                <p style={{marginBottom:24}}>
                  Covered Software is provided under this License on an "as is" basis, without warranty
                  of any kind, either expressed, implied, or statutory.
                </p>
                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16,color:'var(--text-primary)'}}>Limitation of Liability</h2>
                <p>
                  Under no circumstances and under no legal theory shall any Contributor be liable for any
                  direct, indirect, special, incidental, or consequential damages.
                </p>
              </div>
            )}
          </div>
        </section>
      </div>
    );
  };

  // ============================================================================
  // FOOTER
  // ============================================================================
  const Footer = () => (
    <footer className="site-footer">
      <div className="footer-inner">
        <div>
          <div className="footer-brand">
            <Logo size={20} />
            <span className="footer-brand__name">RIINA</span>
          </div>
          <p className="footer-brand__tagline">Rigorous Immutable Invariant,<br/>No Assumptions</p>
        </div>

        {[
          { title: 'Product', links: [['Home','home'],['Language','language'],['Playground','playground'],['Enterprise','enterprise']] },
          { title: 'Learn', links: [['Docs','docs'],['How It Works','how'],['GitHub','https://github.com/ib823/riina']] },
          { title: 'Legal', links: [['License','legal'],['Privacy','legal'],['Terms','legal'],['Reach Us','https://t.me/ib823']] },
        ].map((col, i) => (
          <div key={i} className="footer-col">
            <div className="footer-col__title">{col.title}</div>
            {col.links.map(([label, target], j) => (
              target.startsWith('http') ?
                <a key={j} href={target}>{label}</a> :
                <button key={j} onClick={() => nav(target)}>{label}</button>
            ))}
          </div>
        ))}
      </div>

      <div className="footer-bottom">
        <span>&copy; 2026 RIINA</span>
        <div className="footer-status">
          <span className="footer-dot" /> Build passing &middot; v{metrics.version} &middot; Proprietary
        </div>
      </div>
    </footer>
  );

  // ============================================================================
  // RENDER
  // ============================================================================
  const renderPage = () => {
    switch (currentPage) {
      case 'language': return <LanguagePage />;
      case 'playground': return <PlaygroundPage onNavigate={nav} />;
      case 'docs': return <DocsPage />;
      case 'enterprise': return <EnterprisePage />;
      case 'how': return <HowPage />;
      case 'legal': return <LegalPage />;
      default: return <HomePage />;
    }
  };

  return (
    <div className="app-root">
      <Header />
      <main className="main-content">
        {renderPage()}
      </main>
      <Footer />
    </div>
  );
};

export default RiinaWebsite;
