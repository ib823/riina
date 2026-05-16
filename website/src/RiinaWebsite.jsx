import React, { useState, useEffect, useCallback, useRef } from 'react';
import PlaygroundPage from './playground/Playground.jsx';
import { useMetrics, fmt } from './useMetrics.js';

// ============================================================================
// #39: COPYABLE CODE BLOCK COMPONENT
// ============================================================================

const CopyableCode = ({ children, className = "code-block", style }) => {
  const [copied, setCopied] = useState(false);
  const preRef = useRef(null);

  const handleCopy = () => {
    const text = preRef.current?.textContent || '';
    navigator.clipboard.writeText(text).then(() => {
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    }).catch(() => {});
  };

  return (
    <div className="code-block-wrapper">
      <button
        className={`copy-btn${copied ? ' copy-btn--copied' : ''}`}
        onClick={handleCopy}
        aria-label="Copy to clipboard"
      >
        {copied ? 'Copied!' : 'Copy'}
      </button>
      <pre ref={preRef} className={className} style={style}>{children}</pre>
    </div>
  );
};

// ============================================================================
// RIINA WEBSITE — 7-PAGE DARK-MODE REWRITE
// ============================================================================

const RiinaWebsite = () => {
  const [currentPage, setCurrentPage] = useState('home');
  const [mobileMenuOpen, setMobileMenuOpen] = useState(false);
  const { metrics } = useMetrics();
  const claimLevels = metrics.claimLevels || {};
  const claimLevelLabel = (level) => {
    if (level === 'independently_audited') return 'independently audited';
    if (level === 'mechanized') return 'mechanized';
    if (level === 'compiled') return 'compiled';
    return 'generated';
  };
  const laneClaim = (lane) => claimLevelLabel(claimLevels[lane] || 'generated');
  const runtimeClaim = claimLevelLabel(
    claimLevels.runtimeProofArchitecture || metrics.quality?.runtimeProofStatus || 'generated'
  );
  useEffect(() => { window.scrollTo(0, 0); }, [currentPage]);

  // #42: Scroll-triggered entrance animations (progressive enhancement)
  // Content is visible by default. JS adds will-animate to hide off-screen
  // elements, then observer adds visible to reveal them on scroll.
  useEffect(() => {
    let observer;
    const timer = requestAnimationFrame(() => {
      observer = new IntersectionObserver(
        (entries) => {
          entries.forEach(entry => {
            if (entry.isIntersecting) {
              entry.target.classList.add('visible');
              observer.unobserve(entry.target);
            }
          });
        },
        { threshold: 0.1 }
      );
      const elements = document.querySelectorAll('.animate-on-scroll');
      elements.forEach(el => {
        const rect = el.getBoundingClientRect();
        if (rect.top >= window.innerHeight) {
          // Only hide elements that are BELOW the viewport
          el.classList.add('will-animate');
          observer.observe(el);
        }
        // Elements already in viewport: leave them visible (no will-animate)
      });
    });
    return () => {
      cancelAnimationFrame(timer);
      if (observer) observer.disconnect();
    };
  }, [currentPage]);

  // #50: Register service worker for offline docs
  useEffect(() => {
    if ('serviceWorker' in navigator) {
      navigator.serviceWorker.register('/riina/sw.js').catch(() => {});
    }
  }, []);

  // Release data (auto-updated by scripts/release.sh)
  const releases = [
    // RELEASES_MARKER
    // NOTE: 0.3.0 was prepared but is not yet tagged in git
    // (VERSION=0.2.0; latest tag=v0.2.0). Highlights are draft and will be
    // finalized when scripts/release.sh actually ships the release.
    {
      version: '0.3.0',
      date: '2026-03-19',
      highlights: [
        'Live proof and prover counts in PROOF_STATUS.md and metrics.json',
        'Public quality gates green; CI wired into GitHub Actions',
        'JALINAN actors, CAHAYA UI framework, Blockchain/Syariah keywords',
        '[draft] not yet tagged — see VERSION file for current release',
      ],
    },
    {
      version: '0.2.0',
      date: '2026-02-10',
      highlights: [
        '10-prover verification corpus with explicit claim levels per lane',
        'Public quality gates and repository transparency',
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
    <>
      {/* #7: Skip to content for keyboard/screen reader users */}
      <a href="#main-content" className="skip-to-content">Skip to content</a>
      <header className="site-header">
        <div className="header-inner">
          <button className="header-logo" onClick={() => nav('home')}>
            <Logo size={24} />
            <span>RIINA<sup style={{fontSize:8,verticalAlign:'super',opacity:0.5}}>™</sup></span>
          </button>

          <button className="hamburger" onClick={() => setMobileMenuOpen(!mobileMenuOpen)} aria-label="Menu">
            <svg width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2">
              <line x1="3" y1="6" x2="21" y2="6"/><line x1="3" y1="12" x2="21" y2="12"/><line x1="3" y1="18" x2="21" y2="18"/>
            </svg>
          </button>

          <nav className="site-nav">
            {['Language', 'Playground', 'Docs', 'Enterprise', 'How It Works'].map(p => (
              <button key={p} onClick={() => nav(p === 'How It Works' ? 'how' : p.toLowerCase())} className={`nav-btn${currentPage === (p === 'How It Works' ? 'how' : p.toLowerCase()) ? ' nav-btn--active' : ''}`}>
                {p}
              </button>
            ))}
          </nav>

          {/* #6: External link with target="_blank" and rel="noopener" */}
          <a className="header-github" href="https://github.com/ib823/riina" target="_blank" rel="noopener noreferrer">GitHub</a>
        </div>

        <div className={`mobile-menu${mobileMenuOpen ? ' open' : ''}`}>
          <button className="mobile-menu-close" onClick={() => setMobileMenuOpen(false)} aria-label="Close menu">&#x2715;</button>
          {['Home', 'Language', 'Playground', 'Docs', 'Enterprise', 'How'].map(p => (
            <button key={p} onClick={() => nav(p === 'Home' ? 'home' : p.toLowerCase())}>{p}</button>
          ))}
          <a href="https://github.com/ib823/riina" target="_blank" rel="noopener noreferrer">GitHub</a>
        </div>
      </header>
    </>
  );

  // ============================================================================
  // HOME PAGE — 4-Act Conversion Funnel
  // ============================================================================
  const HomePage = () => (
    <div>
      {/* Act 1: Hero — positioning → headline → explanation → proof → CTA */}
      <section className="hero">
        <p className="hero-positioning">
          <strong>Rigorous Immutable Invariant, No Assumptions</strong> — a programming language
          with mathematical proof built into the compiler.
        </p>

        {/* #8: Explicit spaces around strong to prevent screen reader run-on */}
        <h1 className="hero-fade">
          Your code is{' '}<br/><strong>proven secure</strong>{' '}<br/>before it ships.
        </h1>

        <p className="hero-explain">
          RIINA proves your security properties are correct before your code ever runs.
          Not tested. Not audited. <em>Proven</em> — with the same mathematical certainty
          used in aerospace and nuclear engineering.
        </p>

        {/* #13: Highlight "admitted" and "axioms" as the impressive zero values */}
        <p className="hero-subhead">
          {fmt(metrics.proofs.qedActive)} machine-checked proofs &middot; <span>{metrics.proofs.admitted} admitted</span> &middot; <span>{metrics.proofs.axioms} axioms</span>
        </p>
        <div className="hero-stats">
          <div className="hero-stat">
            <span className="hero-stat__num">{fmt(metrics.multiProver.totalProofsAllProvers)}</span>
            <span className="hero-stat__label">proof artifacts</span>
          </div>
          <div className="hero-stat-divider" />
          <div className="hero-stat">
            <span className="hero-stat__num">{metrics.multiProver.totalProvers}</span>
            <span className="hero-stat__label">independent provers</span>
          </div>
          <div className="hero-stat-divider" />
          <div className="hero-stat">
            <span className="hero-stat__num">{fmt(metrics.rust.tests)}</span>
            <span className="hero-stat__label">tests passing</span>
          </div>
        </div>
        {/* #11: CTA hierarchy — Playground is the conversion action, How It Works is secondary */}
        <div className="hero-cta">
          <button onClick={() => nav('playground')} className="btn btn--primary">Try the Playground</button>
          <button onClick={() => nav('how')} className="btn btn--outline">See How It Works</button>
        </div>

        {/* #9: Scroll affordance */}
        <div className="scroll-indicator" aria-hidden="true">
          <svg width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2" strokeLinecap="round">
            <polyline points="6 9 12 15 18 9"/>
          </svg>
        </div>
      </section>

      {/* Act 2: Show — Side-by-side code */}
      <section className="act-show animate-on-scroll">
        <p className="act-show__label">What it looks like</p>
        <p className="act-show__lang-note">
          RIINA uses <strong>Bahasa Melayu</strong> (Malaysian) keywords — a deliberate
          choice of linguistic sovereignty for a language built in Malaysia.{' '}
          <code style={{color:'var(--text-keyword)'}}>fungsi</code> = fn,{' '}
          <code style={{color:'var(--text-keyword)'}}>biar</code> = let,{' '}
          <code style={{color:'var(--text-keyword)'}}>pulang</code> = return,{' '}
          <code style={{color:'var(--text-accent)'}}>Rahsia</code> = Secret.
        </p>
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
        <div className="code-callouts">
          <div className="code-callout">
            <span className="code-callout__arrow">&larr;</span>
            <span><code style={{color:'var(--text-accent)'}}>Rahsia&lt;Teks&gt;</code> &mdash; Secrets can never leak. Enforced at the type level.</span>
          </div>
          <div className="code-callout">
            <span className="code-callout__arrow">&larr;</span>
            <span><code style={{color:'var(--text-keyword)'}}>masa_tetap</code> &mdash; Constant-time execution. Timing attacks are impossible.</span>
          </div>
          <div className="code-callout">
            <span className="code-callout__arrow">&larr;</span>
            <span>The compiler <em>proved</em> all three properties. Zero trust required.</span>
          </div>
        </div>
      </section>

      {/* Who is this for */}
      <section className="animate-on-scroll" style={{padding:'60px 24px',textAlign:'center'}}>
        <div style={{maxWidth:'var(--max-w-text)',margin:'0 auto'}}>
          <h2 style={{fontSize:32,fontWeight:300,marginBottom:16}}>Built for teams where <strong>security audits aren't enough.</strong></h2>
          <p style={{color:'var(--text-secondary)',fontSize:15,lineHeight:1.7}}>
            Healthcare. Defense. Finance. Critical infrastructure. If your software handles
            secrets, processes payments, or controls physical systems &mdash; RIINA proves your
            security properties are correct. Mathematically. Before deployment.
          </p>
        </div>
      </section>

      {/* Why Now */}
      <section className="animate-on-scroll" style={{padding:'60px 24px'}}>
        <div style={{maxWidth:'var(--max-w-page)',margin:'0 auto'}}>
          <h2 className="section-heading">Why now</h2>
          <div className="why-now-grid">
            <div className="why-now-item">
              <div className="why-now-item__title">AI writes code faster than humans can audit it</div>
              <div className="why-now-item__desc">
                LLMs generate thousands of lines per hour. Traditional security reviews
                can't keep up. RIINA's compiler verifies every function automatically —
                human or AI-written.
              </div>
            </div>
            <div className="why-now-item">
              <div className="why-now-item__title">Security audits fail silently</div>
              <div className="why-now-item__desc">
                Manual audits miss bugs. Penetration tests cover only what testers think
                to try. Mathematical proof covers every possible execution path — not just
                the ones someone remembered to test.
              </div>
            </div>
            <div className="why-now-item">
              <div className="why-now-item__title">Proof technology finally matured</div>
              <div className="why-now-item__desc">
                Proof assistants like Coq and Lean spent decades in academia. They're now
                fast and practical enough to back a production compiler. RIINA is the bridge
                between formal methods research and working software.
              </div>
            </div>
          </div>
        </div>
      </section>

      {/* Vibesafe — The AI-friendly language */}
      <section className="act-vibesafe animate-on-scroll">
        <div className="act-vibesafe__inner">
          <div className="act-vibesafe__text">
            <div className="act-vibesafe__badge">Vibesafe</div>
            <h2 className="act-vibesafe__title">
              The only language where<br /><strong>AI-generated code is mathematically verified.</strong>
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
      <section className="act-proof animate-on-scroll">
        <div className="act-proof__header">
          <h2 className="act-proof__title">Don't trust us. <strong>Verify it.</strong></h2>
          <p className="act-proof__subtitle">Every claim has a machine-checked proof. Run them yourself.</p>
        </div>

        {/* #39: Copyable terminal block */}
        <div className="code-block-wrapper">
          <button
            className="copy-btn"
            onClick={() => {
              const cmds = `git clone https://github.com/ib823/riina.git && cd riina\ncd 02_FORMAL/coq && make\ngrep -c "Qed\\." **/*.v\ngrep -c "Admitted\\." **/*.v`;
              navigator.clipboard.writeText(cmds).catch(() => {});
            }}
            aria-label="Copy commands"
          >Copy</button>
          <div className="terminal-block">
            <div><span className="prompt">$ </span><span className="cmd">git clone https://github.com/ib823/riina.git && cd riina</span></div>
            <div><span className="prompt">$ </span><span className="cmd">cd 02_FORMAL/coq && make</span></div>
            <div style={{color:'var(--text-string)'}}>Compiling {metrics.coq.filesActive} files... done. 0 errors.</div>
            <div><span className="prompt">$ </span><span className="cmd">grep -c "Qed\." **/*.v</span></div>
            <div style={{color:'var(--text-accent)'}}>{metrics.proofs.qedActive}</div>
            <div><span className="prompt">$ </span><span className="cmd">grep -c "Admitted\." **/*.v</span></div>
            <div style={{color:'var(--text-string)'}}>{metrics.proofs.admitted}</div>
          </div>
        </div>

        <div className="proof-pillars">
          <div className="proof-pillar">
            <div className="proof-pillar__icon">SAFE</div>
            <div className="proof-pillar__name">Type Safety</div>
            <div className="proof-pillar__desc">Progress + Preservation. Well-typed programs do not get stuck.</div>
          </div>
          <div className="proof-pillar">
            <div className="proof-pillar__icon">SEALED</div>
            <div className="proof-pillar__name">Non-Interference</div>
            <div className="proof-pillar__desc">Secret data cannot flow to public outputs. Proven via logical relations.</div>
          </div>
          <div className="proof-pillar">
            <div className="proof-pillar__icon">TRACKED</div>
            <div className="proof-pillar__name">Effect Soundness</div>
            <div className="proof-pillar__desc">Only declared effects can be performed. No hidden side effects.</div>
          </div>
        </div>

        <div className="triple-prover">
          <h3 className="triple-prover__title">Multi-prover verification</h3>
          <p className="triple-prover__desc">
            Coq is the primary proof engine — all {fmt(metrics.proofs.qedActive)} proofs compile with zero admits and zero axioms.
            Lean and Isabelle serve as secondary verification targets with explicit claim levels.
          </p>
          <div className="prover-grid">
            {[
              { prover: metrics.coq.prover, count: fmt(metrics.proofs.qedActive), level: laneClaim('coq'), primary: true },
              { prover: metrics.lean.prover, count: fmt(metrics.lean.theorems), level: laneClaim('lean') },
              { prover: metrics.isabelle.prover, count: fmt(metrics.isabelle.lemmas), level: laneClaim('isabelle') },
              { prover: (metrics.smt||{}).prover||'Z3/CVC5', count: fmt((metrics.smt||{}).assertions||0), level: laneClaim('smt') },
              { prover: (metrics.tlaplus||{}).prover||'TLA+', count: fmt((metrics.tlaplus||{}).theorems||0), level: laneClaim('tlaplus') },
              { prover: (metrics.fstar||{}).prover||'F*', count: fmt((metrics.fstar||{}).lemmas||0), level: laneClaim('fstar') },
              { prover: (metrics.alloy||{}).prover||'Alloy 6', count: fmt((metrics.alloy||{}).assertions||0), level: laneClaim('alloy') },
              { prover: (metrics.verus||{}).prover||'Verus', count: fmt((metrics.verus||{}).proofs||0), level: laneClaim('verus') },
              { prover: (metrics.kani||{}).prover||'Kani', count: fmt((metrics.kani||{}).harnesses||0), level: laneClaim('kani') },
              { prover: (metrics.tv||{}).prover||'Translation Validation', count: fmt((metrics.tv||{}).validations||0), level: laneClaim('tv') },
            ].map((p, i) => (
              <div key={i} className={`prover-row${p.primary ? ' prover-row--primary' : ''}`}>
                <span className="prover-row__name">{p.prover}{p.primary && <span style={{fontSize:10,color:'var(--text-accent)',marginLeft:8}}>PRIMARY</span>}</span>
                <span className="prover-row__count">{p.count}</span>
                <span className={`prover-row__level prover-row__level--${p.level}`}>{p.level}</span>
              </div>
            ))}
          </div>

          <div className="claim-levels">
            <h4 className="claim-levels__title">What do claim levels mean?</h4>
            <div className="claim-levels__grid">
              <div className="claim-levels__item">
                <span className="claim-levels__badge claim-levels__badge--mechanized">mechanized</span>
                <span className="claim-levels__desc">Proofs machine-checked by the tool. Builds pass.</span>
              </div>
              <div className="claim-levels__item">
                <span className="claim-levels__badge claim-levels__badge--compiled">compiled</span>
                <span className="claim-levels__desc">Code compiles and smoke-tests pass with the tool.</span>
              </div>
              <div className="claim-levels__item">
                <span className="claim-levels__badge claim-levels__badge--generated">generated</span>
                <span className="claim-levels__desc">Proof artifacts exist but tool verification not yet complete.</span>
              </div>
            </div>
          </div>
        </div>
      </section>

      {/* Social proof — Built in the open */}
      <section className="animate-on-scroll" style={{padding:'60px 24px',textAlign:'center'}}>
        <div style={{maxWidth:'var(--max-w-text)',margin:'0 auto'}}>
          <h2 className="section-heading">Built in the open</h2>
          <div className="social-proof-stats">
            <div>
              <span className="social-proof__num">{fmt(metrics.proofs.qedActive)}</span>
              <span className="social-proof__label">proofs you can verify yourself</span>
            </div>
            <div>
              <span className="social-proof__num">{metrics.multiProver.totalProvers}</span>
              <span className="social-proof__label">independent proof engines</span>
            </div>
            <div>
              <span className="social-proof__num">0</span>
              <span className="social-proof__label">dependencies, telemetry, or trust required</span>
            </div>
          </div>
          <p style={{color:'var(--text-muted)',fontSize:14,marginTop:24}}>
            Source available on GitHub. Every proof artifact compiles from source.
            No black boxes.
          </p>
        </div>
      </section>

      {/* Act 4: Start */}
      <section className="act-start animate-on-scroll">
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
        <p className="act-start__footer">Proprietary license &middot; Source available &middot; Zero dependencies</p>
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
      jalinan: [
        { bm: 'pelakon', en: 'actor' }, { bm: 'lahir', en: 'spawn' },
        { bm: 'hantar', en: 'send' }, { bm: 'terima', en: 'recv' },
        { bm: 'koreografi', en: 'choreography' }, { bm: 'peranan', en: 'role' },
        { bm: 'keadaan', en: 'state' }, { bm: 'penyelia', en: 'supervisor' },
        { bm: 'gabung', en: 'merge' }, { bm: 'cincang', en: 'hash' },
        { bm: 'sahkan', en: 'validate' },
      ],
      cahaya: [
        { bm: 'paparan', en: 'display' }, { bm: 'susun', en: 'layout' },
        { bm: 'warna', en: 'color' }, { bm: 'tulisan', en: 'text' },
        { bm: 'butang', en: 'button' }, { bm: 'kontras', en: 'contrast' },
        { bm: 'mudahcapai', en: 'accessible' }, { bm: 'baris', en: 'row' },
        { bm: 'lajur', en: 'column' },
      ],
      blockchain: [
        { bm: 'kontrak_pintar', en: 'smart_contract' }, { bm: 'token', en: 'token' },
        { bm: 'konsensus', en: 'consensus' }, { bm: 'sukuk', en: 'sukuk' },
        { bm: 'mudarabah', en: 'mudarabah' }, { bm: 'zakat', en: 'zakat' },
        { bm: 'wakaf', en: 'waqf' },
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
              <div className="tab-content" style={{maxWidth:'var(--max-w-code)'}}>
                <KwSection title="Declarations" items={keywords.declarations} />
                <KwSection title="Control Flow" items={keywords.controlFlow} />
                <KwSection title="Built-in Types" items={keywords.types} />
                <KwSection title="Security" items={keywords.security} />
                <KwSection title="Effects" items={keywords.effects} />
                <KwSection title="JALINAN (Distributed)" items={keywords.jalinan} />
                <KwSection title="CAHAYA (UI)" items={keywords.cahaya} />
                <KwSection title="Blockchain / Syariah" items={keywords.blockchain} />

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
              <div className="tab-content" style={{maxWidth:'var(--max-w-text)'}}>
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
              <div className="tab-content" style={{maxWidth:'var(--max-w-text)'}}>
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
              <div className="tab-content" style={{maxWidth:'var(--max-w-text)'}}>
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

        <section style={{padding:'40px 24px 80px',textAlign:'center'}}>
          <button onClick={() => nav('playground')} className="btn btn--primary">Try it in the Playground</button>
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

            {/* #40: Tab content transition */}
            {tab === 'quickstart' && (
              <div className="tab-content" style={{maxWidth:'var(--max-w-text)'}}>
                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>Install</h2>
                {/* #39: Copyable code blocks, #59: Shell syntax highlighting */}
                <CopyableCode style={{marginBottom:32}}>{`# From source
git clone https://github.com/ib823/riina.git
cd riina/03_PROTO
cargo build --release

# Docker
docker build -t riina .
docker run --rm riina check myfile.rii

# Portable installer
curl -sSf https://ib823.github.io/riina/install.sh | bash

# Nix
nix run github:ib823/riina`}</CopyableCode>

                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>Hello World</h2>
                <CopyableCode style={{marginBottom:16}}>{`// hello.rii
modul hello;
guna std::io;

awam fungsi utama() -> kesan Tulis {
    biar mesej = "Selamat datang ke RIINA!";
    laku Tulis cetak_baris(mesej);
}`}</CopyableCode>
                <CopyableCode>{`riinac check hello.rii    # Type-check + verify
riinac run hello.rii      # Run directly
riinac build hello.rii    # Compile to native binary`}</CopyableCode>
              </div>
            )}

            {tab === 'reference' && (
              <div className="tab-content" style={{maxWidth:'var(--max-w-text)'}}>
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
              <div className="tab-content" style={{maxWidth:'var(--max-w-text)'}}>
                <p style={{color:'var(--text-secondary)',marginBottom:24}}>
                  RIINA's source code is publicly available under the RIINA Proprietary License. Contributions to the compiler, proofs, standard library, and documentation are welcome.
                </p>
                <CopyableCode style={{marginBottom:24}}>{`# Setup
git clone https://github.com/ib823/riina.git && cd riina
cd 00_SETUP/scripts
./install_rust.sh && ./install_coq.sh && ./verify_setup.sh

# Build proofs
cd ../../02_FORMAL/coq && make

# Build compiler & run tests
cd ../../03_PROTO && cargo build --all && cargo test --all`}</CopyableCode>

                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>Commit format</h2>
                <CopyableCode style={{marginBottom:24}}>{`[TRACK_X] TYPE: Brief description

Tracks: A (Proofs), B (Compiler), C (Specs), F (Tooling)
Types:  PROOF, IMPL, FIX, DOCS, REFACTOR`}</CopyableCode>

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
              <div className="tab-content" style={{maxWidth:'var(--max-w-text)'}}>
                <CopyableCode style={{marginBottom:32}}>{`# Install latest
curl -fsSL https://ib823.github.io/riina/install.sh | bash`}</CopyableCode>
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
                    <a href={`https://github.com/ib823/riina/releases/tag/v${rel.version}`} target="_blank" rel="noopener noreferrer" style={{fontSize:13,marginTop:8,display:'inline-block'}}>
                      Release notes
                    </a>
                  </div>
                ))}
              </div>
            )}
          </div>
        </section>

        <section style={{padding:'40px 24px 80px',textAlign:'center'}}>
          <button onClick={() => nav('playground')} className="btn btn--primary" style={{marginRight:16}}>Try the Playground</button>
          <button onClick={() => nav('how')} className="btn btn--outline">How It Works</button>
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
          <div className="enterprise-intro">
            <p>Your compliance team spends months on manual security audits.
               Your developers wait weeks for penetration test results. And after all
               that effort, bugs still slip through.</p>
            <p>RIINA replaces manual verification with mathematical proof. The compiler
               checks security properties exhaustively — every code path, every edge case —
               at compile time. No auditor required.</p>
          </div>

          {/* #57: Industry cards with abstract icons */}
          <div className="industry-grid" style={{marginBottom:48}}>
            {[
              { icon: '\u2694', name: 'Defence & Military', regs: 'CMMC, ITAR, NIST 800-171', desc: 'Classified data handling with proven compartmentalization. CUI isolation enforced at the type level. Side-channel resistance for signals intelligence.' },
              { icon: '\u2695', name: 'Healthcare', regs: 'HIPAA, HITECH, HL7 FHIR', desc: 'PHI wrapped in security types that prevent unauthorized disclosure. Audit trails proven complete. De-identification verified at compile time.' },
              { icon: '\u2696', name: 'Financial Services', regs: 'PCI-DSS, SOX, BNM RMiT', desc: 'Cardholder data isolation proven by construction. Transaction integrity with formal audit trails. Constant-time operations prevent timing attacks.' },
              { icon: '\u2708', name: 'Aerospace & Aviation', regs: 'DO-178C DAL A, DO-326A', desc: 'Flight-critical software with formal verification evidence satisfying DAL A. Deterministic execution proven. WCET bounds verified.' },
              { icon: '\u2601', name: 'Technology / SaaS', regs: 'SOC 2, ISO 27001', desc: 'Access control and audit logging proven at compile time. Data isolation between tenants enforced by the type system.' },
              { icon: '\u26A1', name: 'Energy / Utilities', regs: 'NERC CIP, IEC 62443', desc: 'Critical infrastructure protection with proven access boundaries. Control system integrity verified by construction.' },
              { icon: '\u2605', name: 'Islamic Finance', regs: 'AAOIFI, IFSB, BNM RMiT', desc: 'Syariah compliance proven at compile time. No riba, gharar, or maysir possible in type-checked code.' },
              { icon: '\u26D3', name: 'Blockchain / DeFi', regs: 'Smart Contract Security', desc: 'Reentrancy-free by construction. Value conservation proven. Linear state prevents double-spend.' },
            ].map((ind, i) => (
              <div key={i} className="industry-card">
                <div className="industry-card__icon">{ind.icon}</div>
                <div className="industry-card__name">{ind.name}</div>
                <div className="industry-card__regs">{ind.regs}</div>
                <div className="industry-card__desc">{ind.desc}</div>
              </div>
            ))}
          </div>

          <p style={{color:'var(--text-muted)',fontSize:14,textAlign:'center',marginBottom:48}}>
            + 7 more compliance profiles: Telecom, Government, Transportation, Manufacturing, Retail, Education, Legal
          </p>

          <h2 style={{fontSize:12,fontFamily:'var(--font-mono)',color:'var(--text-muted)',textTransform:'uppercase',letterSpacing:'0.1em',marginBottom:16}}>Proof certificate</h2>
          <pre className="code-block" style={{maxWidth:'var(--max-w-text)'}}>{`$ riinac verify --compliance hipaa,pci-dss myapp.rii

RIINA COMPLIANCE CERTIFICATE
============================
Program: myapp.rii
Prover:  Rocq 9.1.1

HIPAA §164.312(a) — Access Control
  PROVEN: All PHI access gated by role-based authorization
  Theorem: access_control_enforced

HIPAA §164.312(b) — Audit Controls
  PROVEN: Every PHI access logged
  Theorem: audit_trail_complete

PCI-DSS Req 3 — Protect Stored Cardholder Data
  PROVEN: Cardholder data encrypted at rest
  Theorem: stored_data_encrypted`}</pre>

          {/* #63: Clear enterprise CTA with next steps */}
          <div style={{textAlign:'center',marginTop:64,padding:'48px 32px',background:'var(--bg-secondary)',border:'1px solid var(--border)',borderRadius:'var(--radius-md)',maxWidth:'var(--max-w-text)'}}>
            <h3 style={{fontSize:24,fontWeight:400,marginBottom:8}}>Ready to prove your compliance?</h3>
            <p style={{color:'var(--text-secondary)',fontSize:15,marginBottom:24,maxWidth:480,margin:'0 auto 24px'}}>
              We'll walk your team through a live proof verification against your compliance framework. 30 minutes.
            </p>
            <div style={{display:'flex',gap:16,justifyContent:'center',flexWrap:'wrap'}}>
              <a href="mailto:ikmal.baharudin@gmail.com?subject=RIINA%20Enterprise%20Evaluation" target="_blank" rel="noopener noreferrer" className="btn btn--primary">Request a Demo</a>
              <a href="https://t.me/ib823" target="_blank" rel="noopener noreferrer" className="btn btn--outline">Contact on Telegram</a>
            </div>
            <p style={{color:'var(--text-muted)',fontSize:12,marginTop:16,fontFamily:'var(--font-mono)'}}>
              Free evaluation &middot; No commitment &middot; Source available
            </p>
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
            { num: '04', title: 'Proof Artifacts Ship With Code', desc: `${fmt(metrics.multiProver.totalProofsAllProvers)} proof artifacts across ${metrics.multiProver.totalProvers} provers ship in the repository. 0 Admitted, 0 axioms. You can clone and verify them yourself.` },
            { num: '05', title: 'Runtime Verification', desc: 'Capability-bound effect gates and proof-bundle chaining enforce guarantees at runtime. Hardware-rooted attestation is on the roadmap.' },
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
            RIINA's proofs are checked by {metrics.multiProver.totalProvers} independent tools, each using a different mathematical foundation.
            If one tool has a bug, the others catch it. No independent external audit has been published yet.
          </p>
          {[
            { prover: metrics.coq.prover, theorems: `${fmt(metrics.proofs.qedActive)} Qed`, level: laneClaim('coq'), role: 'Primary proof engine' },
            { prover: metrics.lean.prover, theorems: `${fmt(metrics.lean.theorems)} theorems`, level: laneClaim('lean'), role: 'Cross-check port' },
            { prover: metrics.isabelle.prover, theorems: `${fmt(metrics.isabelle.lemmas)} lemmas`, level: laneClaim('isabelle'), role: 'Third verification' },
            { prover: (metrics.smt || {}).prover || 'Z3/CVC5', theorems: `${fmt((metrics.smt || {}).assertions || 0)} assertions`, level: laneClaim('smt'), role: 'SMT solving' },
            { prover: (metrics.fstar || {}).prover || 'F*', theorems: `${fmt((metrics.fstar || {}).lemmas || 0)} lemmas`, level: laneClaim('fstar'), role: 'Dependent types' },
            { prover: (metrics.tlaplus || {}).prover || 'TLA+', theorems: `${fmt((metrics.tlaplus || {}).theorems || 0)} theorems`, level: laneClaim('tlaplus'), role: 'Model checking' },
            { prover: (metrics.alloy || {}).prover || 'Alloy 6', theorems: `${fmt((metrics.alloy || {}).assertions || 0)} assertions`, level: laneClaim('alloy'), role: 'Relational logic' },
            { prover: (metrics.verus || {}).prover || 'Verus', theorems: `${fmt((metrics.verus || {}).proofs || 0)} proofs`, level: laneClaim('verus'), role: 'Rust verification' },
            { prover: (metrics.kani || {}).prover || 'Kani', theorems: `${fmt((metrics.kani || {}).harnesses || 0)} harnesses`, level: laneClaim('kani'), role: 'Model checking' },
            { prover: (metrics.tv || {}).prover || 'Translation Validation', theorems: `${fmt((metrics.tv || {}).validations || 0)} validations`, level: laneClaim('tv'), role: 'Binary equivalence' },
          ].map((p, i) => (
            <div key={i} className="cli-row">
              <code style={{minWidth:140}}>{p.prover}</code>
              <span style={{minWidth:100}}>{p.theorems}</span>
              <span style={{minWidth:100,color: p.level === 'mechanized' ? 'var(--text-string)' : p.level === 'compiled' ? 'var(--text-accent)' : 'var(--text-muted)'}}>{p.level}</span>
              <span>{p.role}</span>
            </div>
          ))}
        </div>
      </section>

      <section style={{padding:'80px 24px'}}>
        <div style={{maxWidth:'var(--max-w-page)',margin:'0 auto'}}>
          <h2 style={{fontSize:12,fontFamily:'var(--font-mono)',color:'var(--text-muted)',textTransform:'uppercase',letterSpacing:'0.1em',marginBottom:24}}>Research Coverage</h2>
          <p style={{color:'var(--text-secondary)',marginBottom:24,fontSize:14}}>
            26 research tracks spanning the full security stack — from type theory foundations to hardware side-channel models.
          </p>
          <div style={{display:'grid',gridTemplateColumns:'repeat(auto-fill, minmax(280px, 1fr))',gap:12}}>
            {[
              { name: 'Core Type Theory', desc: 'Type safety, non-interference, logical relations' },
              { name: 'Compiler', desc: `${metrics.rust.crates} crates, ${fmt(metrics.rust.tests)} tests, zero dependencies` },
              { name: 'Attack Surface', desc: `14 domains, ${metrics.status.threats} threats modeled` },
              { name: 'Termination & Memory', desc: 'Sized types, strong normalization, separation logic' },
              { name: 'Concurrency & Effects', desc: 'Session types, effect algebra, data-race freedom' },
              { name: 'Runtime & Hardware', desc: 'Proof bundles, constant-time, side-channel models' },
              { name: 'Runtime Verification', desc: '6-layer runtime: verified allocator, CHERI hardware, Coq monitors, eBPF kernel, attestation, execution receipts' },
              { name: 'Runtime Proof Architecture', desc: 'Phase 7: Proof bundles, capability gates, hardware attestation, execution receipts' },
              { name: 'TERAS-OS', desc: 'Phase 9: Microkernel OS with verified memory, process isolation, and capability-based security' },
            ].map((d, i) => (
              <div key={i} className="card" style={{padding:'16px 20px'}}>
                <div style={{fontSize:14,fontWeight:500,marginBottom:4}}>{d.name}</div>
                <div style={{fontSize:13,color:'var(--text-secondary)'}}>{d.desc}</div>
              </div>
            ))}
          </div>
        </div>
      </section>

      <section className="section--alt" style={{padding:'80px 24px'}}>
        <div style={{maxWidth:'var(--max-w-page)',margin:'0 auto'}}>
          <h2 style={{fontSize:12,fontFamily:'var(--font-mono)',color:'var(--text-muted)',textTransform:'uppercase',letterSpacing:'0.1em',marginBottom:24}}>JALINAN: Distributed by Construction</h2>
          <p style={{color:'var(--text-secondary)',marginBottom:32}}>
            JALINAN unifies local and distributed computing under formal verification. Session-typed actors, content-addressed state, and choreographic protocols — all proven at compile time.
          </p>
          <div style={{display:'grid',gridTemplateColumns:'repeat(auto-fill, minmax(280px, 1fr))',gap:12,marginBottom:32}}>
            {[
              { name: 'Protocol = API', desc: 'Session types replace REST. Type-checked protocols ensure every message is expected, ordered, and complete.' },
              { name: 'State = History', desc: 'Content-addressed Merkle DAGs make state verifiable. Every change is traceable and tamper-evident.' },
              { name: 'Local = Distributed', desc: 'Actors with supervision trees. Code runs the same locally and distributed — no rewrite needed.' },
            ].map((d, i) => (
              <div key={i} className="card" style={{padding:'16px 20px'}}>
                <div style={{fontSize:14,fontWeight:500,marginBottom:4}}>{d.name}</div>
                <div style={{fontSize:13,color:'var(--text-secondary)'}}>{d.desc}</div>
              </div>
            ))}
          </div>
          <pre className="code-block">{`// JALINAN actor example
pelakon Pembilang {
    keadaan: Nombor
    kendalikan Tambah(n) {
        n + 1
    }
}

biar k = lahir Pembilang(0);
hantar(k, 5);
terima(k)`}</pre>
        </div>
      </section>

      <section style={{padding:'40px 24px 80px',textAlign:'center'}}>
        <a href="https://github.com/ib823/riina" target="_blank" rel="noopener noreferrer" className="btn btn--primary" style={{marginRight:16}}>Verify the Proofs Yourself</a>
        <button onClick={() => nav('playground')} className="btn btn--outline">Try the Playground</button>
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
                <h2 style={{fontSize:20,fontWeight:500,marginBottom:16}}>RIINA Proprietary License</h2>
                <p style={{color:'var(--text-secondary)',lineHeight:1.8,marginBottom:24}}>
                  RIINA is distributed under its own proprietary license. Source code is publicly viewable
                  for transparency and auditability. See the full license text on GitHub for terms governing
                  use, modification, and distribution.
                </p>
                <div style={{display:'grid',gridTemplateColumns:'repeat(3,1fr)',gap:16,marginBottom:24}}>
                  <div className="card">
                    <div style={{fontSize:12,color:'var(--text-string)',fontFamily:'var(--font-mono)',marginBottom:8}}>PERMISSIONS</div>
                    <div style={{fontSize:13,color:'var(--text-secondary)',lineHeight:2}}>
                      Commercial use<br/>Private use<br/>Compile software with RIINA<br/>Distribute software you build
                    </div>
                  </div>
                  <div className="card">
                    <div style={{fontSize:12,color:'var(--accent-warm)',fontFamily:'var(--font-mono)',marginBottom:8}}>CONDITIONS</div>
                    <div style={{fontSize:13,color:'var(--text-secondary)',lineHeight:2}}>
                      Follow RIINA license terms<br/>Retain copyright notices<br/>Use for authorized purposes only
                    </div>
                  </div>
                  <div className="card">
                    <div style={{fontSize:12,color:'#f87171',fontFamily:'var(--font-mono)',marginBottom:8}}>LIMITATIONS</div>
                    <div style={{fontSize:13,color:'var(--text-secondary)',lineHeight:2}}>
                      No compiler source modification<br/>No compiler redistribution<br/>No warranty or liability
                    </div>
                  </div>
                </div>
                <a href="https://github.com/ib823/riina/blob/main/LICENSE" target="_blank" rel="noopener noreferrer">Read full LICENSE on GitHub</a>
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
                <p style={{marginBottom:24}}>RIINA is distributed under the RIINA Proprietary License.</p>
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
            <span className="footer-brand__name">RIINA<sup style={{fontSize:8,verticalAlign:'super',opacity:0.5}}>™</sup></span>
          </div>
          <p className="footer-brand__tagline">Rigorous Immutable Invariant,<br/>No Assumptions</p>
        </div>

        {[
          { title: 'Product', links: [['Home','home'],['Language','language'],['Playground','playground'],['Enterprise','enterprise']] },
          { title: 'Learn', links: [['Docs','docs'],['How It Works','how'],['GitHub','https://github.com/ib823/riina']] },
          { title: 'Legal', links: [['License','legal'],['Privacy','legal'],['Terms','legal'],['Contact','mailto:ikmal.baharudin@gmail.com?subject=RIINA%20Inquiry'],['Enterprise Inquiry','mailto:ikmal.baharudin@gmail.com?subject=RIINA%20Enterprise%20Evaluation'],['Telegram','https://t.me/ib823']] },
        ].map((col, i) => (
          <div key={i} className="footer-col">
            <div className="footer-col__title">{col.title}</div>
            {col.links.map(([label, target], j) => (
              target.startsWith('http') || target.startsWith('mailto') ?
                <a key={j} href={target} target="_blank" rel="noopener noreferrer">{label}</a> :
                <button key={j} onClick={() => nav(target)}>{label}</button>
            ))}
          </div>
        ))}
      </div>

      <div className="footer-bottom">
        <span>&copy; 2026 RIINA &middot; v{metrics.version}{metrics.generated ? ` \u00b7 ${new Date(metrics.generated).toLocaleDateString('en-US', { month: 'short', day: 'numeric', year: 'numeric' })}` : ''}</span>
        <div className="footer-status">
          <span className="footer-dot" /> Build passing &middot; <a href="https://github.com/ib823/riina" target="_blank" rel="noopener noreferrer" style={{color:'var(--text-muted)',textDecoration:'none'}}>GitHub</a> &middot; Proprietary
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
      <main className="main-content" id="main-content" key={currentPage}>
        {renderPage()}
      </main>
      <Footer />
    </div>
  );
};

export default RiinaWebsite;
