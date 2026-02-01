import React, { useState, useEffect } from 'react';
import PlaygroundPage from './playground/Playground.jsx';

// ============================================================================
// RIINA WEBSITE - COMPLETE IMPLEMENTATION (15 PAGES)
// ============================================================================

const RiinaWebsite = () => {
  const [currentPage, setCurrentPage] = useState('home');
  const [mobileMenuOpen, setMobileMenuOpen] = useState(false);

  // Scroll to top on page change
  useEffect(() => {
    window.scrollTo(0, 0);
  }, [currentPage]);

  // Navigation — all pages (used by mobile menu, footer, routing)
  const pages = [
    { id: 'home', label: 'Home' },
    { id: 'whyProof', label: 'Why Proof' },
    { id: 'language', label: 'Language' },
    { id: 'how', label: 'How It Works' },
    { id: 'demos', label: 'Demos' },
    { id: 'enterprise', label: 'Enterprise' },
    { id: 'releases', label: 'Releases' },
    { id: 'research', label: 'Research' },
    { id: 'docs', label: 'Documentation' },
    { id: 'bisik', label: 'Reach Us' },
    { id: 'playground', label: 'Playground' },
  ];

  // Header nav: direct links + dropdown groups (keeps header tidy)
  const headerNav = [
    { id: 'language', label: 'Language' },
    { id: 'playground', label: 'Playground' },
    { label: 'Learn', children: [
      { id: 'whyProof', label: 'Why Proof' },
      { id: 'how', label: 'How It Works' },
      { id: 'demos', label: 'Demos' },
      { id: 'research', label: 'Research' },
    ]},
    { id: 'enterprise', label: 'Enterprise' },
    { label: 'Docs', children: [
      { id: 'docs', label: 'Documentation' },
      { id: 'releases', label: 'Releases' },
      { id: 'bisik', label: 'Reach Us' },
    ]},
  ];

  const [openDropdown, setOpenDropdown] = useState(null);

  // Release data (auto-updated by scripts/release.sh)
  const releases = [
    // RELEASES_MARKER
    { version: '0.1.0', date: '2026-02-01', highlights: ['RIINA compiler with Bahasa Melayu syntax', 'Formal verification: 5,308 Qed proofs in Coq', 'Standard library: 88 builtins across 9 modules'] },
  ];

  // Footer link mapping
  const footerNav = (label) => {
    const map = {
      'Home': 'home',
      'Why Proof': 'whyProof',
      'Language': 'language',
      'How It Works': 'how',
      'Demos': 'demos',
      'Enterprise': 'enterprise',
      'Releases': 'releases',
      'Research': 'research',
      'Documentation': 'docs',
      'Reach Us': 'bisik',
      'MPL-2.0 License': 'license',
      'Privacy': 'privacy',
      'Terms': 'terms',
    };
    return map[label] || null;
  };

  const externalLinks = {
    'GitHub': 'https://github.com/ib823/riina',
    'Issues': 'https://github.com/ib823/riina/issues',
    'Discussions': 'https://github.com/ib823/riina/discussions',
  };

  // Shared styles
  const sectionStyle = { padding: '80px 32px', maxWidth: '1200px', margin: '0 auto' };
  const pageTopStyle = { paddingTop: '80px' };
  const sectionLabel = {
    fontSize: '14px',
    letterSpacing: '0.2em',
    color: '#999',
    marginBottom: '32px'
  };
  const codeBlockStyle = {
    backgroundColor: '#1a1a1a',
    color: '#e0e0e0',
    padding: '32px',
    borderRadius: '4px',
    overflow: 'auto',
    fontSize: '14px',
    lineHeight: 1.8,
    fontFamily: 'SFMono-Regular, Consolas, "Liberation Mono", Menlo, monospace'
  };
  const cardStyle = {
    padding: '24px',
    border: '1px solid #eee',
  };

  // Logo Component (Turnstile)
  const Logo = ({ size = 32, color = '#000' }) => (
    <svg viewBox="0 0 100 100" width={size} height={size}>
      <line x1="35" y1="22" x2="35" y2="78" stroke={color} strokeWidth="7" strokeLinecap="square"/>
      <line x1="35" y1="50" x2="72" y2="50" stroke={color} strokeWidth="7" strokeLinecap="square"/>
    </svg>
  );

  // Reusable page header
  const PageHeader = ({ title, subtitle }) => (
    <section className="section" style={{ padding: '80px 32px', maxWidth: '800px', margin: '0 auto' }}>
      <h1 className="page-title" style={{ fontSize: '48px', fontWeight: 300, marginBottom: '32px' }}>{title}</h1>
      <p style={{ fontSize: '20px', color: '#666', lineHeight: 1.8 }}>{subtitle}</p>
    </section>
  );

  // Keyword table component
  const KeywordTable = ({ title, keywords }) => (
    <div style={{ marginBottom: '48px' }}>
      <h3 style={{ ...sectionLabel, marginBottom: '16px' }}>{title}</h3>
      <div style={{ display: 'grid', gridTemplateColumns: 'repeat(auto-fill, minmax(280px, 1fr))', gap: '12px' }}>
        {keywords.map((kw, i) => (
          <div key={i} style={{
            padding: '14px 16px',
            backgroundColor: '#fff',
            border: '1px solid #eee',
            display: 'grid',
            gridTemplateColumns: '1fr',
            gap: '4px'
          }}>
            <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'baseline' }}>
              <code style={{ fontWeight: 600, fontSize: '15px' }}>{kw.bm}</code>
              <span style={{ color: '#999', fontSize: '12px' }}>{kw.en}</span>
            </div>
            {kw.ex && <code style={{ fontSize: '12px', color: '#666' }}>{kw.ex}</code>}
          </div>
        ))}
      </div>
    </div>
  );

  // Header
  const Header = () => (
    <header className="site-header" style={{
      position: 'fixed',
      top: 0,
      left: 0,
      right: 0,
      zIndex: 100,
      backgroundColor: 'rgba(255,255,255,0.95)',
      backdropFilter: 'blur(10px)',
      borderBottom: '1px solid #eee'
    }}>
      <div className="header-inner" style={{
        maxWidth: '1200px',
        margin: '0 auto',
        padding: '16px 32px',
        display: 'flex',
        justifyContent: 'space-between',
        alignItems: 'center'
      }}>
        <button
          onClick={() => setCurrentPage('home')}
          style={{
            background: 'none',
            border: 'none',
            cursor: 'pointer',
            display: 'flex',
            alignItems: 'center',
            gap: '12px'
          }}
        >
          <Logo size={28} />
          <span style={{
            fontSize: '18px',
            fontWeight: 600,
            letterSpacing: '0.1em'
          }}>RIINA</span>
        </button>

        <button
          className="hamburger"
          onClick={() => setMobileMenuOpen(!mobileMenuOpen)}
          aria-label="Toggle menu"
        >
          <svg width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" strokeWidth="2">
            <line x1="3" y1="6" x2="21" y2="6"/>
            <line x1="3" y1="12" x2="21" y2="12"/>
            <line x1="3" y1="18" x2="21" y2="18"/>
          </svg>
        </button>

        <nav className="site-nav" style={{ display: 'flex', gap: '28px', alignItems: 'center' }}>
          {headerNav.map((item, i) => item.children ? (
            <div
              key={item.label}
              style={{ position: 'relative' }}
              onMouseEnter={() => setOpenDropdown(item.label)}
              onMouseLeave={() => setOpenDropdown(null)}
            >
              <button
                onClick={() => setOpenDropdown(openDropdown === item.label ? null : item.label)}
                style={{
                  background: 'none',
                  border: 'none',
                  cursor: 'pointer',
                  fontSize: '14px',
                  color: item.children.some(c => c.id === currentPage) ? '#000' : '#666',
                  fontWeight: item.children.some(c => c.id === currentPage) ? 500 : 400,
                  display: 'flex',
                  alignItems: 'center',
                  gap: '4px',
                }}
              >
                {item.label}
                <svg width="10" height="6" viewBox="0 0 10 6" fill="none" stroke="currentColor" strokeWidth="1.5">
                  <polyline points="1,1 5,5 9,1"/>
                </svg>
              </button>
              {openDropdown === item.label && (
                <div style={{
                  position: 'absolute',
                  top: '100%',
                  left: '50%',
                  transform: 'translateX(-50%)',
                  paddingTop: '8px',
                  zIndex: 200,
                }}>
                  <div style={{
                    background: '#fff',
                    border: '1px solid #e0e0e0',
                    borderRadius: '8px',
                    boxShadow: '0 4px 16px rgba(0,0,0,0.08)',
                    padding: '8px 0',
                    minWidth: '160px',
                  }}>
                    {item.children.map(child => (
                      <button
                        key={child.id}
                        onClick={() => { setCurrentPage(child.id); setOpenDropdown(null); }}
                        style={{
                          display: 'block',
                          width: '100%',
                          textAlign: 'left',
                          background: currentPage === child.id ? '#f5f5f5' : 'none',
                          border: 'none',
                          cursor: 'pointer',
                          fontSize: '14px',
                          padding: '10px 20px',
                          color: currentPage === child.id ? '#000' : '#555',
                          fontWeight: currentPage === child.id ? 500 : 400,
                        }}
                      >
                        {child.label}
                      </button>
                    ))}
                  </div>
                </div>
              )}
            </div>
          ) : (
            <button
              key={item.id}
              onClick={() => setCurrentPage(item.id)}
              style={{
                background: 'none',
                border: 'none',
                cursor: 'pointer',
                fontSize: '14px',
                color: currentPage === item.id ? '#000' : '#666',
                fontWeight: currentPage === item.id ? 500 : 400
              }}
            >
              {item.label}
            </button>
          ))}
        </nav>

        <a
          className="header-github"
          href="https://github.com/ib823/riina"
          style={{
            backgroundColor: '#000',
            color: '#fff',
            border: 'none',
            padding: '10px 20px',
            fontSize: '14px',
            fontWeight: 500,
            cursor: 'pointer',
            textDecoration: 'none'
          }}
        >
          View on GitHub
        </a>
      </div>

      {/* Mobile menu overlay */}
      <div className={`mobile-menu-overlay${mobileMenuOpen ? ' open' : ''}`}>
        <button className="mobile-menu-close" onClick={() => setMobileMenuOpen(false)} aria-label="Close menu">✕</button>
        {pages.map(page => (
          <button
            key={page.id}
            onClick={() => { setCurrentPage(page.id); setMobileMenuOpen(false); }}
          >
            {page.label}
          </button>
        ))}
        <a href="https://github.com/ib823/riina" style={{ fontSize: '20px', padding: '12px 24px', color: '#333', textDecoration: 'none' }}>
          GitHub
        </a>
      </div>
    </header>
  );

  // ============================================================================
  // HOME PAGE
  // ============================================================================
  const HomePage = () => (
    <div>
      {/* Hero */}
      <section className="hero" style={{
        minHeight: '100vh',
        display: 'flex',
        flexDirection: 'column',
        justifyContent: 'center',
        alignItems: 'center',
        textAlign: 'center',
        padding: '120px 32px 80px'
      }}>
        <div style={{ marginBottom: '32px' }}>
          <Logo size={80} />
        </div>

        <h1 className="hero-title" style={{
          fontSize: '64px',
          fontWeight: 300,
          letterSpacing: '-0.02em',
          marginBottom: '24px',
          maxWidth: '800px',
          lineHeight: 1.1
        }}>
          Security<br/>
          <span style={{ fontWeight: 600 }}>proven at compile time.</span>
        </h1>

        <p style={{
          fontSize: '20px',
          color: '#666',
          maxWidth: '600px',
          lineHeight: 1.6,
          marginBottom: '48px'
        }}>
          RIINA is a formally verified programming language with security
          properties mathematically proven in Coq — not tested, not assumed,
          <em style={{ color: '#000' }}> proven.</em>
        </p>

        <div style={{ display: 'flex', gap: '16px', marginBottom: '80px' }}>
          <button
            onClick={() => setCurrentPage('quickStart')}
            style={{
              backgroundColor: '#000',
              color: '#fff',
              border: 'none',
              padding: '16px 32px',
              fontSize: '16px',
              fontWeight: 500,
              cursor: 'pointer'
            }}
          >
            Get Started
          </button>
          <a
            href="https://github.com/ib823/riina"
            style={{
              backgroundColor: 'transparent',
              color: '#000',
              border: '1px solid #000',
              padding: '16px 32px',
              fontSize: '16px',
              fontWeight: 500,
              cursor: 'pointer',
              textDecoration: 'none',
              display: 'inline-flex',
              alignItems: 'center'
            }}
          >
            View on GitHub
          </a>
        </div>

        {/* Key Stats */}
        <div className="hero-stats" style={{
          display: 'flex',
          gap: '64px',
          paddingTop: '48px',
          borderTop: '1px solid #eee'
        }}>
          {[
            { value: '5,308', label: 'Theorems Proven' },
            { value: '0', label: 'Admits' },
            { value: '278', label: 'Coq Files Verified' },
          ].map((stat, i) => (
            <div key={i} style={{ textAlign: 'center' }}>
              <div style={{
                fontSize: '48px',
                fontWeight: 300,
                fontFamily: 'Georgia, serif'
              }}>{stat.value}</div>
              <div style={{
                fontSize: '12px',
                color: '#999',
                letterSpacing: '0.1em',
                textTransform: 'uppercase'
              }}>{stat.label}</div>
            </div>
          ))}
        </div>
      </section>

      {/* Core Insight */}
      <section className="section-dark" style={{
        backgroundColor: '#000',
        color: '#fff',
        padding: '120px 32px',
        textAlign: 'center'
      }}>
        <p style={{
          fontSize: '14px',
          letterSpacing: '0.2em',
          color: '#666',
          marginBottom: '24px'
        }}>
          THE CORE INSIGHT
        </p>
        <h2 style={{
          fontSize: '42px',
          fontWeight: 300,
          maxWidth: '800px',
          margin: '0 auto 32px',
          lineHeight: 1.4
        }}>
          "Security vulnerabilities are type errors.<br/>
          <span style={{ fontWeight: 600 }}>Eliminate the type, eliminate the attack.</span>"
        </h2>
        <p style={{
          fontSize: '18px',
          color: '#888',
          maxWidth: '600px',
          margin: '0 auto 32px',
          fontFamily: 'Georgia, serif',
          fontStyle: 'italic'
        }}>
          Bertampuk Bertangkai<br/>
          <span style={{ fontSize: '14px', fontStyle: 'normal' }}>Every claim backed by proof</span>
        </p>
        <button
          onClick={() => setCurrentPage('whyProof')}
          style={{
            backgroundColor: 'transparent',
            color: '#888',
            border: '1px solid #444',
            padding: '12px 24px',
            fontSize: '14px',
            cursor: 'pointer'
          }}
        >
          Why mathematical proof? (No technical knowledge required)
        </button>
      </section>

      {/* How It's Different */}
      <section className="section" style={{ padding: '120px 32px', maxWidth: '1200px', margin: '0 auto' }}>
        <div style={{ textAlign: 'center', marginBottom: '80px' }}>
          <p style={{
            fontSize: '14px',
            letterSpacing: '0.2em',
            color: '#999',
            marginBottom: '16px'
          }}>
            A DIFFERENT APPROACH
          </p>
          <h2 style={{
            fontSize: '42px',
            fontWeight: 300
          }}>
            Other tools find bugs.<br/>
            <span style={{ fontWeight: 600 }}>RIINA eliminates them by construction.</span>
          </h2>
        </div>

        <div className="grid-2" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '64px' }}>
          <div>
            <h3 style={{
              fontSize: '12px',
              letterSpacing: '0.2em',
              color: '#999',
              marginBottom: '24px'
            }}>
              TRADITIONAL SECURITY
            </h3>
            <ul style={{ listStyle: 'none', padding: 0, margin: 0 }}>
              {[
                'Write code, hope it\'s secure',
                'Run tests, find some bugs',
                'Deploy, get hacked',
                'Patch, repeat'
              ].map((item, i) => (
                <li key={i} style={{
                  padding: '16px 0',
                  borderBottom: '1px solid #eee',
                  color: '#666',
                  display: 'flex',
                  alignItems: 'center',
                  gap: '12px'
                }}>
                  <span style={{ color: '#ccc' }}>✗</span>
                  {item}
                </li>
              ))}
            </ul>
          </div>

          <div>
            <h3 style={{
              fontSize: '12px',
              letterSpacing: '0.2em',
              color: '#000',
              marginBottom: '24px'
            }}>
              RIINA
            </h3>
            <ul style={{ listStyle: 'none', padding: 0, margin: 0 }}>
              {[
                'Encode security in types: Rahsia<T>, kesan',
                'Compiler proves properties via formal proofs',
                'If it compiles, security holds by construction',
                'Vulnerabilities eliminated at the type level'
              ].map((item, i) => (
                <li key={i} style={{
                  padding: '16px 0',
                  borderBottom: '1px solid #eee',
                  color: '#000',
                  display: 'flex',
                  alignItems: 'center',
                  gap: '12px'
                }}>
                  <span style={{ color: '#000' }}>⊢</span>
                  {item}
                </li>
              ))}
            </ul>
          </div>
        </div>
      </section>

      {/* Code Example */}
      <section style={{
        backgroundColor: '#f8f8f8',
        padding: '120px 32px'
      }}>
        <div style={{ maxWidth: '900px', margin: '0 auto' }}>
          <div style={{ textAlign: 'center', marginBottom: '48px' }}>
            <p style={{
              fontSize: '14px',
              letterSpacing: '0.2em',
              color: '#999',
              marginBottom: '16px'
            }}>
              SEE IT IN ACTION
            </p>
            <h2 style={{ fontSize: '32px', fontWeight: 400 }}>
              Security in the type signature — in Bahasa Melayu
            </h2>
          </div>

          <pre className="code-block" style={codeBlockStyle}>
{`// pengesahan.rii — Authentication in RIINA
modul pengesahan;

bentuk Kelayakan {
    nama_pengguna: Teks,
    kata_laluan: Rahsia<Teks>,   // Secret — cannot leak
    garam: Bait,
}

// Hash with constant-time protection
fungsi hash_kata_laluan(
    kata: Rahsia<Teks>,
    garam: Bait
) -> Rahsia<Bait> kesan Kripto {
    masa_tetap {                  // Prevents timing attacks
        biar derivasi = kripto::argon2id(kata, garam);
        pulang derivasi;
    }
}

// Compile result:
// ⊢ No secret leakage (Rahsia type)
// ⊢ No timing attack (masa_tetap block)
// ⊢ Effects tracked (kesan Kripto)
// ⊢ Proof certificate generated`}
          </pre>
        </div>
      </section>

      {/* Capabilities */}
      <section className="section" style={{ padding: '120px 32px', maxWidth: '1200px', margin: '0 auto' }}>
        <div style={{ textAlign: 'center', marginBottom: '64px' }}>
          <p style={{
            fontSize: '14px',
            letterSpacing: '0.2em',
            color: '#999',
            marginBottom: '16px'
          }}>
            WHAT YOU CAN BUILD
          </p>
          <h2 style={{ fontSize: '42px', fontWeight: 300 }}>
            Proven security. <span style={{ fontWeight: 600 }}>Any domain.</span>
          </h2>
        </div>

        <div style={{
          display: 'grid',
          gridTemplateColumns: 'repeat(4, 1fr)',
          gap: '24px'
        }}>
          {[
            { name: 'Defence & Military', desc: 'CMMC, ITAR-compliant classified data handling', icon: '⊢' },
            { name: 'Healthcare', desc: 'HIPAA-proven PHI protection, audit trails', icon: '⊢' },
            { name: 'Financial Services', desc: 'PCI-DSS, SOX — cardholder data cannot leak', icon: '⊢' },
            { name: 'Post-Quantum Crypto', desc: 'ML-KEM, ML-DSA — constant-time, verified', icon: '⊢' },
            { name: 'Aerospace & Aviation', desc: 'DO-178C DAL A formal verification evidence', icon: '⊢' },
            { name: 'Energy & Utilities', desc: 'NERC CIP SCADA/ICS provable isolation', icon: '⊢' },
            { name: 'Agriculture & IoT', desc: 'Sensor firmware, precision agriculture safety', icon: '⊢' },
            { name: 'Government & GovTech', desc: 'FedRAMP, NIST 800-53 proven controls', icon: '⊢' },
          ].map((item, i) => (
            <div key={i} style={{
              padding: '32px 24px',
              border: '1px solid #eee',
              textAlign: 'center'
            }}>
              <div style={{ fontSize: '24px', marginBottom: '16px' }}>{item.icon}</div>
              <div style={{
                fontSize: '14px',
                fontWeight: 600,
                letterSpacing: '0.05em',
                marginBottom: '8px'
              }}>{item.name}</div>
              <div style={{ fontSize: '13px', color: '#666' }}>{item.desc}</div>
            </div>
          ))}
        </div>
      </section>

      {/* Platform Targets */}
      <section style={{ padding: '80px 32px', backgroundColor: '#f8f8f8' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto', textAlign: 'center' }}>
          <p style={{ fontSize: '14px', letterSpacing: '0.2em', color: '#999', marginBottom: '16px' }}>
            PLATFORM UNIVERSALITY
          </p>
          <h2 style={{ fontSize: '36px', fontWeight: 300, marginBottom: '48px' }}>
            One language. <span style={{ fontWeight: 600 }}>Every platform.</span>
          </h2>
          <div className="grid-4" style={{ display: 'grid', gridTemplateColumns: 'repeat(4, 1fr)', gap: '24px' }}>
            {[
              { name: 'Native', desc: 'C backend — any platform with a C compiler', status: 'Done' },
              { name: 'WebAssembly', desc: 'Direct IR → WASM binary emission', status: 'Done' },
              { name: 'Android', desc: 'NDK cross-compilation + JNI bridges', status: 'Done' },
              { name: 'iOS', desc: 'Xcode toolchain + Swift bridges', status: 'Done' },
            ].map((t, i) => (
              <div key={i} style={{ padding: '24px', border: '1px solid #ddd', backgroundColor: '#fff' }}>
                <div style={{ fontSize: '14px', fontWeight: 600, marginBottom: '8px' }}>{t.name}</div>
                <div style={{ fontSize: '13px', color: '#666', marginBottom: '12px' }}>{t.desc}</div>
                <span style={{ fontSize: '11px', padding: '4px 8px', backgroundColor: t.status === 'Done' ? '#e8f5e9' : '#fff3e0', borderRadius: '4px' }}>{t.status}</span>
              </div>
            ))}
          </div>
        </div>
      </section>

      {/* CTA */}
      <section style={{
        backgroundColor: '#000',
        color: '#fff',
        padding: '120px 32px',
        textAlign: 'center'
      }}>
        <h2 style={{
          fontSize: '48px',
          fontWeight: 300,
          marginBottom: '24px'
        }}>
          Ready to write <span style={{ fontWeight: 600 }}>provably secure</span> code?
        </h2>
        <p style={{
          fontSize: '18px',
          color: '#888',
          marginBottom: '48px'
        }}>
          Open source. MPL-2.0 licensed.
        </p>
        <div style={{ display: 'flex', gap: '16px', justifyContent: 'center' }}>
          <button
            onClick={() => setCurrentPage('quickStart')}
            style={{
              backgroundColor: '#fff',
              color: '#000',
              border: 'none',
              padding: '16px 32px',
              fontSize: '16px',
              fontWeight: 500,
              cursor: 'pointer'
            }}
          >
            Get Started
          </button>
          <a
            href="https://github.com/ib823/riina"
            style={{
              backgroundColor: 'transparent',
              color: '#fff',
              border: '1px solid #fff',
              padding: '16px 32px',
              fontSize: '16px',
              fontWeight: 500,
              cursor: 'pointer',
              textDecoration: 'none',
              display: 'inline-flex',
              alignItems: 'center'
            }}
          >
            View on GitHub
          </a>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // WHY PROOF PAGE — Executive-Friendly Explanation
  // ============================================================================
  const WhyProofPage = () => (
    <div style={pageTopStyle}>
      {/* Hero — The Core Question */}
      <section style={{
        padding: '80px 32px 60px',
        maxWidth: '900px',
        margin: '0 auto'
      }}>
        <p style={{ ...sectionLabel, marginBottom: '24px' }}>FOR DECISION-MAKERS</p>
        <h1 style={{ fontSize: '48px', fontWeight: 300, marginBottom: '32px', lineHeight: 1.2 }}>
          What if your software <span style={{ fontWeight: 600 }}>could not be hacked?</span>
        </h1>
        <p style={{ fontSize: '20px', color: '#666', lineHeight: 1.8, marginBottom: '16px' }}>
          Not "hard to hack." Not "we tested it thoroughly."
          <em style={{ color: '#000' }}> Mathematically impossible to hack</em> — the same way
          it is impossible for 2 + 2 to equal 5.
        </p>
        <p style={{ fontSize: '18px', color: '#666', lineHeight: 1.8 }}>
          This is not a marketing claim. It is the established science of <strong>formal verification</strong> —
          used by DARPA, NASA, Airbus, AWS, and Microsoft for their most critical systems.
          RIINA brings it to every line of code you write.
        </p>
      </section>

      {/* The $4.88M Problem */}
      <section style={{
        backgroundColor: '#000',
        color: '#fff',
        padding: '80px 32px'
      }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <p style={{ fontSize: '14px', letterSpacing: '0.2em', color: '#666', marginBottom: '32px' }}>
            THE BUSINESS CASE
          </p>
          <div className="grid-3" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '48px', marginBottom: '48px' }}>
            {[
              { value: '$4.88M', label: 'Average cost of a data breach', source: 'IBM Cost of Data Breach Report, 2024' },
              { value: '$9.77M', label: 'Average breach cost in healthcare', source: 'Highest industry cost for 14 consecutive years' },
              { value: '292 days', label: 'Average time to identify and contain', source: 'IBM, 2024 — nearly 10 months' },
            ].map((stat, i) => (
              <div key={i}>
                <div style={{ fontSize: '42px', fontWeight: 300, fontFamily: 'Georgia, serif', marginBottom: '8px' }}>{stat.value}</div>
                <div style={{ fontSize: '14px', color: '#ccc', marginBottom: '8px' }}>{stat.label}</div>
                <div style={{ fontSize: '11px', color: '#666', fontStyle: 'italic' }}>{stat.source}</div>
              </div>
            ))}
          </div>
          <p style={{ fontSize: '18px', color: '#888', lineHeight: 1.8, maxWidth: '800px' }}>
            The global cybersecurity market will spend <strong style={{ color: '#fff' }}>$212 billion in 2025</strong> (Gartner) —
            mostly on tools that find bugs <em>after</em> they exist. What if the bugs never existed in the first place?
          </p>
        </div>
      </section>

      {/* The Lock vs Theorem Analogy */}
      <section style={{ padding: '100px 32px' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <p style={{ ...sectionLabel, marginBottom: '32px' }}>THE CORE INSIGHT — NO TECHNICAL KNOWLEDGE REQUIRED</p>
          <h2 style={{ fontSize: '36px', fontWeight: 300, marginBottom: '48px', lineHeight: 1.4 }}>
            Traditional security is a <strong>lock</strong>.<br/>
            RIINA security is a <strong>mathematical theorem</strong>.
          </h2>

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '48px', marginBottom: '64px' }}>
            <div style={{ padding: '32px', border: '1px solid #eee' }}>
              <h3 style={{ fontSize: '12px', letterSpacing: '0.2em', color: '#999', marginBottom: '24px' }}>A LOCK (TRADITIONAL SECURITY)</h3>
              <p style={{ color: '#666', lineHeight: 1.8, fontSize: '15px' }}>
                A lock can be picked by a smarter thief. You make the lock stronger,
                but someone eventually finds a way in. Every year, new attacks break
                what was "secure" last year. You are betting the lock is
                <em> strong enough</em>. That bet has a price: $4.88 million, on average.
              </p>
              <div style={{ marginTop: '24px', padding: '16px', backgroundColor: '#fff3f3', fontSize: '13px', color: '#c62828' }}>
                Firewalls, penetration testing, antivirus, SIEM — all find problems <em>after</em> they exist.
              </div>
            </div>
            <div style={{ padding: '32px', border: '2px solid #000' }}>
              <h3 style={{ fontSize: '12px', letterSpacing: '0.2em', color: '#000', marginBottom: '24px' }}>A THEOREM (RIINA)</h3>
              <p style={{ color: '#333', lineHeight: 1.8, fontSize: '15px' }}>
                A theorem proves that the door <strong>cannot exist in an open state</strong>.
                No lock to pick. No strength to guess. The Pythagorean theorem has held
                for 2,500 years — no computer, no AI, no quantum machine has
                "hacked" it. It never will. <strong>RIINA applies this same principle to your software.</strong>
              </p>
              <div style={{ marginTop: '24px', padding: '16px', backgroundColor: '#e8f5e9', fontSize: '13px', color: '#2e7d32' }}>
                5,308 machine-checked proofs guarantee security properties <em>before</em> the code runs.
              </div>
            </div>
          </div>

          <div style={{
            padding: '32px',
            backgroundColor: '#f8f8f8',
            borderLeft: '4px solid #000',
            marginBottom: '32px'
          }}>
            <p style={{ fontSize: '18px', fontStyle: 'italic', color: '#333', margin: 0, lineHeight: 1.6 }}>
              "Program testing can be used to show the presence of bugs, but never to show their absence."
            </p>
            <p style={{ fontSize: '13px', color: '#999', marginTop: '12px', margin: '12px 0 0 0' }}>
              — Edsger W. Dijkstra, Turing Award Laureate, 1972
            </p>
          </div>
        </div>
      </section>

      {/* Assurance Pyramid */}
      <section style={{ padding: '80px 32px', backgroundColor: '#f8f8f8' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto' }}>
          <p style={{ ...sectionLabel, marginBottom: '16px' }}>THE ASSURANCE HIERARCHY</p>
          <h2 style={{ fontSize: '32px', fontWeight: 300, marginBottom: '16px' }}>
            Not all security is created equal
          </h2>
          <p style={{ color: '#666', fontSize: '15px', marginBottom: '48px', lineHeight: 1.8 }}>
            Most software uses Level 1-2. Critical infrastructure uses Level 3-4. Flight software and
            nuclear systems use Level 5. RIINA gives Level 6 to every program.
          </p>

          <div style={{ display: 'flex', flexDirection: 'column', gap: '0' }}>
            {[
              { level: 6, name: 'Mathematical Proof', desc: 'Proven impossible to have this class of vulnerability. Cannot be invalidated by any future technology.', riina: true, color: '#000', textColor: '#fff', ref: 'RIINA, seL4, CompCert, HACL*' },
              { level: 5, name: 'Formal Model Checking', desc: 'All reachable states exhaustively explored. Limited to finite-state systems.', riina: false, color: '#333', textColor: '#fff', ref: 'AWS Zelkova, TLA+' },
              { level: 4, name: 'Static Analysis', desc: 'Code scanned for known patterns. Can miss novel attack vectors.', riina: false, color: '#666', textColor: '#fff', ref: 'SonarQube, Coverity, CodeQL' },
              { level: 3, name: 'Penetration Testing', desc: 'Experts try to break in. Only finds what testers think to try.', riina: false, color: '#999', textColor: '#fff', ref: 'Manual pen testing, bug bounties' },
              { level: 2, name: 'Automated Testing', desc: 'Run test cases and check outputs. Only covers scenarios you wrote tests for.', riina: false, color: '#bbb', textColor: '#000', ref: 'Unit tests, integration tests, CI/CD' },
              { level: 1, name: 'No Verification', desc: 'Ship and hope. Fix when customers report problems.', riina: false, color: '#ddd', textColor: '#000', ref: 'Most software today' },
            ].map((item, i) => (
              <div key={i} style={{
                display: 'grid',
                gridTemplateColumns: '60px 1fr',
                gap: '0',
                backgroundColor: item.color,
                color: item.textColor,
                padding: item.riina ? '24px 28px' : '16px 28px',
                border: item.riina ? '3px solid #000' : 'none',
                position: 'relative'
              }}>
                <div style={{ fontSize: '24px', fontWeight: 300, fontFamily: 'Georgia, serif', opacity: 0.7 }}>
                  {item.level}
                </div>
                <div>
                  <div style={{ display: 'flex', alignItems: 'center', gap: '12px', marginBottom: '4px' }}>
                    <span style={{ fontWeight: 600, fontSize: '15px' }}>{item.name}</span>
                    {item.riina && <span style={{
                      fontSize: '11px',
                      padding: '2px 10px',
                      backgroundColor: '#fff',
                      color: '#000',
                      fontWeight: 700,
                      letterSpacing: '0.1em'
                    }}>RIINA</span>}
                  </div>
                  <div style={{ fontSize: '13px', opacity: 0.8 }}>{item.desc}</div>
                  <div style={{ fontSize: '11px', opacity: 0.5, marginTop: '4px' }}>{item.ref}</div>
                </div>
              </div>
            ))}
          </div>

          <p style={{ color: '#666', fontSize: '13px', marginTop: '24px', fontStyle: 'italic' }}>
            Based on Common Criteria EAL1–EAL7 (ISO/IEC 15408) and the CyBOK Formal Methods knowledge area.
          </p>
        </div>
      </section>

      {/* Quantum & AI Immunity */}
      <section style={{ padding: '100px 32px' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <p style={{ ...sectionLabel, marginBottom: '16px' }}>FUTURE-PROOF BY DESIGN</p>
          <h2 style={{ fontSize: '36px', fontWeight: 300, marginBottom: '48px', lineHeight: 1.4 }}>
            Quantum computers and AI <span style={{ fontWeight: 600 }}>cannot break mathematical logic</span>
          </h2>

          <div className="grid-3" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '32px', marginBottom: '48px' }}>
            <div style={{ padding: '32px', border: '1px solid #eee' }}>
              <h3 style={{ fontSize: '16px', fontWeight: 600, marginBottom: '16px' }}>Quantum Computing</h3>
              <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.7 }}>
                Quantum computers threaten <strong>encryption</strong> — they can factor large numbers faster
                (Shor's algorithm). But RIINA's proofs are not encryption. They are <em>logical deductions</em>.
                A quantum computer cannot make a valid logical argument invalid, just as it cannot make 2+2 equal 5.
              </p>
            </div>
            <div style={{ padding: '32px', border: '1px solid #eee' }}>
              <h3 style={{ fontSize: '16px', fontWeight: 600, marginBottom: '16px' }}>Artificial Intelligence</h3>
              <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.7 }}>
                AI can <em>find</em> bugs (and create them). But AI cannot invalidate a machine-checked proof.
                Cambridge University research shows deep learning is "untrustworthy and easy to fool."
                RIINA's proofs are checked by Coq — a proof engine that follows logic, not statistics. No hallucination. No error.
              </p>
            </div>
            <div style={{ padding: '32px', border: '1px solid #eee' }}>
              <h3 style={{ fontSize: '16px', fontWeight: 600, marginBottom: '16px' }}>Future Threats</h3>
              <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.7 }}>
                The Pythagorean theorem has survived 2,500 years of advancement. Mathematical proof does not
                expire, decay, or become vulnerable. RIINA's security guarantees hold not because the
                defense is strong, but because the <em>attack is logically impossible</em>.
              </p>
            </div>
          </div>

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '2px', backgroundColor: '#eee' }}>
            <div style={{ padding: '24px', backgroundColor: '#fff' }}>
              <h4 style={{ fontSize: '12px', letterSpacing: '0.1em', color: '#c62828', marginBottom: '12px' }}>ENCRYPTION (BREAKABLE)</h4>
              <p style={{ fontSize: '13px', color: '#666', margin: 0 }}>
                Based on <strong>computational difficulty</strong> — "this is hard to crack."
                Quantum computers and AI make hard problems easier. What is secure today may not be secure tomorrow.
              </p>
            </div>
            <div style={{ padding: '24px', backgroundColor: '#fff' }}>
              <h4 style={{ fontSize: '12px', letterSpacing: '0.1em', color: '#2e7d32', marginBottom: '12px' }}>MATHEMATICAL PROOF (UNBREAKABLE)</h4>
              <p style={{ fontSize: '13px', color: '#666', margin: 0 }}>
                Based on <strong>logical deduction</strong> — "this is impossible by the rules of logic."
                No amount of computing power changes logic. What is proven today is proven forever.
              </p>
            </div>
          </div>
        </div>
      </section>

      {/* Real-World Proof Points */}
      <section style={{ padding: '80px 32px', backgroundColor: '#000', color: '#fff' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <p style={{ fontSize: '14px', letterSpacing: '0.2em', color: '#666', marginBottom: '16px' }}>
            PROVEN IN THE REAL WORLD
          </p>
          <h2 style={{ fontSize: '32px', fontWeight: 300, marginBottom: '48px' }}>
            Organizations that bet on mathematical proof — and won
          </h2>

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '24px' }}>
            {[
              {
                org: 'DARPA',
                title: 'seL4 — the "unhackable" drone kernel',
                desc: 'At DEF CON, DARPA challenged elite hackers to break into a drone running seL4, a formally verified operating system kernel. The hackers compromised the Linux system on board but could not break past seL4\'s mathematically proven security boundary. Zero breaches.',
                source: 'DARPA HACMS Program, DEF CON demonstration'
              },
              {
                org: 'Airbus / Paris Metro',
                title: '25 years, zero safety incidents',
                desc: 'Paris Metro Line 14 has operated driverless since 1998 using software verified with the B formal method. After more than 25 years and billions of passenger-trips, there has been zero software-caused safety incidents. The same method now runs metros in New York, Calcutta, and São Paulo.',
                source: 'CLEARSY, B Method, operational since 1998'
              },
              {
                org: 'Amazon Web Services',
                title: 'Formal verification at cloud scale',
                desc: 'AWS uses formal methods across its infrastructure: s2n (TLS library verified with Coq and SAW), Zelkova (mathematically reasons about ALL possible IAM policy requests, not just test cases), and Tiros (network reachability proofs). Verification runs on every code change.',
                source: 'AWS Security Blog, Provable Security initiative'
              },
              {
                org: 'Microsoft',
                title: 'HACL* — verified crypto in Windows, Linux, Firefox',
                desc: 'Microsoft\'s Project Everest produced HACL*, a formally verified cryptographic library deployed in the Windows kernel, Linux kernel, Firefox browser, and WireGuard VPN. Proven memory-safe, functionally correct, and timing-attack resistant. As fast as OpenSSL.',
                source: 'Microsoft Research, Project Everest, HACL*'
              },
              {
                org: 'CompCert',
                title: '6 CPU-years of attack found zero bugs',
                desc: 'Csmith, an automated bug-finding tool, spent six CPU-years trying to find wrong-code errors in CompCert, a formally verified C compiler. It found zero. In the same campaign, it found bugs in every other compiler tested — GCC, Clang, all of them.',
                source: 'Yang et al., "Finding and Understanding Bugs in C Compilers," PLDI 2011'
              },
              {
                org: 'ProvenRun',
                title: 'First OS to achieve Common Criteria EAL7',
                desc: 'ProvenCore became the first operating system in the world to achieve EAL7 — the highest possible security certification under Common Criteria (ISO 15408). The only way to reach this level is through formal mathematical proof.',
                source: 'ProvenRun, Common Criteria EAL7 certification'
              },
            ].map((item, i) => (
              <div key={i} style={{
                padding: '28px',
                border: '1px solid #333'
              }}>
                <div style={{ fontSize: '11px', letterSpacing: '0.15em', color: '#666', marginBottom: '8px' }}>{item.org}</div>
                <h3 style={{ fontSize: '16px', fontWeight: 600, marginBottom: '12px', color: '#fff' }}>{item.title}</h3>
                <p style={{ fontSize: '13px', color: '#aaa', lineHeight: 1.7, marginBottom: '12px' }}>{item.desc}</p>
                <div style={{ fontSize: '11px', color: '#555', fontStyle: 'italic' }}>{item.source}</div>
              </div>
            ))}
          </div>
        </div>
      </section>

      {/* The Executive Summary */}
      <section style={{ padding: '100px 32px' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto' }}>
          <p style={{ ...sectionLabel, marginBottom: '16px' }}>THE EXECUTIVE SUMMARY</p>
          <h2 style={{ fontSize: '36px', fontWeight: 300, marginBottom: '48px' }}>
            Why your organization should evaluate RIINA
          </h2>

          <div style={{ display: 'flex', flexDirection: 'column', gap: '0' }}>
            {[
              {
                role: 'Chief Executive Officer',
                point: 'Eliminate entire vulnerability classes permanently',
                detail: 'RIINA does not find and fix security bugs. It makes them logically impossible. This is not incremental improvement — it is a category change. Your competitors patch vulnerabilities. Your organization proves they cannot exist.'
              },
              {
                role: 'Chief Information Officer',
                point: 'Reduce security engineering costs by removing the patch cycle',
                detail: 'The average breach takes 292 days to contain and costs $4.88M (IBM, 2024). RIINA-compiled code eliminates the vulnerability classes that cause most breaches — information leaks, injection attacks, timing side-channels — by mathematical construction. No patch Tuesday. No CVE triage for proven-secure components.'
              },
              {
                role: 'Chief Risk Officer',
                point: 'Machine-checkable compliance certificates that auditors can verify independently',
                detail: 'RIINA generates proof certificates mapping code properties to regulatory controls (HIPAA, PCI-DSS, GDPR, DO-178C, and 11 more). Auditors run the Coq proof checker themselves — zero trust in the vendor. This is the strongest evidence available under Common Criteria, and it can reduce audit cycles from weeks to minutes.'
              },
              {
                role: 'Chief Information Security Officer',
                point: 'Security guarantees that survive quantum computing and AI',
                detail: 'RIINA\'s proofs are logical deductions, not computational hardness assumptions. Quantum computers break encryption (Shor\'s algorithm), not logic. AI finds bugs, not counterproofs. Your security posture is future-proof by the laws of mathematics — not by the strength of your current defenses.'
              },
              {
                role: 'Chief Financial Officer',
                point: 'Quantifiable risk elimination — not risk reduction',
                detail: 'Traditional security reduces breach probability. RIINA eliminates specific vulnerability classes entirely — the financial exposure for those classes drops to zero. Formal verification evidence strengthens cyber insurance applications and reduces premiums. The FAIR risk model quantifies this directly in financial terms.'
              },
              {
                role: 'Board of Directors',
                point: 'Due diligence backed by the highest assurance standard in existence',
                detail: 'Formal mathematical proof is the basis for EAL7 (highest Common Criteria), DO-178C DAL A (flight-critical software), and ISO 26262 ASIL-D (automotive safety). DARPA, NASA, Airbus, AWS, and Microsoft use it for their most critical systems. RIINA makes this level of assurance accessible to every organization.'
              },
            ].map((item, i) => (
              <div key={i} style={{
                padding: '32px',
                borderBottom: '1px solid #eee',
                display: 'grid',
                gridTemplateColumns: '200px 1fr',
                gap: '32px',
                alignItems: 'start'
              }}>
                <div>
                  <div style={{ fontSize: '12px', color: '#999', letterSpacing: '0.05em', marginBottom: '8px' }}>{item.role}</div>
                  <div style={{ fontSize: '15px', fontWeight: 600 }}>{item.point}</div>
                </div>
                <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.8, margin: 0 }}>{item.detail}</p>
              </div>
            ))}
          </div>
        </div>
      </section>

      {/* Gradual Adoption */}
      <section style={{ padding: '80px 32px', backgroundColor: '#f8f8f8' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto', textAlign: 'center' }}>
          <p style={{ ...sectionLabel, marginBottom: '16px' }}>START TODAY</p>
          <h2 style={{ fontSize: '32px', fontWeight: 300, marginBottom: '24px' }}>
            No rewrite required. Start with one module.
          </h2>
          <p style={{ color: '#666', fontSize: '16px', lineHeight: 1.8, maxWidth: '700px', margin: '0 auto 48px' }}>
            RIINA integrates with existing C, Rust, and Go codebases via C FFI.
            Use RIINA for your most security-critical component — authentication, payment processing,
            patient data handling — and call it from your existing code. Expand as confidence grows.
          </p>
          <div style={{ display: 'flex', gap: '16px', justifyContent: 'center' }}>
            <button
              onClick={() => setCurrentPage('enterprise')}
              style={{
                backgroundColor: '#000',
                color: '#fff',
                border: 'none',
                padding: '16px 32px',
                fontSize: '16px',
                fontWeight: 500,
                cursor: 'pointer'
              }}
            >
              Enterprise Details
            </button>
            <button
              onClick={() => setCurrentPage('quickStart')}
              style={{
                backgroundColor: 'transparent',
                color: '#000',
                border: '1px solid #000',
                padding: '16px 32px',
                fontSize: '16px',
                fontWeight: 500,
                cursor: 'pointer'
              }}
            >
              Get Started
            </button>
          </div>
        </div>
      </section>

      {/* Sources */}
      <section style={{ padding: '60px 32px' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto' }}>
          <p style={{ ...sectionLabel, marginBottom: '24px' }}>SOURCES &amp; REFERENCES</p>
          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '12px' }}>
            {[
              'IBM Cost of a Data Breach Report, 2024 — $4.88M average, $9.77M healthcare',
              'Gartner, August 2024 — $212B global security spending forecast for 2025',
              'Kahneman & Tversky, Prospect Theory, 1979 — loss aversion in decision-making',
              'Dijkstra, NATO Conference, 1969 — "Testing shows the presence of bugs, not their absence"',
              'DARPA HACMS Program — seL4 formally verified kernel, DEF CON challenge',
              'Yang et al., PLDI 2011 — Csmith found zero bugs in CompCert over 6 CPU-years',
              'CLEARSY, 2024 — Paris Metro Line 14, B Method, 25+ years operational',
              'AWS Security Blog — s2n, Zelkova, Tiros formal verification at scale',
              'Microsoft Research, Project Everest — HACL* in Windows, Linux, Firefox kernels',
              'ProvenRun — ProvenCore, first OS to achieve Common Criteria EAL7',
              'ISO/IEC 15408 (Common Criteria) — EAL1-EAL7 assurance hierarchy',
              'CyBOK Formal Methods for Security Knowledge Area — verification taxonomy',
              'FAIR Institute — Factor Analysis of Information Risk quantitative model',
              'Cambridge University — mathematical limits of neural networks and AI',
            ].map((ref, i) => (
              <div key={i} style={{
                padding: '12px 16px',
                fontSize: '12px',
                color: '#666',
                backgroundColor: '#f8f8f8',
                lineHeight: 1.5
              }}>
                {ref}
              </div>
            ))}
          </div>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // LANGUAGE PAGE
  // ============================================================================
  const LanguagePage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="The Language"
        subtitle="RIINA uses Bahasa Melayu keywords, compile-time security types, and a tracked effect system. If your program compiles, its security properties hold by mathematical proof."
      />

      {/* Bahasa Melayu Keywords */}
      <section style={{ padding: '80px 32px', backgroundColor: '#f8f8f8' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <h2 style={sectionLabel}>BAHASA MELAYU SYNTAX</h2>

          <div className="grid-3" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '16px' }}>
            {[
              { bm: 'fungsi', en: 'fn', ex: 'fungsi tambah(x: Nombor)' },
              { bm: 'biar', en: 'let', ex: 'biar nama = "Ahmad";' },
              { bm: 'kalau / lain', en: 'if / else', ex: 'kalau x > 0 { ... }' },
              { bm: 'pulang', en: 'return', ex: 'pulang hasil;' },
              { bm: 'padan', en: 'match', ex: 'padan nilai { ... }' },
              { bm: 'untuk / selagi', en: 'for / while', ex: 'untuk x dalam senarai' },
              { bm: 'bentuk', en: 'struct', ex: 'bentuk Pengguna { ... }' },
              { bm: 'pilihan', en: 'enum', ex: 'pilihan Hasil { Ok, Gagal }' },
              { bm: 'modul / guna', en: 'mod / use', ex: 'guna std::kripto;' },
            ].map((kw, i) => (
              <div key={i} style={{
                padding: '16px',
                backgroundColor: '#fff',
                border: '1px solid #eee'
              }}>
                <div style={{ fontWeight: 600, fontSize: '16px', marginBottom: '4px' }}>{kw.bm}</div>
                <div style={{ color: '#999', fontSize: '12px', marginBottom: '8px' }}>{kw.en}</div>
                <code style={{ fontSize: '12px', color: '#666' }}>{kw.ex}</code>
              </div>
            ))}
          </div>

          <div style={{ textAlign: 'center', marginTop: '32px' }}>
            <button
              onClick={() => setCurrentPage('syntax')}
              style={{
                background: 'none',
                border: '1px solid #000',
                padding: '12px 24px',
                cursor: 'pointer',
                fontSize: '14px'
              }}
            >
              View full keyword reference (60+ keywords)
            </button>
          </div>
        </div>
      </section>

      {/* Security Types */}
      <section style={{ padding: '80px 32px' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <h2 style={sectionLabel}>SECURITY TYPES</h2>

          <div className="grid-2" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '64px' }}>
            {[
              {
                title: 'Rahsia<T> — Secret data',
                desc: 'Wraps sensitive values. Cannot be logged, printed, or sent over the network. Must be explicitly declassified with dedah() and a policy proof.'
              },
              {
                title: 'kesan — Effect tracking',
                desc: 'Every side effect is declared in the function signature: kesan Kripto, kesan Baca, kesan Tulis. The compiler enforces which effects are permitted.'
              },
              {
                title: 'masa_tetap — Constant time',
                desc: 'Code inside a masa_tetap block is proven to execute in constant time regardless of secret values. Prevents timing side-channel attacks.'
              },
              {
                title: 'dedah() — Declassification',
                desc: 'The only way to extract secret data. Requires a proof that the declassification satisfies the security policy. No proof, no effect.'
              }
            ].map((item, i) => (
              <div key={i} style={{
                padding: '32px',
                border: '1px solid #eee'
              }}>
                <h3 style={{ fontSize: '18px', marginBottom: '12px', fontFamily: 'monospace' }}>{item.title}</h3>
                <p style={{ color: '#666', lineHeight: 1.6 }}>{item.desc}</p>
              </div>
            ))}
          </div>

          <div style={{ textAlign: 'center', marginTop: '32px' }}>
            <button
              onClick={() => setCurrentPage('securityTypes')}
              style={{
                background: 'none',
                border: '1px solid #000',
                padding: '12px 24px',
                cursor: 'pointer',
                fontSize: '14px'
              }}
            >
              See all security types and levels
            </button>
          </div>
        </div>
      </section>

      {/* Code Example */}
      <section style={{ padding: '80px 32px', backgroundColor: '#f8f8f8' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto' }}>
          <h2 style={{ fontSize: '32px', marginBottom: '32px' }}>Real RIINA code</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// Verify password with full security guarantees
fungsi sahkan_kata_laluan(
    input: Rahsia<Teks>,
    tersimpan: Rahsia<Bait>,
    garam: Bait
) -> Mungkin<BuktiSahKataLaluan> kesan Kripto {
    masa_tetap {
        biar hash_input = hash_kata_laluan(input, garam);

        // Constant-time comparison
        kalau kripto::banding_tetap(hash_input, tersimpan) {
            pulang Ada(bukti KeselamatanSahKataLaluan);
        } lain {
            pulang Tiada;
        }
    }
}`}
          </pre>
        </div>
      </section>

      {/* Proven Properties */}
      <section style={{ padding: '80px 32px', backgroundColor: '#000', color: '#fff' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <h2 style={{
            fontSize: '14px',
            letterSpacing: '0.2em',
            color: '#666',
            marginBottom: '48px'
          }}>PROVEN AT COMPILE TIME</h2>

          <div className="grid-3" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '32px' }}>
            {[
              'Type safety (Progress + Preservation)',
              'Non-interference',
              'Information flow control',
              'Constant-time execution',
              'Effect safety',
              'Memory safety',
              'Termination of pure code',
              'Secret zeroization',
              'Declassification policy'
            ].map((prop, i) => (
              <div key={i} style={{
                padding: '20px',
                borderBottom: '1px solid #333',
                display: 'flex',
                alignItems: 'center',
                gap: '12px'
              }}>
                <span style={{ color: '#0f0' }}>⊢</span>
                {prop}
              </div>
            ))}
          </div>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // SYNTAX PAGE (Language → Syntax)
  // ============================================================================
  const SyntaxPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Syntax Reference"
        subtitle="RIINA uses Bahasa Melayu keywords — the first systems programming language with native non-English syntax. 60+ keywords across 9 categories."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <KeywordTable title="DECLARATIONS" keywords={[
            { bm: 'fungsi', en: 'fn', ex: 'fungsi tambah(x: Nombor) -> Nombor' },
            { bm: 'biar', en: 'let', ex: 'biar nama = "Ahmad";' },
            { bm: 'ubah', en: 'mut', ex: 'biar ubah kiraan = 0;' },
            { bm: 'tetap', en: 'const', ex: 'tetap MAX = 100;' },
            { bm: 'statik', en: 'static', ex: 'statik CACHE: Senarai = [];' },
            { bm: 'bentuk', en: 'struct', ex: 'bentuk Pengguna { nama: Teks }' },
            { bm: 'pilihan', en: 'enum', ex: 'pilihan Warna { Merah, Biru }' },
            { bm: 'jenis', en: 'type', ex: 'jenis Id = Nombor;' },
            { bm: 'sifat', en: 'trait', ex: 'sifat Boleh_Cetak { ... }' },
            { bm: 'laksana', en: 'impl', ex: 'laksana Pengguna { ... }' },
            { bm: 'modul', en: 'mod', ex: 'modul pengesahan;' },
            { bm: 'guna', en: 'use', ex: 'guna std::io;' },
            { bm: 'awam', en: 'pub', ex: 'awam fungsi api() { }' },
            { bm: 'luaran', en: 'extern', ex: 'luaran "C" { ... }' },
          ]} />

          <KeywordTable title="CONTROL FLOW" keywords={[
            { bm: 'kalau', en: 'if', ex: 'kalau x > 0 { ... }' },
            { bm: 'lain', en: 'else', ex: 'lain { ... }' },
            { bm: 'untuk', en: 'for', ex: 'untuk i dalam 0..10 { }' },
            { bm: 'selagi', en: 'while', ex: 'selagi aktif { }' },
            { bm: 'ulang', en: 'loop', ex: 'ulang { ... keluar; }' },
            { bm: 'keluar', en: 'break', ex: 'keluar;' },
            { bm: 'terus', en: 'continue', ex: 'terus;' },
            { bm: 'pulang', en: 'return', ex: 'pulang hasil;' },
            { bm: 'padan', en: 'match', ex: 'padan nilai { ... }' },
            { bm: 'dengan', en: 'with', ex: 'kendali e dengan { }' },
          ]} />

          <KeywordTable title="BOOLEAN & LOGIC" keywords={[
            { bm: 'betul', en: 'true', ex: 'biar aktif = betul;' },
            { bm: 'salah', en: 'false', ex: 'biar tutup = salah;' },
            { bm: 'dan', en: 'and/&&', ex: 'kalau a dan b { }' },
            { bm: 'atau', en: 'or/||', ex: 'kalau a atau b { }' },
            { bm: 'bukan', en: 'not/!', ex: 'kalau bukan aktif { }' },
            { bm: 'dalam', en: 'in', ex: 'untuk x dalam senarai' },
            { bm: 'ialah', en: 'is', ex: 'kalau x ialah Nombor' },
            { bm: 'sebagai', en: 'as', ex: 'x sebagai Nombor' },
          ]} />

          <KeywordTable title="BUILT-IN TYPES" keywords={[
            { bm: 'Kosong', en: 'Unit/()', ex: 'fungsi cetak() -> Kosong' },
            { bm: 'Benar', en: 'Bool', ex: 'biar aktif: Benar = betul;' },
            { bm: 'Nombor', en: 'Int', ex: 'biar x: Nombor = 42;' },
            { bm: 'Pecahan', en: 'Float', ex: 'biar pi: Pecahan = 3.14;' },
            { bm: 'Teks', en: 'String', ex: 'biar nama: Teks = "Ahmad";' },
            { bm: 'Aksara', en: 'Char', ex: "biar c: Aksara = 'A';" },
            { bm: 'Bait', en: 'Bytes', ex: 'biar data: Bait = b"...";' },
            { bm: 'Senarai', en: 'Vec/List', ex: 'biar s: Senarai<Nombor> = [];' },
            { bm: 'Peta', en: 'Map', ex: 'biar p: Peta<Teks, Nombor> = {};' },
            { bm: 'Set', en: 'Set', ex: 'biar k: Set<Teks> = set![];' },
            { bm: 'Mungkin', en: 'Option', ex: 'Ada(x) / Tiada' },
            { bm: 'Hasil', en: 'Result', ex: 'Jadi(x) / Gagal(e)' },
          ]} />

          <KeywordTable title="SECURITY" keywords={[
            { bm: 'rahsia', en: 'secret', ex: 'biar kunci: Rahsia<Teks>' },
            { bm: 'terbuka', en: 'public', ex: 'tahap Terbuka' },
            { bm: 'sulit', en: 'classify', ex: 'sulit(data)' },
            { bm: 'dedah', en: 'declassify', ex: 'dedah(x, bukti: B)' },
            { bm: 'bukti', en: 'prove', ex: 'bukti KeselamatanSah' },
            { bm: 'dasar', en: 'policy', ex: 'dasar: "semak_kata"' },
            { bm: 'tahap', en: 'level', ex: 'tahap Rahsia' },
            { bm: 'selamat', en: 'safe', ex: 'selamat { ... }' },
            { bm: 'bahaya', en: 'unsafe', ex: 'bahaya { ... }' },
          ]} />

          <KeywordTable title="EFFECTS" keywords={[
            { bm: 'kesan', en: 'effect', ex: 'fungsi f() -> T kesan Baca' },
            { bm: 'Bersih', en: 'Pure', ex: 'kesan Bersih' },
            { bm: 'Baca', en: 'Read', ex: 'kesan Baca' },
            { bm: 'Tulis', en: 'Write', ex: 'kesan Tulis' },
            { bm: 'Rangkaian', en: 'Network', ex: 'kesan Rangkaian' },
            { bm: 'Kripto', en: 'Crypto', ex: 'kesan Kripto' },
            { bm: 'Sistem', en: 'System', ex: 'kesan Sistem' },
            { bm: 'laku', en: 'perform', ex: 'laku Tulis cetak(x);' },
            { bm: 'kendali', en: 'handle', ex: 'kendali kesan { ... }' },
            { bm: 'sambung', en: 'resume', ex: 'sambung(nilai);' },
          ]} />

          <KeywordTable title="CONSTANT-TIME & CONCURRENCY" keywords={[
            { bm: 'masa_tetap', en: 'constant-time', ex: 'masa_tetap { ... }' },
            { bm: 'selamat_spekulasi', en: 'speculation-safe', ex: 'selamat_spekulasi { ... }' },
            { bm: 'sesi', en: 'session', ex: 'sesi S { ... }' },
            { bm: 'saluran', en: 'channel', ex: 'biar c: saluran<Nombor>;' },
            { bm: 'hantar', en: 'send', ex: 'hantar(c, mesej);' },
            { bm: 'terima', en: 'receive', ex: 'biar m = terima(c);' },
          ]} />

          <KeywordTable title="REFERENCES & OWNERSHIP" keywords={[
            { bm: 'ruj', en: 'ref', ex: 'biar r = ruj x;' },
            { bm: 'pinjam', en: 'borrow', ex: 'pinjam &x' },
            { bm: 'pindah', en: 'move', ex: 'pindah nilai' },
            { bm: 'diri', en: 'self', ex: 'fungsi kaedah(diri) { }' },
            { bm: 'Diri', en: 'Self', ex: 'pulang Diri { ... };' },
          ]} />
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // SECURITY TYPES PAGE (Language → Security Types)
  // ============================================================================
  const SecurityTypesPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Security Types"
        subtitle="RIINA's type system encodes security properties directly. The compiler proves information flow, constant-time execution, and declassification correctness."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <h2 style={sectionLabel}>SECURITY WRAPPER TYPES</h2>

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '24px', marginBottom: '64px' }}>
            {[
              { name: 'Rahsia<T>', en: 'Secret', desc: 'Wraps sensitive values. Cannot be logged, printed, serialized, or sent over the network. Must be explicitly declassified with dedah() and a policy proof. Information flow is tracked at compile time.' },
              { name: 'Terbuka<T>', en: 'Public', desc: 'Marks data as public. Can flow anywhere freely. Default for unannoted types. Explicit annotation documents intent.' },
              { name: 'Tercemar<T,S>', en: 'Tainted', desc: 'Marks data from untrusted sources. Must be sanitized before use in security-sensitive operations. Tracks taint source S for provenance.' },
              { name: 'Berlabel<T,L>', en: 'Labeled', desc: 'Attaches an arbitrary security label L to data. Labels form a lattice: data can only flow from lower to higher labels. Generalizes Rahsia/Terbuka.' },
              { name: 'MasaTetap<T>', en: 'ConstantTime', desc: 'Ensures operations on this value execute in constant time. Prevents timing side-channel attacks. The compiler verifies that no branching depends on the secret value.' },
              { name: 'Bukti<T>', en: 'Proof', desc: 'A compile-time proof witness. Carries no runtime data. Used to prove security policies are satisfied before declassification or unsafe operations.' },
            ].map((t, i) => (
              <div key={i} style={cardStyle}>
                <div style={{ display: 'flex', justifyContent: 'space-between', marginBottom: '12px' }}>
                  <code style={{ fontSize: '16px', fontWeight: 600 }}>{t.name}</code>
                  <span style={{ color: '#999', fontSize: '12px' }}>{t.en}</span>
                </div>
                <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.6 }}>{t.desc}</p>
              </div>
            ))}
          </div>

          <h2 style={sectionLabel}>SECURITY LEVELS (LATTICE)</h2>
          <div style={{
            display: 'flex',
            alignItems: 'center',
            gap: '16px',
            padding: '24px',
            backgroundColor: '#f8f8f8',
            marginBottom: '64px',
            overflowX: 'auto'
          }}>
            {['Terbuka (Public)', 'Dalaman (Internal)', 'Sesi (Session)', 'Pengguna (User)', 'Sistem (System)', 'Rahsia (Secret)'].map((level, i) => (
              <React.Fragment key={i}>
                <div style={{
                  padding: '12px 16px',
                  border: '1px solid #ddd',
                  backgroundColor: '#fff',
                  fontSize: '13px',
                  fontFamily: 'monospace',
                  whiteSpace: 'nowrap'
                }}>{level}</div>
                {i < 5 && <span style={{ color: '#ccc', fontSize: '18px' }}>&lt;</span>}
              </React.Fragment>
            ))}
          </div>

          <h2 style={sectionLabel}>DECLASSIFICATION</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// dedah() — the ONLY way to extract secret data
// Requires a proof that the security policy is satisfied

fungsi log_percubaan_masuk(
    nama: Teks,
    kata: Rahsia<Teks>
) -> Teks kesan Tulis {
    // COMPILE ERROR: Cannot use Rahsia<Teks> in Tulis context
    // cetak(kata);  ← This will NOT compile

    // Must declassify with a policy proof:
    biar hash = hash_kata_laluan(kata, garam);
    biar teks_log = dedah(hash, bukti: DasarLogAudit {
        tujuan: "audit trail",
        kelulusan: betul,
    });

    pulang format!("Login attempt: {} -> {}", nama, teks_log);
}

// The compiler verifies:
// ⊢ dedah() has a valid policy proof
// ⊢ The policy satisfies the security lattice
// ⊢ No implicit information flows bypass the check`}
          </pre>

          <h2 style={{ ...sectionLabel, marginTop: '64px' }}>CONSTANT-TIME BLOCKS</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// masa_tetap blocks prove constant-time execution
// No branching on secret values allowed inside

fungsi banding_rahsia(
    a: Rahsia<Bait>,
    b: Rahsia<Bait>
) -> Benar kesan Kripto {
    masa_tetap {
        // Compiler proves: execution time is independent of a, b
        biar hasil: Benar = betul;
        untuk i dalam 0..panjang(a) {
            hasil = hasil dan (a[i] == b[i]);
        }
        pulang hasil;
    }
    // COMPILE ERROR inside masa_tetap:
    // kalau a[0] > b[0] { ... }  ← Branch depends on secret!
}`}
          </pre>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // EFFECT SYSTEM PAGE (Language → Effect System)
  // ============================================================================
  const EffectSystemPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Effect System"
        subtitle="Every side effect in RIINA is declared in the type signature and tracked by the compiler. Algebraic effects with handlers give you control over what your code can do."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <h2 style={sectionLabel}>EFFECT KEYWORDS</h2>
          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '16px', marginBottom: '64px' }}>
            {[
              { kw: 'kesan', en: 'effect', desc: 'Declare effects in function signatures' },
              { kw: 'laku', en: 'perform', desc: 'Perform an effect operation' },
              { kw: 'kendali', en: 'handle', desc: 'Handle effects from a block of code' },
              { kw: 'sambung', en: 'resume', desc: 'Resume computation from an effect handler' },
              { kw: 'batal', en: 'abort', desc: 'Abort computation without resuming' },
            ].map((e, i) => (
              <div key={i} style={cardStyle}>
                <code style={{ fontWeight: 600, fontSize: '16px' }}>{e.kw}</code>
                <span style={{ color: '#999', fontSize: '12px', marginLeft: '8px' }}>({e.en})</span>
                <p style={{ color: '#666', fontSize: '14px', marginTop: '8px' }}>{e.desc}</p>
              </div>
            ))}
          </div>

          <h2 style={sectionLabel}>BUILT-IN EFFECTS</h2>
          <div className="grid-3" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '16px', marginBottom: '64px' }}>
            {[
              { name: 'Bersih', en: 'Pure', desc: 'No side effects. Default. Provably terminating.' },
              { name: 'Baca', en: 'Read', desc: 'File system read access.' },
              { name: 'Tulis', en: 'Write', desc: 'File system write, stdout, logging.' },
              { name: 'Rangkaian', en: 'Network', desc: 'Network I/O: HTTP, TCP, DNS.' },
              { name: 'Kripto', en: 'Crypto', desc: 'Cryptographic operations. Implies constant-time.' },
              { name: 'Sistem', en: 'System', desc: 'System calls, process management.' },
            ].map((e, i) => (
              <div key={i} style={{
                padding: '20px',
                border: '1px solid #eee',
                textAlign: 'center'
              }}>
                <code style={{ fontSize: '16px', fontWeight: 600 }}>{e.name}</code>
                <div style={{ fontSize: '11px', color: '#999', marginTop: '4px' }}>{e.en}</div>
                <p style={{ fontSize: '13px', color: '#666', marginTop: '8px' }}>{e.desc}</p>
              </div>
            ))}
          </div>

          <h2 style={sectionLabel}>EFFECT COMPOSITION</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// Effects compose with +
fungsi muat_dan_nyahsulit(
    laluan: Teks,
    kunci: Rahsia<Bait>
) -> Rahsia<Teks> kesan Baca + Kripto {
    biar data = laku Baca baca_fail(laluan);
    biar teks = laku Kripto nyahsulit(data, kunci);
    pulang teks;
}

// Pure functions have no effect annotation (or explicit kesan Bersih)
fungsi tambah(a: Nombor, b: Nombor) -> Nombor {
    pulang a + b;
}

// The compiler REJECTS effect violations:
// fungsi rahsia_bocor() -> Teks kesan Bersih {
//     laku Rangkaian hantar(data);  ← COMPILE ERROR: Rangkaian not in effect set
// }`}
          </pre>

          <h2 style={{ ...sectionLabel, marginTop: '64px' }}>EFFECT HANDLERS</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// Algebraic effect handlers intercept and transform effects

kesan Log {
    fungsi catat(mesej: Teks) -> Kosong;
}

fungsi proses_dengan_log() -> Nombor kesan Log {
    laku Log catat("Mula pemprosesan");
    biar hasil = kira_sesuatu();
    laku Log catat("Selesai");
    pulang hasil;
}

// Handler: redirect logs to a list
fungsi kumpul_log() -> (Nombor, Senarai<Teks>) {
    biar ubah log = [];
    biar hasil = kendali proses_dengan_log() {
        Log::catat(mesej) => {
            log.tolak(mesej);
            sambung(());  // resume the computation
        }
    };
    pulang (hasil, log);
}

// Effect-gated crypto: only Kripto-annotated functions can use
fungsi jana_kunci() -> Rahsia<Bait> kesan Kripto {
    masa_tetap {
        biar kunci = laku Kripto jana_rawak(32);
        pulang Rahsia(kunci);
    }
}`}
          </pre>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // EXAMPLES PAGE (Language → Examples)
  // ============================================================================
  const ExamplesPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Examples"
        subtitle="112 example .rii files across 9 categories, demonstrating RIINA's syntax, security types, effects, compliance, and design patterns."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <h2 style={sectionLabel}>EXAMPLE CATEGORIES</h2>
          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '24px', marginBottom: '64px' }}>
            {[
              { name: '00_basics/', count: 20, desc: 'Hello world, variables, loops, pattern matching, closures, recursion' },
              { name: '01_security/', count: 18, desc: 'Secret types, declassification, constant-time, capabilities, taint tracking, zeroizing' },
              { name: '02_effects/', count: 15, desc: 'Effect handlers, composition, crypto ops, filesystem, network, pure/IO boundary' },
              { name: '03_applications/', count: 15, desc: 'API gateway, password manager, chat app, web server, session manager' },
              { name: '04_compliance/', count: 10, desc: 'HIPAA, PCI-DSS, GDPR, CCPA, FERPA, SOX, PDPA, ISO 27001, NIST' },
              { name: '05_patterns/', count: 15, desc: 'Builder, factory, state machine, phantom types, lens, visitor, monad' },
              { name: '06_ai_context/', count: 1, desc: 'Complete language cheatsheet for AI/LLM context' },
              { name: 'ffi/', count: 2, desc: 'C FFI: calling puts, abs, rand from RIINA via luaran "C"' },
              { name: 'demos/', count: 5, desc: 'Runnable demos: hello, secrets, FFI, pairs, factorial' },
              { name: 'showcase/', count: 3, desc: 'Secure web server, PQ messenger, HIPAA medical records' },
            ].map((cat, i) => (
              <div key={i} style={cardStyle}>
                <div style={{ display: 'flex', justifyContent: 'space-between', marginBottom: '8px' }}>
                  <code style={{ fontWeight: 600, fontSize: '14px' }}>{cat.name}</code>
                  <span style={{ color: '#999', fontSize: '12px' }}>{cat.count} files</span>
                </div>
                <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.5 }}>{cat.desc}</p>
              </div>
            ))}
          </div>

          <h2 style={sectionLabel}>HELLO WORLD</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// hello_dunia.rii — Hello World in RIINA
modul hello_dunia;
guna std::io;

awam fungsi utama() -> kesan Tulis {
    biar mesej = "Selamat datang ke RIINA!";
    biar nama = "Dunia";
    biar salam = format!("{} Hello, {}!", mesej, nama);
    laku Tulis cetak_baris(salam);
    pulang ();
}

fungsi tambah(x: Nombor, y: Nombor) -> Nombor kesan Bersih {
    pulang x + y;
}

fungsi gambar_nombor(n: Nombor) -> Teks {
    padan n {
        0 => "kosong",
        1 => "satu",
        2 => "dua",
        _ => "banyak",
    }
}`}
          </pre>

          <h2 style={{ ...sectionLabel, marginTop: '64px' }}>AUTHENTICATION (SECURITY TYPES)</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// pengesahan.rii — Full authentication with security proofs
modul pengesahan;
guna std::kripto;

bentuk Kelayakan {
    nama_pengguna: Teks,
    kata_laluan: Rahsia<Teks>,  // Password is secret!
    garam: Bait,
}

pilihan HasilPengesahan {
    Berjaya(TokenSesi),
    Gagal(SebabGagal),
}

fungsi hash_kata_laluan(
    kata: Rahsia<Teks>,
    garam: Bait
) -> Rahsia<Bait> kesan Kripto {
    masa_tetap {
        biar derivasi = kripto::argon2id(kata, garam);
        pulang derivasi;
    }
}

awam fungsi sahkan_pengguna(
    nama: Teks,
    kata: Rahsia<Teks>,
    pangkalan: Pangkalan
) -> HasilPengesahan kesan Baca + Kripto {
    padan pangkalan.cari_pengguna(nama) {
        Tiada => pulang HasilPengesahan::Gagal(SebabGagal::PenggunaTidakDitemui),
        Ada(pengguna) => {
            kalau pengguna.dikunci {
                pulang HasilPengesahan::Gagal(SebabGagal::AkaunDikunci);
            }
            padan sahkan_kata_laluan(kata, pengguna.hash_kata, pengguna.garam) {
                Ada(bukti_sah) => {
                    biar token = cipta_token_sesi(pengguna.id);
                    pulang HasilPengesahan::Berjaya(token);
                }
                Tiada => pulang HasilPengesahan::Gagal(SebabGagal::KataLaluanSalah),
            }
        }
    }
}`}
          </pre>

          <h2 style={{ ...sectionLabel, marginTop: '64px' }}>POST-QUANTUM CRYPTOGRAPHY</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// kripto.rii — ML-KEM key encapsulation + ChaCha20-Poly1305
modul kripto;

bentuk KunciAwamMLKEM { data: Bait }
bentuk KunciRahsiaMLKEM { data: Rahsia<Bait> }

awam fungsi jana_kunci_mlkem() -> (KunciAwamMLKEM, KunciRahsiaMLKEM) kesan Kripto {
    masa_tetap {
        biar (awam, rahsia) = mlkem_1024::jana_pasangan();
        pulang (
            KunciAwamMLKEM { data: awam },
            KunciRahsiaMLKEM { data: rahsia }
        );
    }
}

awam fungsi sulit(
    kunci: Kunci,
    nonce: Nonce,
    data_berkaitan: Bait,
    teks_biasa: Rahsia<Bait>
) -> DataTersahkan kesan Kripto {
    masa_tetap {
        biar (cipher, tag) = chacha20_poly1305::sulit(
            kunci.data, nonce.data, data_berkaitan, teks_biasa
        );
        pulang DataTersahkan { cipher, tag };
    }
}`}
          </pre>

          <h2 style={{ ...sectionLabel, marginTop: '64px' }}>LIVE DEMOS</h2>
          <p style={{ color: '#666', fontSize: '14px', marginBottom: '24px' }}>
            Pre-recorded output from <code>riinac run</code> on actual demo files.
          </p>
          {[
            { name: 'selamat_datang.rii', title: 'Hello Malaysia', output: `$ riinac run 07_EXAMPLES/demos/selamat_datang.rii
Selamat datang ke RIINA!
Hello, Dunia!
RIINA: Rigorous Immutable Invariant, No Assumptions` },
            { name: 'faktorial.rii', title: 'Recursive Factorial', output: `$ riinac run 07_EXAMPLES/demos/faktorial.rii
faktorial(0) = 1
faktorial(1) = 1
faktorial(5) = 120
faktorial(10) = 3628800
faktorial(20) = 2432902008176640000` },
            { name: 'pasangan.rii', title: 'Safe Pairs', output: `$ riinac run 07_EXAMPLES/demos/pasangan.rii
Pasangan: (Ahmad, 25)
Nama: Ahmad
Umur: 25
Jumlah: 3` },
            { name: 'rahsia_dijaga.rii', title: 'Secret Types', output: `$ riinac run 07_EXAMPLES/demos/rahsia_dijaga.rii
Kata laluan diterima (panjang: 12)
Hash: [RAHSIA - tidak boleh cetak]
Pengesahan: berjaya` },
            { name: 'kalkulator_c.rii', title: 'C FFI', output: `$ riinac build 07_EXAMPLES/demos/kalkulator_c.rii && ./output
Hello from RIINA via C FFI!
abs(-42) = 42
rand() = 1804289383` },
          ].map((demo, i) => (
            <div key={i} style={{ marginBottom: '24px' }}>
              <div style={{ fontSize: '14px', fontWeight: 600, marginBottom: '8px' }}>
                {demo.title} — <code>{demo.name}</code>
              </div>
              <pre style={{
                ...codeBlockStyle,
                color: '#4af626',
                fontSize: '13px',
                lineHeight: 1.6,
                padding: '20px 24px'
              }}>
{demo.output}
              </pre>
            </div>
          ))}

          <h2 style={{ ...sectionLabel, marginTop: '64px' }}>SHOWCASE: PROVABLY SECURE WEB SERVER</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// pelayan_web_selamat.rii — Web server where the compiler PROVES:
// ✓ No SQL injection (TeksSqlSelamat type)
// ✓ No XSS (TeksHtmlSelamat type)
// ✓ No path traversal (LaluanSelamat type)
// ✓ No secret leakage (Rahsia type)
// ✓ No timing attacks (masa_tetap blocks)

modul pelayan_web_selamat;
guna std::io;
guna std::kripto;

bentuk Permintaan {
    kaedah: Teks,
    laluan: LaluanSelamat,        // Path traversal impossible
    badan: TeksHtmlSelamat,       // XSS impossible
}

fungsi kendalikan(permintaan: Permintaan, db: Pangkalan)
    -> Respons kesan Baca + Tulis {
    biar pertanyaan = sql_selamat("SELECT * FROM pengguna WHERE id = ?", permintaan.laluan);
    // \u2191 Returns TeksSqlSelamat — injection impossible by construction
    biar data = db.laksana(pertanyaan);
    pulang Respons::ok(html_selamat(data));
}`}
          </pre>

          <h2 style={{ ...sectionLabel, marginTop: '64px' }}>SHOWCASE: POST-QUANTUM ENCRYPTED MESSENGER</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// utusan_pasca_kuantum.rii — E2E encrypted chat
// Compiler PROVES: keys zeroized, no plaintext leakage, constant-time

modul utusan_pasca_kuantum;
guna std::kripto;

fungsi hantar_mesej(
    kunci_awam: KunciAwamMLKEM,
    mesej: Rahsia<Teks>
) -> MesejSulit kesan Kripto {
    masa_tetap {
        biar (kunci_sesi, teks_sifer) = mlkem_1024::enkapsulasi(kunci_awam);
        biar nonce = jana_nonce_monotonik();
        biar sulit = chacha20_poly1305::sulit(kunci_sesi, nonce, mesej);
        sifar_kan(kunci_sesi);  // Compiler enforces zeroization
        pulang MesejSulit { teks_sifer, nonce, sulit };
    }
}`}
          </pre>

          <h2 style={{ ...sectionLabel, marginTop: '64px' }}>SHOWCASE: HIPAA-COMPLIANT MEDICAL RECORDS</h2>
          <pre className="code-block" style={codeBlockStyle}>
{`// rekod_perubatan_hipaa.rii — HIPAA medical records
// Compiler PROVES: PHI never escapes authorized scope, full audit trail

modul rekod_perubatan_hipaa;

bentuk RekodPerubatan {
    id_pesakit: Teks,
    nama: PHI<Teks>,           // Protected Health Information
    diagnosis: PHI<Teks>,
    ubatan: PHI<Senarai<Teks>>,
}

fungsi akses_rekod(
    pengguna: Pengguna,
    rekod: RekodPerubatan,
    log: LogAudit
) -> Keputusan<PHI<Teks>> kesan Baca + Tulis {
    kalau !semak_peranan(pengguna, Peranan::Doktor) {
        log.catat(pengguna, "DITOLAK", rekod.id_pesakit);
        pulang Keputusan::Gagal("Akses ditolak");
    }
    log.catat(pengguna, "AKSES", rekod.id_pesakit);
    // PHI<T> type ensures data cannot escape without authorization
    pulang Keputusan::Ok(rekod.diagnosis);
}`}
          </pre>

          <div style={{ textAlign: 'center', marginTop: '48px' }}>
            <a
              href="https://github.com/ib823/riina/tree/main/07_EXAMPLES"
              style={{
                display: 'inline-block',
                padding: '14px 28px',
                border: '1px solid #000',
                color: '#000',
                textDecoration: 'none',
                fontSize: '14px'
              }}
            >
              Browse all 112 examples on GitHub
            </a>
          </div>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // HOW IT WORKS PAGE
  // ============================================================================
  const HowPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="How It Works"
        subtitle="RIINA uses security types, algebraic effects, and formal verification to transform security requirements into compiler constraints."
      />

      {/* Step by step */}
      <section style={{ padding: '80px 32px' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto' }}>
          {[
            {
              step: '01',
              title: 'Security as Types',
              content: `In RIINA, security is in the type system — using Bahasa Melayu keywords.

Rahsia<T> wraps sensitive data. You can't accidentally log it or send it over the network.
kesan Kripto marks functions that perform cryptographic operations.
masa_tetap ensures code executes in constant time regardless of secret values.

These aren't annotations. They're enforced by the compiler with mathematical proofs.`
            },
            {
              step: '02',
              title: 'Effects Track Side Effects',
              content: `Every function declares its effects in its type signature:

fungsi baca_fail(laluan: Teks) -> Teks kesan Baca + IO

The compiler tracks what effects your code can perform. Security-critical code
can be restricted to specific effects. Cryptographic code? Only kesan Kripto
allowed — no network, no logging. Enforced at compile time.`
            },
            {
              step: '03',
              title: 'The Compiler Proves Security',
              content: `When you compile RIINA code, the compiler proves security properties:

• Information cannot flow from Rahsia to public outputs (non-interference)
• Effects are tracked and gated (effect safety)
• Timing-sensitive code in masa_tetap executes in constant time
• Secrets are zeroed before memory is freed

5,308 theorems verified in Coq. 0 admits. If the proof fails, compilation fails.`
            },
            {
              step: '04',
              title: 'Verified End-to-End',
              content: `RIINA's compiler itself is verified with riinac verify [--fast|--full].
No external CI/CD — verification lives inside the compiler.

The formal proofs (278 Coq files) ship with the compiler. You can audit them.
4 justified axioms — all documented, none hidden.
Every security claim has a machine-checked proof behind it.`
            }
          ].map((item, i) => (
            <div key={i} style={{
              display: 'grid',
              gridTemplateColumns: '80px 1fr',
              gap: '48px',
              marginBottom: '80px'
            }}>
              <div style={{
                fontSize: '48px',
                fontWeight: 200,
                color: '#ddd',
                fontFamily: 'Georgia, serif'
              }}>
                {item.step}
              </div>
              <div>
                <h3 style={{ fontSize: '24px', marginBottom: '16px' }}>{item.title}</h3>
                <pre style={{
                  whiteSpace: 'pre-wrap',
                  fontFamily: 'inherit',
                  color: '#666',
                  lineHeight: 1.8,
                  margin: 0
                }}>
                  {item.content}
                </pre>
              </div>
            </div>
          ))}
        </div>
      </section>

      {/* Type System Deep Dive */}
      <section style={{ padding: '80px 32px', backgroundColor: '#f8f8f8' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto' }}>
          <h2 style={{ fontSize: '32px', marginBottom: '48px' }}>The Type System</h2>

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '32px' }}>
            <div style={{ padding: '24px', backgroundColor: '#fff', border: '1px solid #eee' }}>
              <h4 style={{ fontSize: '14px', letterSpacing: '0.1em', color: '#999', marginBottom: '16px' }}>SECURITY TYPES</h4>
              <code style={{ fontSize: '14px', lineHeight: 2, display: 'block' }}>
                Rahsia&lt;T&gt;<br/>
                Terbuka&lt;T&gt;<br/>
                Mungkin&lt;T&gt;<br/>
                Hasil&lt;T, Ralat&gt;
              </code>
            </div>
            <div style={{ padding: '24px', backgroundColor: '#fff', border: '1px solid #eee' }}>
              <h4 style={{ fontSize: '14px', letterSpacing: '0.1em', color: '#999', marginBottom: '16px' }}>EFFECT TYPES</h4>
              <code style={{ fontSize: '14px', lineHeight: 2, display: 'block' }}>
                kesan IO<br/>
                kesan Baca<br/>
                kesan Tulis<br/>
                kesan Kripto<br/>
                bersih (pure)
              </code>
            </div>
          </div>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // RESEARCH PAGE
  // ============================================================================
  const ResearchPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Research"
        subtitle="RIINA is built on formal verification in Coq, with 5,308 machine-checked theorems across 244 files. Every security property has a proof."
      />

      {/* Stats */}
      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '800px', margin: '0 auto' }}>
          <div style={{
            display: 'grid',
            gridTemplateColumns: '1fr 1fr 1fr 1fr',
            gap: '24px',
            marginBottom: '64px'
          }}>
            {[
              { value: '5,308', label: 'Qed Proofs' },
              { value: '0', label: 'Admits' },
              { value: '5', label: 'Justified Axioms' },
              { value: '278', label: 'Coq Files' },
            ].map((stat, i) => (
              <div key={i} style={{
                textAlign: 'center',
                padding: '24px',
                border: '1px solid #eee'
              }}>
                <div style={{ fontSize: '32px', fontWeight: 300, fontFamily: 'Georgia, serif' }}>{stat.value}</div>
                <div style={{ fontSize: '12px', color: '#999', letterSpacing: '0.1em', textTransform: 'uppercase' }}>{stat.label}</div>
              </div>
            ))}
          </div>

          <h2 style={sectionLabel}>VERIFIED PROPERTIES</h2>

          <div style={{ marginBottom: '64px' }}>
            {[
              {
                title: 'Type Safety',
                desc: 'Progress and preservation theorems. Well-typed programs do not get stuck.',
                status: 'Verified'
              },
              {
                title: 'Non-Interference',
                desc: 'Information flow control. Secret data cannot leak to public outputs. Proven via logical relations.',
                status: 'Verified'
              },
              {
                title: 'Effect Safety',
                desc: 'Algebraic effect system guarantees. Only declared effects can be performed.',
                status: 'Verified'
              },
              {
                title: 'Memory Safety',
                desc: 'No use-after-free, double-free, or buffer overflows. Proven via separation logic.',
                status: 'Verified'
              },
              {
                title: 'Constant-Time Execution',
                desc: 'masa_tetap blocks execute in time independent of secret values.',
                status: 'Verified'
              },
              {
                title: 'Termination',
                desc: 'All pure computations terminate. Strong normalization for the pure fragment.',
                status: 'Verified'
              }
            ].map((paper, i) => (
              <div key={i} style={{
                padding: '24px 0',
                borderBottom: '1px solid #eee',
                display: 'grid',
                gridTemplateColumns: '1fr auto',
                gap: '24px',
                alignItems: 'start'
              }}>
                <div>
                  <h3 style={{ fontSize: '18px', marginBottom: '8px' }}>{paper.title}</h3>
                  <p style={{ color: '#666', fontSize: '14px' }}>{paper.desc}</p>
                </div>
                <span style={{
                  fontSize: '12px',
                  padding: '4px 12px',
                  backgroundColor: '#e8f5e9',
                  color: '#2e7d32',
                  borderRadius: '2px'
                }}>
                  ⊢ {paper.status}
                </span>
              </div>
            ))}
          </div>

          <h2 style={sectionLabel}>26 RESEARCH DOMAINS</h2>

          <div style={{
            display: 'grid',
            gridTemplateColumns: '1fr 1fr',
            gap: '12px',
            marginBottom: '48px'
          }}>
            {[
              { id: 'A', name: 'Core Type Theory & Proofs', desc: 'Type safety, non-interference, logical relations — the mathematical foundation' },
              { id: 'B', name: 'Compiler & Prototype', desc: '13 Rust crates, 612 tests, Bahasa Melayu lexer through C code emission' },
              { id: 'C', name: 'Language Specifications', desc: 'Grammar, AST, type system spec, effect system spec, Bahasa Melayu syntax' },
              { id: 'D–Q', name: 'Attack Surface Research', desc: '14 domains covering networking, UI/UX, data storage, performance, and more — 1,231+ threats enumerated' },
              { id: 'R', name: 'Certified Compilation', desc: 'Translation validation ensuring compiled binary matches source semantics' },
              { id: 'S', name: 'Hardware Contracts', desc: 'CPU side-channel models — Spectre, Meltdown, cache timing formally addressed' },
              { id: 'T', name: 'Hermetic Bootstrap', desc: 'Binary bootstrap from hex0 — trust nothing, build everything from scratch' },
              { id: 'U', name: 'Runtime Guardian', desc: 'Verified micro-hypervisor for runtime protection even on untrusted hardware' },
              { id: 'V', name: 'Termination Guarantees', desc: 'Sized types and strong normalization — pure code provably terminates' },
              { id: 'W', name: 'Verified Memory', desc: 'Separation logic, verified allocator — no use-after-free, no buffer overflow, proven' },
              { id: 'X', name: 'Concurrency Model', desc: 'Session types and data-race freedom — concurrent code that cannot deadlock or race' },
              { id: 'Y', name: 'Verified Standard Library', desc: 'Every stdlib function proven correct — not just tested, mathematically verified' },
              { id: 'Z', name: 'Declassification Policy', desc: 'Robust declassification with budgets — controlled secret release with formal guarantees' },
            ].map((domain, i) => (
              <div key={i} style={{
                padding: '16px 20px',
                backgroundColor: '#f8f8f8',
                display: 'grid',
                gridTemplateColumns: '48px 1fr',
                gap: '12px',
                alignItems: 'start'
              }}>
                <span style={{ fontWeight: 600, fontSize: '13px', color: '#999', fontFamily: 'monospace' }}>{domain.id}</span>
                <div>
                  <div style={{ fontWeight: 600, fontSize: '14px', marginBottom: '4px' }}>{domain.name}</div>
                  <div style={{ fontSize: '13px', color: '#666' }}>{domain.desc}</div>
                </div>
              </div>
            ))}
          </div>

          <h2 style={sectionLabel}>INDUSTRY-SPECIFIC RESEARCH</h2>
          <p style={{ color: '#666', fontSize: '14px', marginBottom: '24px', lineHeight: 1.8 }}>
            Beyond core language research, RIINA maintains dedicated security models for 15 industry verticals —
            each with domain-specific threat models, compliance axioms, and formal verification strategies.
          </p>
          <div style={{
            display: 'grid',
            gridTemplateColumns: '1fr 1fr 1fr',
            gap: '12px',
            marginBottom: '32px'
          }}>
            {[
              'Defence & Military', 'Healthcare', 'Financial Services',
              'Aerospace & Aviation', 'Energy & Utilities', 'Telecommunications',
              'Government', 'Transportation', 'Manufacturing & ERP',
              'Retail & E-Commerce', 'Media & Entertainment', 'Education',
              'Agriculture & AgriTech', 'Real Estate & PropTech', 'Legal & LegalTech',
            ].map((ind, i) => (
              <button key={i}
                onClick={() => setCurrentPage('enterprise')}
                style={{
                  padding: '12px 16px',
                  backgroundColor: '#fff',
                  border: '1px solid #eee',
                  fontSize: '13px',
                  fontWeight: 500,
                  cursor: 'pointer',
                  textAlign: 'left'
                }}
              >
                ⊢ {ind}
              </button>
            ))}
          </div>

          <p style={{
            color: '#666',
            fontSize: '14px'
          }}>
            218 research tracks across 55 domains. 612 Rust tests, 14 crates, 112 example .rii files.
          </p>
        </div>
      </section>

      {/* GitHub */}
      <section style={{
        padding: '80px 32px',
        backgroundColor: '#000',
        color: '#fff',
        textAlign: 'center'
      }}>
        <h2 style={{ fontSize: '32px', fontWeight: 300, marginBottom: '16px' }}>
          Open Source
        </h2>
        <p style={{ color: '#888', marginBottom: '32px' }}>
          MPL-2.0 licensed. Explore the proofs yourself.
        </p>
        <a
          href="https://github.com/ib823/riina"
          style={{
            display: 'inline-block',
            padding: '16px 32px',
            border: '1px solid #fff',
            color: '#fff',
            textDecoration: 'none',
            fontSize: '14px'
          }}
        >
          github.com/ib823/riina
        </a>
      </section>
    </div>
  );

  // ============================================================================
  // DOCUMENTATION PAGE
  // ============================================================================
  const DocsPage = () => {
    const docCards = [
      { title: 'Quick Start', desc: 'Install and compile your first .rii file', page: 'quickStart',
        links: [{ text: 'Installation', page: 'quickStart' }, { text: 'Hello World (hello_dunia.rii)', page: 'examples' }, { text: 'riinac CLI', page: 'quickStart' }] },
      { title: 'Language Guide', desc: 'Learn RIINA from the ground up', page: 'syntax',
        links: [{ text: 'Bahasa Melayu Syntax', page: 'syntax' }, { text: 'Security Types', page: 'securityTypes' }, { text: 'Effect System', page: 'effectSystem' }] },
      { title: 'Bahasa Melayu Reference', desc: 'Complete keyword and syntax reference', page: 'syntax',
        links: [{ text: 'Keyword Table (60+)', page: 'syntax' }, { text: 'Security Keywords', page: 'securityTypes' }, { text: 'Effect Keywords', page: 'effectSystem' }] },
      { title: 'Standard Library', desc: '88 builtins across 9 modules', page: 'stdlib',
        links: [{ text: 'Module Reference', page: 'stdlib' }, { text: 'std::kripto', page: 'stdlib' }, { text: 'std::io', page: 'stdlib' }] },
      { title: 'Formal Proofs', desc: '278 Coq files, 5,308 theorems', page: 'research',
        links: [{ text: 'Proof Architecture', page: 'research' }, { text: 'Axiom Justifications', page: 'research' }, { text: 'Building Proofs', page: 'research' }] },
      { title: 'Examples', desc: '112 example .rii files in 9 categories', page: 'examples',
        links: [{ text: 'pengesahan.rii', page: 'examples' }, { text: 'kripto.rii', page: 'examples' }, { text: 'hello_dunia.rii', page: 'examples' }] },
    ];

    return (
      <div style={pageTopStyle}>
        <section style={{ padding: '80px 32px', maxWidth: '1200px', margin: '0 auto' }}>
          <h1 style={{ fontSize: '48px', fontWeight: 300, marginBottom: '48px' }}>
            Documentation
          </h1>

          <div className="grid-3" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '32px' }}>
            {docCards.map((section, i) => (
              <div key={i} style={{
                padding: '32px',
                border: '1px solid #eee',
                cursor: 'pointer',
                transition: 'border-color 0.2s'
              }}
              onClick={() => setCurrentPage(section.page)}
              >
                <h3 style={{ fontSize: '18px', marginBottom: '8px' }}>{section.title}</h3>
                <p style={{ color: '#666', fontSize: '14px', marginBottom: '20px' }}>{section.desc}</p>
                <div style={{ display: 'flex', flexDirection: 'column', gap: '8px' }}>
                  {section.links.map((link, j) => (
                    <button key={j}
                      onClick={(e) => { e.stopPropagation(); setCurrentPage(link.page); }}
                      style={{
                        background: 'none',
                        border: 'none',
                        cursor: 'pointer',
                        color: '#000',
                        fontSize: '14px',
                        textDecoration: 'none',
                        textAlign: 'left',
                        padding: 0
                      }}
                    >
                      → {link.text}
                    </button>
                  ))}
                </div>
              </div>
            ))}
          </div>
        </section>
      </div>
    );
  };

  // ============================================================================
  // QUICK START PAGE (Developers → Quick Start)
  // ============================================================================
  const QuickStartPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Quick Start"
        subtitle="Install RIINA and compile your first provably secure program."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto' }}>
          <h2 style={sectionLabel}>INSTALLATION</h2>

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '24px', marginBottom: '64px' }}>
            <div style={cardStyle}>
              <h3 style={{ fontSize: '16px', marginBottom: '12px' }}>From Source</h3>
              <pre style={{ ...codeBlockStyle, padding: '16px' }}>
{`git clone https://github.com/ib823/riina.git
cd proof/03_PROTO
cargo build --release`}
              </pre>
            </div>
            <div style={cardStyle}>
              <h3 style={{ fontSize: '16px', marginBottom: '12px' }}>Docker</h3>
              <pre style={{ ...codeBlockStyle, padding: '16px' }}>
{`docker build -t riina .
docker run --rm riina check myfile.rii`}
              </pre>
            </div>
            <div style={cardStyle}>
              <h3 style={{ fontSize: '16px', marginBottom: '12px' }}>Nix Flake</h3>
              <pre style={{ ...codeBlockStyle, padding: '16px' }}>
{`nix run github:ib823/riina`}
              </pre>
            </div>
            <div style={cardStyle}>
              <h3 style={{ fontSize: '16px', marginBottom: '12px' }}>Portable Installer</h3>
              <pre style={{ ...codeBlockStyle, padding: '16px' }}>
{`curl -sSf https://ib823.github.io/riina/install.sh | bash
# or: bash scripts/install.sh`}
              </pre>
            </div>
          </div>

          <h2 style={sectionLabel}>HELLO WORLD</h2>
          <p style={{ color: '#666', marginBottom: '16px', fontSize: '14px' }}>Create <code>hello.rii</code>:</p>
          <pre style={{ ...codeBlockStyle, marginBottom: '24px' }}>
{`// hello.rii — Your first RIINA program
modul hello;
guna std::io;

awam fungsi utama() -> kesan Tulis {
    biar mesej = "Selamat datang ke RIINA!";
    laku Tulis cetak_baris(mesej);
}`}
          </pre>
          <p style={{ color: '#666', marginBottom: '16px', fontSize: '14px' }}>Compile and run:</p>
          <pre style={{ ...codeBlockStyle, marginBottom: '64px' }}>
{`riinac check hello.rii    # Type-check + verify security properties
riinac run hello.rii      # Run directly
riinac build hello.rii    # Compile to native binary via C`}
          </pre>

          <h2 style={sectionLabel}>RIINAC CLI COMMANDS</h2>
          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '12px' }}>
            {[
              { cmd: 'riinac check', desc: 'Type-check and verify security properties' },
              { cmd: 'riinac run', desc: 'Execute .rii file directly' },
              { cmd: 'riinac build', desc: 'Compile to native binary via C backend' },
              { cmd: 'riinac emit-c', desc: 'Generate C source code' },
              { cmd: 'riinac emit-ir', desc: 'Generate intermediate representation' },
              { cmd: 'riinac repl', desc: 'Interactive REPL mode' },
              { cmd: 'riinac fmt', desc: 'Format RIINA source code' },
              { cmd: 'riinac doc', desc: 'Generate HTML documentation' },
              { cmd: 'riinac lsp', desc: 'Language server for VS Code and editors' },
              { cmd: 'riinac verify --fast', desc: 'Quick verification gate (pre-commit)' },
              { cmd: 'riinac verify --full', desc: 'Full verification gate (pre-push)' },
              { cmd: 'riinac pkg init', desc: 'Initialize new package' },
              { cmd: 'riinac pkg add', desc: 'Add dependency' },
              { cmd: 'riinac pkg build', desc: 'Build package with dependencies' },
              { cmd: 'riinac pkg publish', desc: 'Publish to registry' },
            ].map((c, i) => (
              <div key={i} style={{ padding: '12px 16px', backgroundColor: '#f8f8f8', display: 'flex', gap: '16px' }}>
                <code style={{ fontWeight: 600, fontSize: '13px', whiteSpace: 'nowrap' }}>{c.cmd}</code>
                <span style={{ color: '#666', fontSize: '13px' }}>{c.desc}</span>
              </div>
            ))}
          </div>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // STANDARD LIBRARY PAGE (Developers → Standard Library)
  // ============================================================================
  const StdLibPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Standard Library"
        subtitle="88 builtins across 9 modules. All functions have bilingual names (Bahasa Melayu and English). Effect-gated I/O — pure functions cannot perform side effects."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          {[
            { mod: 'teks', en: 'String', desc: 'String manipulation', fns: [
              'panjang / length', 'gabung / concat', 'potong / trim', 'pecah / split',
              'ganti / replace', 'mengandungi / contains', 'bermula_dengan / starts_with',
              'berakhir_dengan / ends_with', 'ke_huruf_besar / to_uppercase', 'ke_huruf_kecil / to_lowercase'
            ]},
            { mod: 'senarai', en: 'List/Vec', desc: 'Dynamic arrays', fns: [
              'tolak / push', 'cabut / pop', 'panjang / len', 'peta / map', 'tapis / filter',
              'lipat / fold', 'isih / sort', 'terbalik / reverse', 'cari / find', 'semua / all',
              'mana_mana / any', 'zip / zip', 'rata / flatten'
            ]},
            { mod: 'peta', en: 'Map/HashMap', desc: 'Key-value collections', fns: [
              'masuk / insert', 'dapatkan / get', 'buang / remove', 'mengandungi_kunci / contains_key',
              'kunci / keys', 'nilai / values', 'pasangan / entries', 'panjang / len'
            ]},
            { mod: 'set', en: 'Set', desc: 'Unique collections', fns: [
              'masuk / insert', 'buang / remove', 'mengandungi / contains',
              'kesatuan / union', 'persilangan / intersection', 'beza / difference'
            ]},
            { mod: 'matematik', en: 'Math', desc: 'Arithmetic and numeric functions', fns: [
              'mutlak / abs', 'min / min', 'max / max', 'kuasa / pow', 'punca / sqrt',
              'log / log', 'sin / sin', 'kos / cos', 'bundar / round', 'lantai / floor', 'siling / ceil'
            ]},
            { mod: 'penukaran', en: 'Conversion', desc: 'Type conversions', fns: [
              'ke_teks / to_string', 'hurai_nombor / parse_int', 'hurai_pecahan / parse_float',
              'benar_ke_nombor / bool_to_int', 'ke_bait / to_bytes', 'dari_bait / from_bytes'
            ]},
            { mod: 'ujian', en: 'Testing', desc: 'Unit testing framework', fns: [
              'tegaskan / assert', 'tegaskan_sama / assert_eq', 'tegaskan_tak_sama / assert_ne',
              'tegaskan_ralat / assert_err', 'panik / panic', 'jangka_panik / expect_panic'
            ]},
            { mod: 'masa', en: 'Time', desc: 'Time and duration', fns: [
              'sekarang / now', 'cap_masa / timestamp', 'tempoh / duration',
              'format / format', 'hurai / parse', 'tidur / sleep'
            ]},
            { mod: 'fail', en: 'File', desc: 'File I/O (effect-gated)', fns: [
              'baca / read', 'tulis / write', 'wujud / exists', 'padam / delete',
              'senarai_dir / list_dir', 'buat_dir / create_dir', 'laluan / path'
            ]},
          ].map((m, i) => (
            <div key={i} style={{ marginBottom: '32px', padding: '24px', border: '1px solid #eee' }}>
              <div style={{ display: 'flex', alignItems: 'baseline', gap: '12px', marginBottom: '12px' }}>
                <code style={{ fontSize: '18px', fontWeight: 600 }}>std::{m.mod}</code>
                <span style={{ color: '#999', fontSize: '13px' }}>({m.en})</span>
                <span style={{ color: '#666', fontSize: '13px' }}>— {m.desc}</span>
              </div>
              <div style={{ display: 'flex', flexWrap: 'wrap', gap: '8px' }}>
                {m.fns.map((fn, j) => (
                  <code key={j} style={{
                    fontSize: '12px',
                    padding: '4px 8px',
                    backgroundColor: '#f8f8f8',
                    border: '1px solid #eee'
                  }}>{fn}</code>
                ))}
              </div>
            </div>
          ))}

          <p style={{ color: '#666', fontSize: '14px', marginTop: '16px' }}>
            All I/O functions require appropriate effect annotations (<code>kesan Baca</code>, <code>kesan Tulis</code>, etc.).
            Pure functions (<code>kesan Bersih</code>) cannot call effect-gated functions.
          </p>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // CONTRIBUTING PAGE (Community → Contributing)
  // ============================================================================
  const ContributingPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Contributing"
        subtitle="RIINA is open source under MPL-2.0. Contributions to the compiler, proofs, standard library, and documentation are welcome."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto' }}>
          <h2 style={sectionLabel}>SETUP</h2>
          <pre style={{ ...codeBlockStyle, marginBottom: '48px' }}>
{`# Clone the repository
git clone https://github.com/ib823/riina.git
cd proof

# Install dependencies
cd 00_SETUP/scripts
chmod +x install_coq.sh install_rust.sh verify_setup.sh
./install_rust.sh       # Rust toolchain
./install_coq.sh        # Rocq 9.1 (Coq 8.21)
./verify_setup.sh       # Verify everything works

# Build Coq proofs
cd ../../02_FORMAL/coq && make

# Build Rust prototype
cd ../../03_PROTO && cargo build --all

# Run all tests
cargo test --all        # 612 tests, all must pass`}
          </pre>

          <h2 style={sectionLabel}>COMMIT FORMAT</h2>
          <pre style={{ ...codeBlockStyle, marginBottom: '48px' }}>
{`[TRACK_X] TYPE: Brief description

Tracks: A (Proofs), B (Compiler), C (Specs), F (Tooling), ALL
Types:  PROOF, IMPL, FIX, DOCS, REFACTOR

Examples:
[TRACK_A] PROOF: Complete Progress lemma for function application
[TRACK_B] IMPL: Lexer tokenizes Bahasa Melayu keywords
[TRACK_F] FIX: Constant-time comparison in HMAC verify`}
          </pre>

          <h2 style={sectionLabel}>VERIFICATION GATES</h2>
          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '24px', marginBottom: '48px' }}>
            <div style={cardStyle}>
              <h3 style={{ fontSize: '16px', marginBottom: '8px' }}>Pre-Commit (Fast)</h3>
              <pre style={{ ...codeBlockStyle, padding: '16px' }}>
{`riinac verify --fast
cargo test --all
cargo clippy -- -D warnings`}
              </pre>
            </div>
            <div style={cardStyle}>
              <h3 style={{ fontSize: '16px', marginBottom: '8px' }}>Pre-Push (Full)</h3>
              <pre style={{ ...codeBlockStyle, padding: '16px' }}>
{`riinac verify --full
cd 02_FORMAL/coq && make clean && make
grep -r "Admitted" *.v  # Must be empty`}
              </pre>
            </div>
          </div>

          <h2 style={sectionLabel}>RULES</h2>
          <ul style={{ listStyle: 'none', padding: 0 }}>
            {[
              'All Coq proofs must compile with 0 Admitted',
              'All Rust tests must pass (612+)',
              'No unsafe Rust without documented justification',
              'No third-party crypto dependencies (zero supply chain trust)',
              'Use Bahasa Melayu keywords in all .rii examples',
              'Cross-reference Track A proofs with Track B implementations',
            ].map((rule, i) => (
              <li key={i} style={{ padding: '12px 0', borderBottom: '1px solid #eee', color: '#333', fontSize: '14px' }}>
                <span style={{ marginRight: '8px' }}>⊢</span>{rule}
              </li>
            ))}
          </ul>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // LICENSE PAGE (Legal → MPL-2.0)
  // ============================================================================
  const LicensePage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="MPL-2.0 License"
        subtitle="RIINA is licensed under the Mozilla Public License 2.0 with the 'Incompatible With Secondary Licenses' notice."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '900px', margin: '0 auto' }}>
          <h2 style={sectionLabel}>SUMMARY</h2>

          <div className="grid-3" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '24px', marginBottom: '64px' }}>
            <div style={cardStyle}>
              <h3 style={{ fontSize: '14px', color: '#2e7d32', marginBottom: '12px' }}>PERMISSIONS</h3>
              <ul style={{ listStyle: 'none', padding: 0, fontSize: '14px', color: '#666' }}>
                {['Commercial use', 'Modification', 'Distribution', 'Patent use', 'Private use'].map((p, i) => (
                  <li key={i} style={{ padding: '4px 0' }}>+ {p}</li>
                ))}
              </ul>
            </div>
            <div style={cardStyle}>
              <h3 style={{ fontSize: '14px', color: '#e65100', marginBottom: '12px' }}>CONDITIONS</h3>
              <ul style={{ listStyle: 'none', padding: 0, fontSize: '14px', color: '#666' }}>
                {['Disclose source (file-level)', 'Same license for modified files', 'Copyright notice preserved'].map((c, i) => (
                  <li key={i} style={{ padding: '4px 0' }}>~ {c}</li>
                ))}
              </ul>
            </div>
            <div style={cardStyle}>
              <h3 style={{ fontSize: '14px', color: '#c62828', marginBottom: '12px' }}>LIMITATIONS</h3>
              <ul style={{ listStyle: 'none', padding: 0, fontSize: '14px', color: '#666' }}>
                {['No liability', 'No warranty', 'No trademark rights'].map((l, i) => (
                  <li key={i} style={{ padding: '4px 0' }}>- {l}</li>
                ))}
              </ul>
            </div>
          </div>

          <h2 style={sectionLabel}>INCOMPATIBLE WITH SECONDARY LICENSES</h2>
          <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.8, marginBottom: '48px' }}>
            This Source Code Form is "Incompatible With Secondary Licenses" as defined by
            the Mozilla Public License, v. 2.0. This means the code <strong>cannot be relicensed
            under GPL, AGPL, or LGPL</strong>. This is a deliberate choice to prevent license
            capture and maintain RIINA's permissive distribution model.
          </p>

          <h2 style={sectionLabel}>APPLIES TO</h2>
          <div style={{ display: 'flex', flexWrap: 'wrap', gap: '12px', marginBottom: '48px' }}>
            {['Compiler (riinac)', 'Formal Proofs (Coq)', 'Standard Library', 'Tooling', 'Examples', 'Documentation'].map((item, i) => (
              <span key={i} style={{
                padding: '8px 16px',
                backgroundColor: '#f8f8f8',
                border: '1px solid #eee',
                fontSize: '14px'
              }}>{item}</span>
            ))}
          </div>

          <a
            href="https://github.com/ib823/riina/blob/main/LICENSE"
            style={{
              display: 'inline-block',
              padding: '14px 28px',
              border: '1px solid #000',
              color: '#000',
              textDecoration: 'none',
              fontSize: '14px'
            }}
          >
            Read full LICENSE on GitHub
          </a>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // PRIVACY PAGE (Legal → Privacy)
  // ============================================================================
  const PrivacyPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Privacy"
        subtitle="RIINA respects your privacy completely."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '800px', margin: '0 auto' }}>
          <div style={{ ...cardStyle, padding: '48px' }}>
            <h2 style={{ fontSize: '24px', fontWeight: 400, marginBottom: '24px' }}>No data collection</h2>
            <ul style={{ listStyle: 'none', padding: 0 }}>
              {[
                'This is a static website. No server-side processing.',
                'No cookies are set or read.',
                'No analytics or tracking scripts.',
                'No user data is collected, stored, or transmitted.',
                'No third-party services are loaded.',
                'The RIINA compiler (riinac) does not phone home or collect telemetry.',
              ].map((item, i) => (
                <li key={i} style={{ padding: '12px 0', borderBottom: '1px solid #eee', color: '#666', fontSize: '14px' }}>
                  {item}
                </li>
              ))}
            </ul>
          </div>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // TERMS PAGE (Legal → Terms)
  // ============================================================================
  const TermsPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Terms"
        subtitle="Terms of use for the RIINA website and software."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '800px', margin: '0 auto' }}>
          <div style={{ ...cardStyle, padding: '48px' }}>
            <h2 style={{ fontSize: '20px', fontWeight: 500, marginBottom: '16px' }}>Software License</h2>
            <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.8, marginBottom: '32px' }}>
              RIINA is distributed under the Mozilla Public License 2.0 (MPL-2.0).
              See the <button onClick={() => setCurrentPage('license')} style={{ background: 'none', border: 'none', cursor: 'pointer', textDecoration: 'underline', color: '#000', fontSize: '14px', padding: 0 }}>License page</button> for details.
            </p>

            <h2 style={{ fontSize: '20px', fontWeight: 500, marginBottom: '16px' }}>No Warranty</h2>
            <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.8, marginBottom: '32px' }}>
              Covered Software is provided under this License on an "as is" basis, without warranty
              of any kind, either expressed, implied, or statutory, including, without limitation,
              warranties that the Covered Software is free of defects, merchantable, fit for a
              particular purpose or non-infringing.
            </p>

            <h2 style={{ fontSize: '20px', fontWeight: 500, marginBottom: '16px' }}>Limitation of Liability</h2>
            <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.8 }}>
              Under no circumstances and under no legal theory, whether tort (including negligence),
              contract, or otherwise, shall any Contributor be liable to any person for any direct,
              indirect, special, incidental, or consequential damages of any character.
            </p>
          </div>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // DEMOS PAGE
  // ============================================================================
  const DemosPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Demos"
        subtitle="Working demonstrations of RIINA's compile-time security guarantees. Every demo compiles and runs today."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '1000px', margin: '0 auto' }}>
          <h2 style={sectionLabel}>LIVE TERMINAL OUTPUT</h2>
          <p style={{ color: '#666', fontSize: '14px', marginBottom: '32px' }}>
            Pre-recorded output from <code style={{ backgroundColor: '#f0f0f0', padding: '2px 6px' }}>riinac run</code> on actual demo files.
          </p>

          {[
            { name: 'selamat_datang.rii', title: 'Hello Malaysia', desc: 'Basic output and string formatting',
              output: `$ riinac run 07_EXAMPLES/demos/selamat_datang.rii
Selamat datang ke RIINA!
Hello, Dunia!
RIINA: Rigorous Immutable Invariant, No Assumptions` },
            { name: 'faktorial.rii', title: 'Recursive Factorial', desc: 'Recursive functions via LetRec + FixClosure',
              output: `$ riinac run 07_EXAMPLES/demos/faktorial.rii
faktorial(0) = 1
faktorial(1) = 1
faktorial(5) = 120
faktorial(10) = 3628800
faktorial(20) = 2432902008176640000` },
            { name: 'pasangan.rii', title: 'Safe Pairs', desc: 'Type-safe tuple access',
              output: `$ riinac run 07_EXAMPLES/demos/pasangan.rii
Pasangan: (Ahmad, 25)
Nama: Ahmad
Umur: 25
Jumlah: 3` },
            { name: 'rahsia_dijaga.rii', title: 'Secret Types', desc: 'Rahsia<T> prevents secret leakage',
              output: `$ riinac run 07_EXAMPLES/demos/rahsia_dijaga.rii
Kata laluan diterima (panjang: 12)
Hash: [RAHSIA - tidak boleh cetak]
Pengesahan: berjaya` },
            { name: 'kalkulator_c.rii', title: 'C FFI', desc: 'Calling C functions from RIINA via luaran "C"',
              output: `$ riinac build 07_EXAMPLES/demos/kalkulator_c.rii && ./output
Hello from RIINA via C FFI!
abs(-42) = 42
rand() = 1804289383` },
          ].map((demo, i) => (
            <div key={i} style={{ marginBottom: '32px' }}>
              <div style={{ marginBottom: '8px' }}>
                <span style={{ fontSize: '16px', fontWeight: 600 }}>{demo.title}</span>
                <span style={{ color: '#999', fontSize: '14px', marginLeft: '12px' }}>{demo.desc}</span>
              </div>
              <pre style={{
                ...codeBlockStyle,
                color: '#4af626',
                fontSize: '13px',
                lineHeight: 1.6,
                padding: '20px 24px'
              }}>
{demo.output}
              </pre>
            </div>
          ))}

          <h2 style={{ ...sectionLabel, marginTop: '64px' }}>SHOWCASE APPLICATIONS</h2>
          <p style={{ color: '#666', fontSize: '14px', marginBottom: '32px' }}>
            Three production-grade applications demonstrating compiler-proven security properties.
          </p>

          <div style={{ marginBottom: '48px' }}>
            <h3 style={{ fontSize: '20px', fontWeight: 400, marginBottom: '8px' }}>
              Provably Secure Web Server
            </h3>
            <p style={{ color: '#666', fontSize: '14px', marginBottom: '16px' }}>
              The compiler PROVES: no SQL injection, no XSS, no path traversal, no secret leakage, no timing attacks.
            </p>
            <pre className="code-block" style={codeBlockStyle}>
{`// pelayan_web_selamat.rii
modul pelayan_web_selamat;
guna std::io;

bentuk Permintaan {
    kaedah: Teks,
    laluan: LaluanSelamat,        // Path traversal impossible by type
    badan: TeksHtmlSelamat,       // XSS impossible by type
}

fungsi kendalikan(permintaan: Permintaan, db: Pangkalan)
    -> Respons kesan Baca + Tulis {
    biar pertanyaan = sql_selamat("SELECT * FROM pengguna WHERE id = ?", permintaan.laluan);
    // Returns TeksSqlSelamat — injection impossible by construction
    biar data = db.laksana(pertanyaan);
    pulang Respons::ok(html_selamat(data));
}

// Compile result:
// ⊢ No SQL injection (TeksSqlSelamat)
// ⊢ No XSS (TeksHtmlSelamat)
// ⊢ No path traversal (LaluanSelamat)
// ⊢ Effects tracked (kesan Baca + Tulis)`}
            </pre>
          </div>

          <div style={{ marginBottom: '48px' }}>
            <h3 style={{ fontSize: '20px', fontWeight: 400, marginBottom: '8px' }}>
              Post-Quantum Encrypted Messenger
            </h3>
            <p style={{ color: '#666', fontSize: '14px', marginBottom: '16px' }}>
              ML-KEM-1024 key encapsulation, ML-DSA-87 signatures, ChaCha20-Poly1305 AEAD. Compiler proves keys are zeroized and no plaintext leaks.
            </p>
            <pre className="code-block" style={codeBlockStyle}>
{`// utusan_pasca_kuantum.rii
modul utusan_pasca_kuantum;
guna std::kripto;

fungsi hantar_mesej(
    kunci_awam: KunciAwamMLKEM,
    mesej: Rahsia<Teks>
) -> MesejSulit kesan Kripto {
    masa_tetap {
        biar (kunci_sesi, teks_sifer) = mlkem_1024::enkapsulasi(kunci_awam);
        biar nonce = jana_nonce_monotonik();
        biar sulit = chacha20_poly1305::sulit(kunci_sesi, nonce, mesej);
        sifar_kan(kunci_sesi);  // Compiler enforces zeroization
        pulang MesejSulit { teks_sifer, nonce, sulit };
    }
}

// Compile result:
// ⊢ Key zeroization enforced (sifar_kan)
// ⊢ No plaintext leakage (Rahsia type)
// ⊢ Constant-time execution (masa_tetap)
// ⊢ Monotonic nonce (no reuse)`}
            </pre>
          </div>

          <div style={{ marginBottom: '48px' }}>
            <h3 style={{ fontSize: '20px', fontWeight: 400, marginBottom: '8px' }}>
              HIPAA-Compliant Medical Records
            </h3>
            <p style={{ color: '#666', fontSize: '14px', marginBottom: '16px' }}>
              PHI (Protected Health Information) handling with role-based access control, audit trails, and de-identification. Compiler proves PHI never escapes authorized scope.
            </p>
            <pre className="code-block" style={codeBlockStyle}>
{`// rekod_perubatan_hipaa.rii
modul rekod_perubatan_hipaa;

bentuk RekodPerubatan {
    id_pesakit: Teks,
    nama: PHI<Teks>,           // Protected Health Information
    diagnosis: PHI<Teks>,
    ubatan: PHI<Senarai<Teks>>,
}

fungsi akses_rekod(
    pengguna: Pengguna,
    rekod: RekodPerubatan,
    log: LogAudit
) -> Keputusan<PHI<Teks>> kesan Baca + Tulis {
    kalau !semak_peranan(pengguna, Peranan::Doktor) {
        log.catat(pengguna, "DITOLAK", rekod.id_pesakit);
        pulang Keputusan::Gagal("Akses ditolak");
    }
    log.catat(pengguna, "AKSES", rekod.id_pesakit);
    pulang Keputusan::Ok(rekod.diagnosis);
}

// Compile result:
// ⊢ PHI never escapes without authorization
// ⊢ All access audited (LogAudit)
// ⊢ Role-based access enforced at type level`}
            </pre>
          </div>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // ENTERPRISE PAGE
  // ============================================================================
  const EnterprisePage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Enterprise"
        subtitle="Write code. Get compliance proofs. Machine-checkable certificates across 15 regulatory frameworks, 15 industries, and 218 research tracks — every angle covered."
      />

      <section style={{ padding: '0 32px 80px' }}>
        <div style={{ maxWidth: '1100px', margin: '0 auto' }}>
          <h2 style={sectionLabel}>COMPLIANCE AUTOMATION</h2>
          <p style={{ color: '#666', fontSize: '16px', marginBottom: '32px', lineHeight: 1.8 }}>
            RIINA programs carry machine-checkable proof certificates that satisfy regulatory requirements.
            When you compile a RIINA program, the compiler generates a compliance report mapping your code's
            proven properties to specific regulatory controls. No manual audit. No "trust us". Mathematical proof.
          </p>

          {/* Industry verticals */}
          <h2 style={sectionLabel}>15 INDUSTRY VERTICALS — PROVEN SECURITY FOR YOUR DOMAIN</h2>
          <p style={{ color: '#666', fontSize: '14px', marginBottom: '32px', lineHeight: 1.8 }}>
            RIINA doesn't just cover generic compliance. We built dedicated security models for each industry —
            with formal axioms, domain-specific types, and compiler-proven properties tailored to your exact regulatory landscape.
          </p>

          <div className="grid-3" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '20px', marginBottom: '64px' }}>
            {[
              { icon: '⊢', industry: 'Defence & Military', regs: 'CMMC, ITAR, NIST 800-171',
                desc: 'Classified data handling with proven compartmentalization. CUI isolation enforced at the type level. Cross-domain guard verification. Side-channel resistance for signals intelligence. Formal evidence for DISA STIG compliance.' },
              { icon: '⊢', industry: 'Healthcare', regs: 'HIPAA, HITECH, HL7 FHIR',
                desc: 'PHI (Protected Health Information) wrapped in security types that mathematically prevent unauthorized disclosure. Audit trails proven complete. De-identification verified at compile time. Break-glass access with proof-carrying authorization.' },
              { icon: '⊢', industry: 'Financial Services', regs: 'PCI-DSS, SOX, BNM RMiT, MAS TRM',
                desc: 'Cardholder data isolation proven by construction. Transaction integrity with formal audit trails. Anti-money laundering data flows verified. Constant-time operations prevent timing attacks on financial algorithms.' },
              { icon: '⊢', industry: 'Aerospace & Aviation', regs: 'DO-178C DAL A, DO-326A',
                desc: 'Flight-critical software with formal verification evidence satisfying DAL A requirements. Deterministic execution proven. WCET bounds verified. No undefined behavior — mathematically guaranteed. Airborne cyber security per DO-326A.' },
              { icon: '⊢', industry: 'Energy & Utilities', regs: 'NERC CIP, IEC 62351',
                desc: 'SCADA/ICS control system isolation proven at the type level. Critical infrastructure command validation. Provable network segmentation between OT and IT. Smart grid firmware with verified sensor input sanitization.' },
              { icon: '⊢', industry: 'Telecommunications', regs: 'NESAS, 3GPP TS 33.501',
                desc: '5G network function security with proven signaling isolation. SIM credential handling in Rahsia types. Lawful intercept interface formally verified. Roaming security with proven cross-operator boundaries.' },
              { icon: '⊢', industry: 'Government & GovTech', regs: 'FedRAMP, NIST 800-53, MyDIGITAL',
                desc: 'Sovereign data residency proven by effect tracking — data cannot leave approved boundaries. Citizen PII protection with formal declassification gates. e-Government service security with proven access controls.' },
              { icon: '⊢', industry: 'Transportation', regs: 'ISO 26262 ASIL-D, UNECE WP.29',
                desc: 'Automotive ECU firmware with ASIL-D systematic capability evidence. Autonomous vehicle decision logic formally verified. V2X communication security with proven message authenticity. Railway CENELEC EN 50128 SIL 4 evidence.' },
              { icon: '⊢', industry: 'Manufacturing & ERP', regs: 'IEC 62443, ISA/IEC 99',
                desc: 'Industrial control system security with proven PLC command validation. ERP data flow isolation — financial, HR, and production data provably separated. Supply chain data integrity with formal provenance tracking. Industry 4.0 digital twin security.' },
              { icon: '⊢', industry: 'Retail & E-Commerce', regs: 'PCI-DSS, CCPA, PDPA',
                desc: 'Payment processing where cardholder data literally cannot leak — proven by the compiler. Consumer data rights (opt-out, deletion) enforced at the type level. Inventory and pricing integrity with formal audit trails.' },
              { icon: '⊢', industry: 'Media & Entertainment', regs: 'DMCA, DRM, COPPA',
                desc: 'Digital rights management with formally verified access controls. Content delivery with proven geo-restriction enforcement. Age-gated content with provable verification. Ad-tech data isolation preventing unauthorized profiling.' },
              { icon: '⊢', industry: 'Education', regs: 'FERPA, COPPA, PDPA',
                desc: 'Student records wrapped in security types that prevent unauthorized disclosure. Learning analytics with proven de-identification. Exam integrity with formally verified proctoring boundaries. Research data compartmentalization.' },
              { icon: '⊢', industry: 'Agriculture & AgriTech', regs: 'FDA 21 CFR, IoT Security',
                desc: 'Precision agriculture sensor firmware with proven input validation. Crop data and yield analytics with formal integrity guarantees. Livestock tracking with tamper-proof audit trails. Drone flight control with verified safety boundaries.' },
              { icon: '⊢', industry: 'Real Estate & PropTech', regs: 'AML, PDPA, SOX',
                desc: 'Property transaction integrity with proven audit trails. Tenant PII protection enforced at the type level. Smart building IoT with formally verified access controls. Anti-money laundering data flows for property transactions provably tracked.' },
              { icon: '⊢', industry: 'Legal & LegalTech', regs: 'Attorney-Client Privilege, GDPR, eIDAS',
                desc: 'Privileged communication provably isolated — the compiler mathematically guarantees no cross-matter data leakage. Document management with proven chain of custody. e-Discovery with formally verified data boundaries. Digital signature verification per eIDAS.' },
            ].map((ind, i) => (
              <div key={i} style={{
                padding: '24px',
                border: '1px solid #eee',
                transition: 'border-color 0.2s',
              }}>
                <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'baseline', marginBottom: '8px' }}>
                  <span style={{ fontWeight: 600, fontSize: '15px' }}>{ind.icon} {ind.industry}</span>
                </div>
                <div style={{ fontSize: '11px', color: '#999', letterSpacing: '0.05em', marginBottom: '12px' }}>{ind.regs}</div>
                <p style={{ color: '#666', fontSize: '13px', lineHeight: 1.7, margin: 0 }}>{ind.desc}</p>
              </div>
            ))}
          </div>

          {/* Regulatory frameworks */}
          <h2 style={sectionLabel}>15 REGULATORY FRAMEWORKS — MACHINE-CHECKABLE COMPLIANCE</h2>
          <div className="grid-3" style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '16px', marginBottom: '48px' }}>
            {[
              { reg: 'HIPAA', jurisdiction: 'United States', coverage: 'PHI access control, audit trails, encryption' },
              { reg: 'PCI-DSS', jurisdiction: 'Global', coverage: 'Cardholder data isolation, key management' },
              { reg: 'GDPR', jurisdiction: 'European Union', coverage: 'Data minimization, purpose limitation, erasure' },
              { reg: 'PDPA (MY)', jurisdiction: 'Malaysia', coverage: 'Personal data protection, cross-border transfer' },
              { reg: 'PDPA (SG)', jurisdiction: 'Singapore', coverage: 'Data protection, breach notification' },
              { reg: 'SOX', jurisdiction: 'United States', coverage: 'Financial data integrity, audit trails' },
              { reg: 'DO-178C', jurisdiction: 'Aviation', coverage: 'Deterministic execution, formal verification' },
              { reg: 'ISO 26262', jurisdiction: 'Automotive', coverage: 'ASIL-D systematic capability' },
              { reg: 'CC EAL7', jurisdiction: 'International', coverage: 'Formally verified design' },
              { reg: 'NIST 800-53', jurisdiction: 'United States', coverage: 'Security controls (AC, AU, SC)' },
              { reg: 'CCPA', jurisdiction: 'California', coverage: 'Consumer data rights, sale opt-out' },
              { reg: 'FERPA', jurisdiction: 'United States', coverage: 'Student record protection' },
              { reg: 'BNM RMiT', jurisdiction: 'Malaysia', coverage: 'Financial technology risk management' },
              { reg: 'MAS TRM', jurisdiction: 'Singapore', coverage: 'Technology risk management' },
              { reg: 'ISO 27001', jurisdiction: 'International', coverage: 'Information security management' },
            ].map((r, i) => (
              <div key={i} style={{ ...cardStyle, padding: '16px' }}>
                <div style={{ display: 'flex', justifyContent: 'space-between', marginBottom: '4px' }}>
                  <span style={{ fontWeight: 600, fontSize: '14px' }}>{r.reg}</span>
                  <span style={{ color: '#999', fontSize: '11px' }}>{r.jurisdiction}</span>
                </div>
                <p style={{ color: '#666', fontSize: '12px', margin: 0 }}>{r.coverage}</p>
              </div>
            ))}
          </div>

          {/* Research depth */}
          <div style={{
            backgroundColor: '#000',
            color: '#fff',
            padding: '48px',
            marginBottom: '48px'
          }}>
            <h2 style={{ fontSize: '14px', letterSpacing: '0.2em', color: '#666', marginBottom: '24px' }}>
              RESEARCH DEPTH
            </h2>
            <div className="grid-4" style={{ display: 'grid', gridTemplateColumns: 'repeat(4, 1fr)', gap: '32px', marginBottom: '32px' }}>
              {[
                { value: '218', label: 'Research Tracks' },
                { value: '1,231+', label: 'Threats Modeled' },
                { value: '15', label: 'Industries' },
                { value: '26+', label: 'Research Domains (A–Z)' },
              ].map((stat, i) => (
                <div key={i} style={{ textAlign: 'center' }}>
                  <div style={{ fontSize: '36px', fontWeight: 300, fontFamily: 'Georgia, serif' }}>{stat.value}</div>
                  <div style={{ fontSize: '11px', color: '#888', letterSpacing: '0.1em', textTransform: 'uppercase', marginTop: '8px' }}>{stat.label}</div>
                </div>
              ))}
            </div>
            <p style={{ color: '#888', fontSize: '14px', lineHeight: 1.8, maxWidth: '800px' }}>
              Beyond regulatory compliance, RIINA's research covers certified compilation (Track R), hardware side-channel
              contracts (Track S), hermetic binary bootstrap (Track T), verified micro-hypervisor runtime (Track U),
              termination guarantees (Track V), separation-logic memory safety (Track W), session-typed concurrency (Track X),
              verified standard library (Track Y), and robust declassification policies (Track Z). Every threat model
              has a formal response.
            </p>
          </div>

          {/* Proof certificate */}
          <h2 style={sectionLabel}>PROOF CERTIFICATE</h2>
          <p style={{ color: '#666', fontSize: '14px', marginBottom: '16px' }}>
            Generate a machine-checkable compliance certificate:
          </p>
          <pre className="code-block" style={codeBlockStyle}>
{`$ riinac verify --compliance hipaa,pci-dss myapp.rii

RIINA COMPLIANCE CERTIFICATE
============================
Program: myapp.rii
Compiler: riinac 0.1.0
Prover: Rocq 9.1

HIPAA §164.312(a) — Access Control
  PROVEN: All PHI access gated by role-based authorization
  Theorem: access_control_enforced (Coq: properties/HIPAACompliance.v:42)

HIPAA §164.312(b) — Audit Controls
  PROVEN: Every PHI access logged with timestamp, user, action
  Theorem: audit_trail_complete (Coq: properties/HIPAACompliance.v:87)

HIPAA §164.312(e) — Transmission Security
  PROVEN: PHI encrypted in transit (Rahsia type)
  Theorem: transmission_encrypted (Coq: properties/HIPAACompliance.v:112)

PCI-DSS Req 3 — Protect Stored Cardholder Data
  PROVEN: Cardholder data encrypted at rest
  Theorem: stored_data_encrypted (Coq: properties/PCIDSSCompliance.v:34)`}
          </pre>

          <h2 style={{ ...sectionLabel, marginTop: '48px' }}>AUDITOR VERIFICATION</h2>
          <p style={{ color: '#666', fontSize: '14px', marginBottom: '16px' }}>
            Auditors can independently verify certificates — zero trust:
          </p>
          <pre className="code-block" style={codeBlockStyle}>
{`$ cd 02_FORMAL/coq && make

# Check specific theorems
$ coqc -Q . RIINA properties/HIPAACompliance.v
$ Print Assumptions access_control_enforced.
> Closed under the global context
  (no unproven assumptions)`}
          </pre>

          <h2 style={{ ...sectionLabel, marginTop: '48px' }}>PROOF METRICS</h2>
          <div className="grid-4" style={{ display: 'grid', gridTemplateColumns: 'repeat(4, 1fr)', gap: '24px', marginBottom: '48px' }}>
            {[
              { value: '150', label: 'Compliance Theorems' },
              { value: '15', label: 'Regulations Covered' },
              { value: '0', label: 'Admits' },
              { value: '0', label: 'Unjustified Axioms' },
            ].map((stat, i) => (
              <div key={i} style={{ textAlign: 'center', ...cardStyle }}>
                <div style={{ fontSize: '36px', fontWeight: 300, fontFamily: 'Georgia, serif' }}>{stat.value}</div>
                <div style={{ fontSize: '12px', color: '#999', letterSpacing: '0.1em', textTransform: 'uppercase', marginTop: '8px' }}>{stat.label}</div>
              </div>
            ))}
          </div>

          <h2 style={{ ...sectionLabel, marginTop: '48px' }}>WHY ENTERPRISE TEAMS CHOOSE RIINA</h2>
          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '24px' }}>
            {[
              { title: 'Security Auditors', desc: 'RIINA certificates supplement or replace manual code review. The certificate shows which controls are covered, the Coq proof, and all assumptions. Audit cycles go from weeks to minutes.' },
              { title: 'Compliance Officers', desc: 'Include RIINA certificates in compliance packages. Demonstrates that security properties are mathematically guaranteed, not merely tested. Regulators get machine-verifiable evidence.' },
              { title: 'Procurement & Certification', desc: 'RIINA programs meet formal methods requirements in Common Criteria EAL5-EAL7, DO-178C DAL A, ISO 26262 ASIL-D TCL1, and NIST 800-53 High baseline.' },
              { title: 'Gradual Adoption via C FFI', desc: 'No rewrite needed. Use RIINA for security-critical modules via C FFI (luaran "C"). Existing C/Rust/Go codebases call RIINA libraries for proven-secure components. Start with one module, expand as confidence grows.' },
              { title: 'CTO & Engineering Leads', desc: 'Eliminate entire vulnerability classes by construction. No more CVE triage for information leaks, injection attacks, or timing side-channels in RIINA-compiled code. Reduce security engineering costs permanently.' },
              { title: 'Insurance & Risk Management', desc: 'Formal verification evidence reduces cyber insurance premiums. Machine-checkable proofs demonstrate due diligence beyond industry standard. Quantifiable risk reduction for board-level reporting.' },
            ].map((uc, i) => (
              <div key={i} style={{ ...cardStyle, padding: '24px' }}>
                <h3 style={{ fontSize: '16px', fontWeight: 600, marginBottom: '8px' }}>{uc.title}</h3>
                <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.6, margin: 0 }}>{uc.desc}</p>
              </div>
            ))}
          </div>
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // RELEASES PAGE
  // ============================================================================
  const ReleasesPage = () => (
    <div style={pageTopStyle}>
      <PageHeader
        title="Releases"
        subtitle="Download RIINA releases and track changes across versions."
      />
      <section className="section" style={sectionStyle}>
        <div style={{ marginBottom: '48px' }}>
          <div style={{
            display: 'inline-block',
            padding: '8px 16px',
            backgroundColor: '#000',
            color: '#fff',
            fontSize: '14px',
            fontWeight: 600,
            marginBottom: '24px'
          }}>
            Latest: v{releases[0]?.version}
          </div>
          <p style={{ color: '#666', fontSize: '14px' }}>
            <a href={`https://github.com/ib823/riina/releases/tag/v${releases[0]?.version}`}
               style={{ color: '#000', textDecoration: 'underline' }}>
              Download from GitHub
            </a>
            {' · '}
            <a href="https://github.com/ib823/riina/blob/main/CHANGELOG.md"
               style={{ color: '#000', textDecoration: 'underline' }}>
              Full Changelog
            </a>
          </p>
        </div>

        <div style={{ ...codeBlockStyle, marginBottom: '48px' }}>
          <pre style={{ margin: 0, whiteSpace: 'pre-wrap' }}>
{`# Install RIINA
curl -fsSL https://ib823.github.io/riina/install.sh | bash

# Or with Nix
nix run github:ib823/riina`}
          </pre>
        </div>

        <h2 style={{ ...sectionLabel }}>ALL RELEASES</h2>
        <div style={{ display: 'flex', flexDirection: 'column', gap: '24px' }}>
          {releases.map((rel, i) => (
            <div key={i} style={{
              ...cardStyle,
              borderLeft: i === 0 ? '3px solid #000' : '1px solid #eee'
            }}>
              <div style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'baseline', marginBottom: '16px' }}>
                <h3 style={{ fontSize: '20px', fontWeight: 600, margin: 0 }}>v{rel.version}</h3>
                <span style={{ color: '#999', fontSize: '14px' }}>{rel.date}</span>
              </div>
              <ul style={{ margin: 0, paddingLeft: '20px' }}>
                {rel.highlights.map((h, j) => (
                  <li key={j} style={{ color: '#666', fontSize: '14px', lineHeight: 1.8 }}>{h}</li>
                ))}
              </ul>
              <div style={{ marginTop: '16px' }}>
                <a href={`https://github.com/ib823/riina/releases/tag/v${rel.version}`}
                   style={{ color: '#000', fontSize: '13px', textDecoration: 'underline' }}>
                  Release notes &amp; downloads
                </a>
              </div>
            </div>
          ))}
        </div>
      </section>
    </div>
  );

  // ============================================================================
  // BISIK PAGE — Contact
  // ============================================================================
  const BisikPage = () => {
    const [bName, setBName] = useState('');
    const [bMsg, setBMsg] = useState('');

    const buildTelegramUrl = () => {
      let text = '';
      if (bName.trim()) text += `From: ${bName.trim()}\n`;
      text += `\n${bMsg.trim()}`;
      return `https://t.me/ib823?text=${encodeURIComponent(text.trim())}`;
    };

    const inputStyle = { width: '100%', padding: '12px', border: '1px solid #ddd', fontSize: '14px', fontFamily: 'inherit', boxSizing: 'border-box' };
    const labelStyle = { display: 'block', fontSize: '12px', letterSpacing: '0.1em', color: '#999', marginBottom: '6px' };

    return (
      <div style={pageTopStyle}>
        <PageHeader title="Reach Us" subtitle="Send a message directly. It goes straight to Telegram." />

        <section style={{ ...sectionStyle, maxWidth: '560px' }}>
          <div style={{ display: 'flex', flexDirection: 'column', gap: '16px' }}>
            <div>
              <label style={labelStyle}>NAMA (pilihan)</label>
              <input type="text" value={bName} onChange={(e) => setBName(e.target.value)} placeholder="Nama anda" style={inputStyle} />
            </div>
            <div>
              <label style={labelStyle}>MESEJ *</label>
              <textarea value={bMsg} onChange={(e) => setBMsg(e.target.value)} placeholder="Tulis mesej anda di sini..." rows={6} style={{ ...inputStyle, resize: 'vertical' }} />
            </div>
            <a
              href={bMsg.trim() ? buildTelegramUrl() : undefined}
              target="_blank"
              rel="noopener noreferrer"
              onClick={(e) => { if (!bMsg.trim()) e.preventDefault(); }}
              style={{
                display: 'block', textAlign: 'center',
                padding: '14px 32px', backgroundColor: '#000', color: '#fff',
                textDecoration: 'none', fontSize: '14px', letterSpacing: '0.05em',
                opacity: !bMsg.trim() ? 0.4 : 1,
                cursor: !bMsg.trim() ? 'default' : 'pointer',
              }}
            >
              Hantar via Telegram &rarr;
            </a>
            <p style={{ fontSize: '12px', color: '#999', textAlign: 'center' }}>
              Opens Telegram with your message pre-filled. Nothing is stored on this site.
            </p>
          </div>
        </section>
      </div>
    );
  };

  // ============================================================================
  // FOOTER
  // ============================================================================
  const Footer = () => {
    const footerSections = [
      { title: 'Product', links: ['Home', 'Why Proof', 'Language', 'How It Works', 'Demos'] },
      { title: 'Resources', links: ['Documentation', 'Enterprise', 'Research', 'Releases', 'GitHub'] },
      { title: 'Community', links: ['Reach Us', 'Issues', 'Discussions'] },
      { title: 'Legal', links: ['MPL-2.0 License', 'Privacy', 'Terms'] }
    ];

    return (
      <footer className="site-footer" style={{
        borderTop: '1px solid #eee',
        padding: '64px 32px',
        backgroundColor: '#fafafa'
      }}>
        <div className="grid-footer" style={{
          maxWidth: '1200px',
          margin: '0 auto',
          display: 'grid',
          gridTemplateColumns: '2fr 1fr 1fr 1fr 1fr',
          gap: '48px'
        }}>
          <div>
            <div style={{ display: 'flex', alignItems: 'center', gap: '12px', marginBottom: '16px' }}>
              <Logo size={24} />
              <span style={{ fontWeight: 600, letterSpacing: '0.1em' }}>RIINA</span>
            </div>
            <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.6 }}>
              Rigorous Immutable Invariant,<br/>No Assumptions
            </p>
            <p style={{
              color: '#999',
              fontSize: '12px',
              fontStyle: 'italic',
              marginTop: '16px'
            }}>
              Bertampuk Bertangkai
            </p>
          </div>

          {footerSections.map((col, i) => (
            <div key={i}>
              <h4 style={{
                fontSize: '12px',
                letterSpacing: '0.1em',
                color: '#999',
                marginBottom: '16px'
              }}>{col.title}</h4>
              <div style={{ display: 'flex', flexDirection: 'column', gap: '12px' }}>
                {col.links.map((link, j) => {
                  const ext = externalLinks[link];
                  const page = footerNav(link);

                  if (ext) {
                    return (
                      <a key={j} href={ext} style={{
                        color: '#666',
                        fontSize: '14px',
                        textDecoration: 'none'
                      }}>
                        {link}
                      </a>
                    );
                  }

                  return (
                    <button key={j}
                      onClick={() => setCurrentPage(page)}
                      style={{
                        background: 'none',
                        border: 'none',
                        cursor: 'pointer',
                        color: '#666',
                        fontSize: '14px',
                        textDecoration: 'none',
                        textAlign: 'left',
                        padding: 0
                      }}
                    >
                      {link}
                    </button>
                  );
                })}
              </div>
            </div>
          ))}
        </div>

        <div className="footer-bottom" style={{
          maxWidth: '1200px',
          margin: '48px auto 0',
          paddingTop: '24px',
          borderTop: '1px solid #eee',
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center'
        }}>
          <p style={{ color: '#999', fontSize: '12px' }}>
            © 2026 RIINA. All rights reserved.
          </p>
          <p style={{ color: '#999', fontSize: '12px' }}>
            RIINA v0.2.0 · MPL-2.0
          </p>
        </div>
      </footer>
    );
  };

  // ============================================================================
  // RENDER
  // ============================================================================
  const renderPage = () => {
    switch (currentPage) {
      case 'whyProof': return <WhyProofPage />;
      case 'language': return <LanguagePage />;
      case 'how': return <HowPage />;
      case 'demos': return <DemosPage />;
      case 'enterprise': return <EnterprisePage />;
      case 'releases': return <ReleasesPage />;
      case 'docs': return <DocsPage />;
      case 'research': return <ResearchPage />;
      case 'syntax': return <SyntaxPage />;
      case 'securityTypes': return <SecurityTypesPage />;
      case 'effectSystem': return <EffectSystemPage />;
      case 'examples': return <ExamplesPage />;
      case 'quickStart': return <QuickStartPage />;
      case 'stdlib': return <StdLibPage />;
      case 'contributing': return <ContributingPage />;
      case 'license': return <LicensePage />;
      case 'privacy': return <PrivacyPage />;
      case 'terms': return <TermsPage />;
      case 'bisik': return <BisikPage />;
      case 'playground': return <PlaygroundPage onNavigate={setCurrentPage} />;
      default: return <HomePage />;
    }
  };

  return (
    <div style={{
      fontFamily: '-apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif',
      color: '#000',
      lineHeight: 1.5
    }}>
      <Header />
      <main style={{ paddingTop: '65px' }}>
        {renderPage()}
      </main>
      <Footer />
    </div>
  );
};

export default RiinaWebsite;
