import React, { useState, useEffect } from 'react';

// ============================================================================
// RIINA WEBSITE - COMPLETE IMPLEMENTATION (13 PAGES)
// ============================================================================

const RiinaWebsite = () => {
  const [currentPage, setCurrentPage] = useState('home');
  const [mobileMenuOpen, setMobileMenuOpen] = useState(false);

  // Scroll to top on page change
  useEffect(() => {
    window.scrollTo(0, 0);
  }, [currentPage]);

  // Navigation
  const pages = [
    { id: 'home', label: 'Home' },
    { id: 'language', label: 'Language' },
    { id: 'how', label: 'How It Works' },
    { id: 'research', label: 'Research' },
    { id: 'docs', label: 'Documentation' },
  ];

  // Footer link mapping
  const footerNav = (label) => {
    const map = {
      'Syntax': 'syntax',
      'Security Types': 'securityTypes',
      'Effect System': 'effectSystem',
      'Examples': 'examples',
      'Documentation': 'docs',
      'Quick Start': 'quickStart',
      'Standard Library': 'stdlib',
      'Contributing': 'contributing',
      'MPL-2.0 License': 'license',
      'Privacy': 'privacy',
      'Terms': 'terms',
    };
    return map[label] || null;
  };

  const externalLinks = {
    'GitHub': 'https://github.com/ib823/proof',
    'Issues': 'https://github.com/ib823/proof/issues',
    'Discussions': 'https://github.com/ib823/proof/discussions',
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
    <section style={{ padding: '80px 32px', maxWidth: '800px', margin: '0 auto' }}>
      <h1 style={{ fontSize: '48px', fontWeight: 300, marginBottom: '32px' }}>{title}</h1>
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
    <header style={{
      position: 'fixed',
      top: 0,
      left: 0,
      right: 0,
      zIndex: 100,
      backgroundColor: 'rgba(255,255,255,0.95)',
      backdropFilter: 'blur(10px)',
      borderBottom: '1px solid #eee'
    }}>
      <div style={{
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

        <nav style={{ display: 'flex', gap: '32px' }}>
          {pages.slice(1).map(page => (
            <button
              key={page.id}
              onClick={() => setCurrentPage(page.id)}
              style={{
                background: 'none',
                border: 'none',
                cursor: 'pointer',
                fontSize: '14px',
                color: currentPage === page.id ? '#000' : '#666',
                fontWeight: currentPage === page.id ? 500 : 400
              }}
            >
              {page.label}
            </button>
          ))}
        </nav>

        <a
          href="https://github.com/ib823/proof"
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
    </header>
  );

  // ============================================================================
  // HOME PAGE
  // ============================================================================
  const HomePage = () => (
    <div>
      {/* Hero */}
      <section style={{
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

        <h1 style={{
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
          RIINA is a formally verified programming language with Bahasa Melayu
          syntax. Security properties are mathematically proven in Coq — not
          tested, not assumed,
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
            href="https://github.com/ib823/proof"
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
        <div style={{
          display: 'flex',
          gap: '64px',
          paddingTop: '48px',
          borderTop: '1px solid #eee'
        }}>
          {[
            { value: '5,304', label: 'Theorems Proven' },
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
      <section style={{
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
          margin: '0 auto',
          fontFamily: 'Georgia, serif',
          fontStyle: 'italic'
        }}>
          Bertampuk Bertangkai<br/>
          <span style={{ fontSize: '14px', fontStyle: 'normal' }}>Every claim backed by proof</span>
        </p>
      </section>

      {/* How It's Different */}
      <section style={{ padding: '120px 32px', maxWidth: '1200px', margin: '0 auto' }}>
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

        <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '64px' }}>
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

          <pre style={codeBlockStyle}>
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
      <section style={{ padding: '120px 32px', maxWidth: '1200px', margin: '0 auto' }}>
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
            { name: 'Secure Web Services', desc: 'Taint tracking, injection prevention', icon: '⊢' },
            { name: 'Post-Quantum Crypto', desc: 'Constant-time, verified primitives', icon: '⊢' },
            { name: 'Healthcare (HIPAA)', desc: 'Patient data provably confidential', icon: '⊢' },
            { name: 'Payment Processing', desc: 'Cardholder data cannot leak', icon: '⊢' },
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
          Open source. MPL-2.0 licensed. Made in Malaysia.
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
            href="https://github.com/ib823/proof"
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

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '16px' }}>
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

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr', gap: '64px' }}>
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
          <pre style={codeBlockStyle}>
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

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '32px' }}>
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
          <pre style={codeBlockStyle}>
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
          <pre style={codeBlockStyle}>
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
          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '16px', marginBottom: '64px' }}>
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
          <pre style={codeBlockStyle}>
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
          <pre style={codeBlockStyle}>
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
        subtitle="111 example .rii files across 9 categories, demonstrating RIINA's syntax, security types, effects, compliance, and design patterns."
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
          <pre style={codeBlockStyle}>
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
          <pre style={codeBlockStyle}>
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
          <pre style={codeBlockStyle}>
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
          <p style={{ color: '#666', fontSize: '14px', lineHeight: 1.6, marginBottom: '32px' }}>
            Pre-recorded output from <code>riinac run</code> on the 5 demo programs in <code>07_EXAMPLES/demos/</code>.
          </p>
          {[
            { name: 'selamat_datang.rii', desc: 'Hello World — Bahasa Melayu greeting', code: `fungsi utama() -> Teks kesan IO {
    biar mesej = "Selamat datang ke RIINA, Malaysia!";
    cetakln(mesej);
    pulang mesej;
}`, output: `$ riinac run selamat_datang.rii
Selamat datang ke RIINA, Malaysia!` },
            { name: 'faktorial.rii', desc: 'Recursive factorial with LetRec', code: `fungsi utama() -> Teks kesan IO {
    biar hasil = faktorial(10);
    biar mesej = "faktorial(10) = " + ke_teks(hasil);
    cetakln(mesej);
    pulang mesej;
}`, output: `$ riinac run faktorial.rii
faktorial(10) = 3628800` },
            { name: 'pasangan.rii', desc: 'Tuple / pair types', code: `fungsi utama() -> Teks kesan IO {
    biar titik = (10, 20);
    biar mesej = "Titik: (" + ke_teks(titik.0) + ", " + ke_teks(titik.1) + ")";
    cetakln(mesej);
    pulang mesej;
}`, output: `$ riinac run pasangan.rii
Titik: (10, 20)` },
            { name: 'rahsia_dijaga.rii', desc: 'Secret type with controlled declassification', code: `fungsi utama() -> Teks kesan IO {
    biar kunci: Rahsia<Teks> = rahsia("s3cr3t_p4ss");
    biar terdedah = dedah(kunci);
    cetakln(terdedah);
    pulang terdedah;
}`, output: `$ riinac run rahsia_dijaga.rii
s3cr3t_p4ss` },
            { name: 'kalkulator_c.rii', desc: 'C FFI — calling abs() via luaran "C"', code: `luaran "C" {
    fungsi abs(n: Nombor) -> Nombor;
}

fungsi utama() -> Teks kesan IO {
    biar hasil = abs(42);
    biar mesej = "mutlak(42) = " + ke_teks(hasil);
    cetakln(mesej);
    pulang mesej;
}`, output: `$ riinac run kalkulator_c.rii
mutlak(42) = 42` },
          ].map((demo, i) => (
            <div key={i} style={{ ...cardStyle, marginBottom: '24px' }}>
              <div style={{ display: 'flex', justifyContent: 'space-between', marginBottom: '8px' }}>
                <code style={{ fontWeight: 600, fontSize: '14px' }}>{demo.name}</code>
                <span style={{ color: '#999', fontSize: '12px' }}>{demo.desc}</span>
              </div>
              <pre style={{ ...codeBlockStyle, marginBottom: '12px' }}>{demo.code}</pre>
              <pre style={{
                background: '#1a1a1a',
                color: '#33ff33',
                padding: '16px 20px',
                fontSize: '13px',
                lineHeight: 1.5,
                borderRadius: '0',
                border: '1px solid #333',
                fontFamily: '"SF Mono", "Fira Code", monospace',
                overflow: 'auto',
              }}>{demo.output}</pre>
            </div>
          ))}

          <div style={{ textAlign: 'center', marginTop: '48px' }}>
            <a
              href="https://github.com/ib823/proof/tree/public/07_EXAMPLES"
              style={{
                display: 'inline-block',
                padding: '14px 28px',
                border: '1px solid #000',
                color: '#000',
                textDecoration: 'none',
                fontSize: '14px'
              }}
            >
              Browse all 108 examples on GitHub
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

5,304 theorems verified in Coq. 0 admits. If the proof fails, compilation fails.`
            },
            {
              step: '04',
              title: 'Verified End-to-End',
              content: `RIINA's compiler itself is verified with riinac verify [--fast|--full].
No external CI/CD — verification lives inside the compiler.

The formal proofs (278 Coq files) ship with the compiler. You can audit them.
5 justified axioms — all documented, none hidden.
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
        subtitle="RIINA is built on formal verification in Coq, with 5,304 machine-checked theorems across 244 files. Every security property has a proof."
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
              { value: '5,304', label: 'Qed Proofs' },
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

          <h2 style={sectionLabel}>RESEARCH SCOPE</h2>

          <div style={{
            display: 'grid',
            gridTemplateColumns: '1fr 1fr',
            gap: '16px'
          }}>
            {[
              'A: Core Type Theory & Proofs',
              'B: Compiler & Prototype (Rust)',
              'C: Language Specifications',
              'D–Q: Attack Surface Research',
              'R: Certified Compilation',
              'S: Hardware Contracts',
              'T: Hermetic Bootstrap',
              'U: Runtime Guardian',
              'V: Termination Guarantees',
              'W: Verified Memory',
              'X: Concurrency Model',
              'Y: Verified Standard Library',
              'Z: Declassification Policy',
              'AA–AJ: Extended Research'
            ].map((domain, i) => (
              <div key={i} style={{
                padding: '16px',
                backgroundColor: '#f8f8f8',
                fontSize: '14px'
              }}>
                {domain}
              </div>
            ))}
          </div>

          <p style={{
            marginTop: '32px',
            color: '#666',
            fontSize: '14px'
          }}>
            218 research tracks across 55 domains. 588 Rust tests, 13 crates, 111 example .rii files.
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
          href="https://github.com/ib823/proof"
          style={{
            display: 'inline-block',
            padding: '16px 32px',
            border: '1px solid #fff',
            color: '#fff',
            textDecoration: 'none',
            fontSize: '14px'
          }}
        >
          github.com/ib823/proof
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
      { title: 'Formal Proofs', desc: '278 Coq files, 5,304 theorems', page: 'research',
        links: [{ text: 'Proof Architecture', page: 'research' }, { text: 'Axiom Justifications', page: 'research' }, { text: 'Building Proofs', page: 'research' }] },
      { title: 'Examples', desc: '111 example .rii files in 9 categories', page: 'examples',
        links: [{ text: 'pengesahan.rii', page: 'examples' }, { text: 'kripto.rii', page: 'examples' }, { text: 'hello_dunia.rii', page: 'examples' }] },
    ];

    return (
      <div style={pageTopStyle}>
        <section style={{ padding: '80px 32px', maxWidth: '1200px', margin: '0 auto' }}>
          <h1 style={{ fontSize: '48px', fontWeight: 300, marginBottom: '48px' }}>
            Documentation
          </h1>

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '32px' }}>
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
{`git clone https://github.com/ib823/proof.git
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
{`nix run github:ib823/proof`}
              </pre>
            </div>
            <div style={cardStyle}>
              <h3 style={{ fontSize: '16px', marginBottom: '12px' }}>Portable Installer</h3>
              <pre style={{ ...codeBlockStyle, padding: '16px' }}>
{`curl -sSf https://riina.my/install.sh | bash
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
git clone https://github.com/ib823/proof.git
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
cargo test --all        # 588 tests, all must pass`}
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
              'All Rust tests must pass (588+)',
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

          <div style={{ display: 'grid', gridTemplateColumns: '1fr 1fr 1fr', gap: '24px', marginBottom: '64px' }}>
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
            href="https://github.com/ib823/proof/blob/main/LICENSE"
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
  // FOOTER
  // ============================================================================
  const Footer = () => {
    const footerSections = [
      { title: 'Language', links: ['Syntax', 'Security Types', 'Effect System', 'Examples'] },
      { title: 'Developers', links: ['Documentation', 'Quick Start', 'Standard Library', 'GitHub'] },
      { title: 'Community', links: ['Contributing', 'Issues', 'Discussions'] },
      { title: 'Legal', links: ['MPL-2.0 License', 'Privacy', 'Terms'] }
    ];

    return (
      <footer style={{
        borderTop: '1px solid #eee',
        padding: '64px 32px',
        backgroundColor: '#fafafa'
      }}>
        <div style={{
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

        <div style={{
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
            Made in Malaysia
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
      case 'language': return <LanguagePage />;
      case 'how': return <HowPage />;
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
