import React, { useState, useEffect } from 'react';

/**
 * RIINA Release Information Components
 *
 * Displays release versioning with semantic impact categories
 * so users understand the nature and impact of each update.
 *
 * Release Categories:
 * - MAJOR (X.0.0): Breaking changes, new security domains, architectural shifts
 * - MINOR (0.X.0): New proofs, features, optimizations, expanded coverage
 * - PATCH (0.0.X): Bug fixes, documentation, small improvements
 *
 * Session Categories:
 * - PROOF: New formal proofs added or axioms eliminated
 * - FEATURE: New language/compiler features
 * - PLATFORM: Platform support, backends, deployment
 * - SECURITY: Security domain coverage expansion
 * - DOCS: Documentation and examples
 * - FIX: Bug fixes and corrections
 */

// Impact level colors and styles
const IMPACT_STYLES = {
  major: {
    bg: 'rgba(239, 68, 68, 0.1)',
    border: 'rgba(239, 68, 68, 0.3)',
    text: '#dc2626',
    label: 'MAJOR',
    desc: 'Breaking changes or major new capabilities',
  },
  minor: {
    bg: 'rgba(59, 130, 246, 0.1)',
    border: 'rgba(59, 130, 246, 0.3)',
    text: '#2563eb',
    label: 'MINOR',
    desc: 'New features and improvements',
  },
  patch: {
    bg: 'rgba(34, 197, 94, 0.1)',
    border: 'rgba(34, 197, 94, 0.3)',
    text: '#16a34a',
    label: 'PATCH',
    desc: 'Bug fixes and small updates',
  },
};

// Session type categories
const SESSION_TYPES = {
  proof: { icon: '∴', color: '#8b5cf6', label: 'Proofs' },
  feature: { icon: '⚡', color: '#f59e0b', label: 'Feature' },
  platform: { icon: '🔧', color: '#06b6d4', label: 'Platform' },
  security: { icon: '🛡️', color: '#ef4444', label: 'Security' },
  docs: { icon: '📖', color: '#64748b', label: 'Docs' },
  fix: { icon: '🔨', color: '#22c55e', label: 'Fix' },
};

// Parse version to determine impact level
const getImpactLevel = (version) => {
  const [major, minor, patch] = version.split('.').map(Number);
  if (patch === 0 && minor === 0) return 'major';
  if (patch === 0) return 'minor';
  return 'patch';
};

// Impact badge component
export const ImpactBadge = ({ level, size = 'normal' }) => {
  const style = IMPACT_STYLES[level] || IMPACT_STYLES.patch;
  const padding = size === 'small' ? '2px 6px' : '4px 10px';
  const fontSize = size === 'small' ? '9px' : '10px';

  return (
    <span style={{
      display: 'inline-block',
      backgroundColor: style.bg,
      border: `1px solid ${style.border}`,
      color: style.text,
      padding: padding,
      borderRadius: '4px',
      fontSize: fontSize,
      fontWeight: '700',
      letterSpacing: '0.5px',
    }}>
      {style.label}
    </span>
  );
};

// Session type badge
export const SessionTypeBadge = ({ type }) => {
  const config = SESSION_TYPES[type] || SESSION_TYPES.docs;

  return (
    <span style={{
      display: 'inline-flex',
      alignItems: 'center',
      gap: '4px',
      backgroundColor: `${config.color}15`,
      color: config.color,
      padding: '3px 8px',
      borderRadius: '12px',
      fontSize: '11px',
      fontWeight: '600',
    }}>
      <span>{config.icon}</span>
      {config.label}
    </span>
  );
};

// Version display with context
export const VersionDisplay = ({ version, showImpact = true, showContext = true }) => {
  const impact = getImpactLevel(version);
  const style = IMPACT_STYLES[impact];

  return (
    <div style={{
      display: 'inline-flex',
      alignItems: 'center',
      gap: '10px',
    }}>
      <span style={{
        fontFamily: 'JetBrains Mono, monospace',
        fontSize: '16px',
        fontWeight: '700',
        color: '#0f172a',
      }}>
        v{version}
      </span>
      {showImpact && <ImpactBadge level={impact} />}
      {showContext && (
        <span style={{ fontSize: '12px', color: '#64748b' }}>
          {style.desc}
        </span>
      )}
    </div>
  );
};

// Activity timeline showing recent sessions
export const ActivityTimeline = ({ maxItems = 5 }) => {
  const [metrics, setMetrics] = useState(null);

  useEffect(() => {
    fetch('/riina/metrics.json')
      .then(r => r.ok ? r.json() : null)
      .then(data => setMetrics(data))
      .catch(() => null);
  }, []);

  // Enhanced milestones with types
  const activities = [
    { date: '2026-02-06', type: 'feature', title: 'Session 75: P2/P4/P5 Implementation', detail: 'Typechecker formalization, mobile backends, self-hosting scaffolds (782 tests)' },
    { date: '2026-02-06', type: 'proof', title: 'Session 74: Triple-Prover Verification', detail: '84 theorems verified in Coq + Lean 4 + Isabelle/HOL' },
    { date: '2026-02-05', type: 'proof', title: 'Session 73: Proof Depth Expansion', detail: '+1,830 Qed proofs across 15 domain files' },
    { date: '2026-02-05', type: 'platform', title: 'Session 72: Coq 8.20.1 Migration', detail: 'Migrated from Rocq 9.1, all Admitted eliminated' },
    { date: '2026-02-01', type: 'platform', title: 'Phase 7 Complete', detail: 'WASM backend, mobile backends, playground' },
  ];

  return (
    <div style={{
      backgroundColor: '#fff',
      borderRadius: '16px',
      padding: '24px',
      border: '1px solid rgba(0, 0, 0, 0.06)',
    }}>
      <div style={{
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'space-between',
        marginBottom: '20px',
      }}>
        <h3 style={{ fontSize: '16px', fontWeight: '700', color: '#0f172a', margin: 0 }}>
          Recent Activity
        </h3>
        <span style={{
          fontSize: '11px',
          color: '#94a3b8',
          display: 'flex',
          alignItems: 'center',
          gap: '6px',
        }}>
          <span style={{
            width: '6px',
            height: '6px',
            borderRadius: '50%',
            backgroundColor: '#22c55e',
            animation: 'pulse 2s ease-in-out infinite',
          }} />
          Actively maintained
        </span>
      </div>

      <div style={{ display: 'flex', flexDirection: 'column', gap: '16px' }}>
        {activities.slice(0, maxItems).map((activity, i) => (
          <div key={i} style={{
            display: 'flex',
            gap: '14px',
            position: 'relative',
          }}>
            {/* Timeline line */}
            {i < activities.length - 1 && (
              <div style={{
                position: 'absolute',
                left: '11px',
                top: '28px',
                bottom: '-16px',
                width: '2px',
                backgroundColor: '#e2e8f0',
              }} />
            )}

            {/* Timeline dot */}
            <div style={{
              width: '24px',
              height: '24px',
              borderRadius: '50%',
              backgroundColor: `${SESSION_TYPES[activity.type]?.color}20`,
              border: `2px solid ${SESSION_TYPES[activity.type]?.color}`,
              display: 'flex',
              alignItems: 'center',
              justifyContent: 'center',
              fontSize: '12px',
              flexShrink: 0,
              zIndex: 1,
            }}>
              {SESSION_TYPES[activity.type]?.icon}
            </div>

            {/* Content */}
            <div style={{ flex: 1 }}>
              <div style={{
                display: 'flex',
                alignItems: 'center',
                gap: '10px',
                marginBottom: '4px',
                flexWrap: 'wrap',
              }}>
                <span style={{
                  fontSize: '14px',
                  fontWeight: '600',
                  color: '#1e293b',
                }}>
                  {activity.title}
                </span>
                <SessionTypeBadge type={activity.type} />
              </div>
              <div style={{
                fontSize: '13px',
                color: '#64748b',
                marginBottom: '4px',
              }}>
                {activity.detail}
              </div>
              <div style={{
                fontSize: '11px',
                color: '#94a3b8',
                fontFamily: 'JetBrains Mono, monospace',
              }}>
                {activity.date}
              </div>
            </div>
          </div>
        ))}
      </div>
    </div>
  );
};

// Compact footer showing active development
export const ActiveDevelopmentFooter = () => {
  const [metrics, setMetrics] = useState(null);

  useEffect(() => {
    fetch('/riina/metrics.json')
      .then(r => r.ok ? r.json() : null)
      .then(data => setMetrics(data))
      .catch(() => setMetrics({ version: '0.2.0', session: 73 }));
  }, []);

  return (
    <div style={{
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'center',
      gap: '20px',
      padding: '16px 24px',
      backgroundColor: 'rgba(248, 250, 252, 0.8)',
      borderRadius: '12px',
      border: '1px solid rgba(0, 0, 0, 0.04)',
      flexWrap: 'wrap',
      fontSize: '13px',
      color: '#475569',
    }}>
      <span style={{ display: 'flex', alignItems: 'center', gap: '6px' }}>
        <span style={{
          width: '8px',
          height: '8px',
          borderRadius: '50%',
          backgroundColor: '#22c55e',
          animation: 'pulse 2s ease-in-out infinite',
        }} />
        <strong style={{ color: '#166534' }}>Actively Maintained</strong>
      </span>

      <span style={{ color: '#cbd5e1' }}>·</span>

      {metrics && (
        <span>
          <strong style={{ color: '#1e293b' }}>v{metrics.version}</strong>
          <span style={{ margin: '0 6px', color: '#cbd5e1' }}>·</span>
          Session {metrics.session}
        </span>
      )}

      <span style={{ color: '#cbd5e1' }}>·</span>

      <span>
        Last update: <strong style={{ color: '#1e293b' }}>Today</strong>
      </span>
    </div>
  );
};

// Release card for releases page
export const ReleaseCard = ({ version, date, highlights, current = false }) => {
  const impact = getImpactLevel(version);

  return (
    <div style={{
      backgroundColor: current ? 'rgba(59, 130, 246, 0.04)' : '#fff',
      border: current ? '2px solid rgba(59, 130, 246, 0.3)' : '1px solid rgba(0, 0, 0, 0.08)',
      borderRadius: '16px',
      padding: '24px',
      position: 'relative',
    }}>
      {current && (
        <span style={{
          position: 'absolute',
          top: '-10px',
          right: '16px',
          backgroundColor: '#3b82f6',
          color: '#fff',
          padding: '4px 12px',
          borderRadius: '10px',
          fontSize: '11px',
          fontWeight: '600',
        }}>
          LATEST
        </span>
      )}

      <div style={{
        display: 'flex',
        alignItems: 'center',
        gap: '12px',
        marginBottom: '16px',
        flexWrap: 'wrap',
      }}>
        <span style={{
          fontFamily: 'JetBrains Mono, monospace',
          fontSize: '20px',
          fontWeight: '700',
          color: '#0f172a',
        }}>
          v{version}
        </span>
        <ImpactBadge level={impact} />
        <span style={{ fontSize: '13px', color: '#64748b' }}>{date}</span>
      </div>

      <ul style={{
        margin: 0,
        paddingLeft: '20px',
        color: '#475569',
        fontSize: '14px',
        lineHeight: '1.7',
      }}>
        {highlights.map((h, i) => (
          <li key={i}>{h}</li>
        ))}
      </ul>
    </div>
  );
};

export default {
  ImpactBadge,
  SessionTypeBadge,
  VersionDisplay,
  ActivityTimeline,
  ActiveDevelopmentFooter,
  ReleaseCard,
};
