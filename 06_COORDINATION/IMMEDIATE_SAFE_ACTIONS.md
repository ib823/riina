# Immediate Safe Actions

```
╔══════════════════════════════════════════════════════════════════════════════════╗
║  IMMEDIATE ACTIONS THAT CAN BE STARTED WITHOUT COORDINATION                      ║
║  Date: 2026-01-16                                                                ║
║                                                                                  ║
║  These actions create NEW files only - zero conflict risk                        ║
╚══════════════════════════════════════════════════════════════════════════════════╝
```

## Summary

The following improvements can be started **immediately** without waiting for
any other work to complete, because they only create NEW files:

| Priority | ID | Description | Est. Effort |
|----------|-----|-------------|-------------|
| 1 | P0-002 | Create riina-symbols crate | 15 units |
| 2 | P0-003 | Create riina-arena crate | 20 units |
| 3 | P0-005 | Create riina-span crate | 10 units |
| 4 | P3-001 | Create aes_ni.rs | 30 units |
| 5 | P3-002 | Create aes_bitsliced.rs | 60 units |
| 6 | P2-001 | Create fast_lexer.rs | 40 units |

---

## Action 1: Create riina-symbols Crate

**Command sequence:**
```bash
cd /workspaces/proof/03_PROTO

# Create crate directory
mkdir -p crates/riina-symbols/src

# Create Cargo.toml
cat > crates/riina-symbols/Cargo.toml << 'EOF'
[package]
name = "riina-symbols"
version.workspace = true
edition.workspace = true
license.workspace = true

[dependencies]
# None - zero dependencies (Law 8)
EOF

# Add to workspace
# (Edit 03_PROTO/Cargo.toml to add "crates/riina-symbols" to members)
```

**Implementation:** See `01_RESEARCH/specs/SPEC_PERFORMANCE_OPTIMIZATION.md` Section 2.1

---

## Action 2: Create riina-arena Crate

**Command sequence:**
```bash
cd /workspaces/proof/03_PROTO

# Create crate directory
mkdir -p crates/riina-arena/src

# Create Cargo.toml
cat > crates/riina-arena/Cargo.toml << 'EOF'
[package]
name = "riina-arena"
version.workspace = true
edition.workspace = true
license.workspace = true

[dependencies]
# None - zero dependencies (Law 8)
EOF
```

**Implementation:** See `01_RESEARCH/specs/SPEC_PERFORMANCE_OPTIMIZATION.md` Section 2.2

---

## Action 3: Create riina-span Crate

**Command sequence:**
```bash
cd /workspaces/proof/03_PROTO

mkdir -p crates/riina-span/src

cat > crates/riina-span/Cargo.toml << 'EOF'
[package]
name = "riina-span"
version.workspace = true
edition.workspace = true
license.workspace = true

[dependencies]
# None
EOF
```

**Implementation:** See `01_RESEARCH/specs/SPEC_PERFORMANCE_OPTIMIZATION.md` Section 2.3

---

## Action 4: Create aes_ni.rs (Hardware AES)

**Location:** `05_TOOLING/crates/teras-core/src/crypto/aes_ni.rs`

**This is a NEW file** - no conflicts with existing `aes.rs`

**Implementation outline:**
```rust
//! AES-NI hardware acceleration for x86_64
//!
//! Uses Intel AES-NI instructions for 50-100x speedup.

#[cfg(all(target_arch = "x86_64", target_feature = "aes"))]
mod implementation {
    use std::arch::x86_64::*;
    // ... implementation
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "aes")))]
mod implementation {
    // Fallback to software implementation
    pub use super::super::aes::*;
}

pub use implementation::*;
```

---

## Action 5: Create aes_bitsliced.rs

**Location:** `05_TOOLING/crates/teras-core/src/crypto/aes_bitsliced.rs`

**This is a NEW file** - provides constant-time without hardware

---

## Action 6: Create fast_lexer.rs

**Location:** `03_PROTO/crates/riina-lexer/src/fast_lexer.rs`

**This is a NEW file** - sits alongside existing `lexer.rs`

**Implementation:** See `01_RESEARCH/specs/SPEC_PERFORMANCE_OPTIMIZATION.md` Section 3

---

## Verification After Each Action

```bash
# For Rust changes:
cd /workspaces/proof/03_PROTO
cargo build --all
cargo test --all
cargo clippy -- -D warnings

# For Tooling changes:
cd /workspaces/proof/05_TOOLING
cargo build --all
cargo test --all
cargo clippy -- -D warnings
```

---

## Commit Message Template

```
[P#-###] START: Creating {crate/file name}

- New file/crate, no modifications to existing code
- Zero external dependencies
- Part of Revolutionary Improvement Roadmap

Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>
```

---

*These actions can be performed in any order by any worker.*
*No coordination required beyond updating SESSION_LOG.md*
