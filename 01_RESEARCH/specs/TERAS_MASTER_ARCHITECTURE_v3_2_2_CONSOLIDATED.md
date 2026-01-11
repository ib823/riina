# TERAS MASTER ARCHITECTURE v3.2.2 â€” CONSOLIDATED AUTHORITATIVE DOCUMENT

> **CLASSIFICATION:** AUTHORITATIVE SPECIFICATION â€” SINGLE SOURCE OF TRUTH  
> **VERSION:** 3.2.2 CONSOLIDATED  
> **DATE:** 2026-01-01  
> **STATUS:** BINDING LAW  
> **DOCUMENT HASH:** [Compute SHA-256 upon finalization]  
> **PREVIOUS VERSION HASH (V3.2.1):** [Reference from official repository]

---

# PREFACE: HOW TO READ THIS DOCUMENT

This document is **LAW**. It is not a vision, not a guideline, not a suggestion.

This is the **SINGLE CONSOLIDATED AUTHORITATIVE DOCUMENT** for TERAS Master Architecture v3.2.2. All specifications are contained herein â€” there are NO external references, NO appendices in separate files, NO "see other document" statements.

**RULES FOR ANY CLAUDE INSTANCE OR DEVELOPER:**

1. If this document does not specify something, **ASK** before implementing
2. If this document says MUST, there are **NO EXCEPTIONS**
3. If this document says MUST NOT, **VIOLATION IS FAILURE**
4. If implementation differs from specification, **IMPLEMENTATION IS WRONG**
5. If specification seems impossible, **STOP AND REPORT**, do not improvise
6. All code must pass validation checkpoints **BEFORE** being considered complete
7. "Working code" that violates this specification is **REJECTED**
8. If you think you found a better way, **DOCUMENT AND PROPOSE**, do not implement

**VALIDATION HASH:** Any future version must include SHA-256 of previous version to prove lineage.

---

# VERSION 3.2.2 CHANGES

```
+------------------------------------------------------------------------------+
|                                                                              |
|   VERSION 3.2.2: ZERO THIRD-PARTY DEPENDENCIES                               |
|                                                                              |
|   This version establishes COMPLETE INDEPENDENCE from external components.   |
|                                                                              |
|   TERAS INFRASTRUCTURE COMPONENTS (NEW):                                     |
|     â€¢ SIMPAN: Embedded database (replaces SQLite/PostgreSQL/DuckDB)          |
|     â€¢ TUKAR: Binary protocol (replaces JSON/Protobuf/FlatBuffers)            |
|     â€¢ ATUR: Orchestration engine (replaces Kubernetes/Nomad)                 |
|     â€¢ MAMPAT: Compression engine (replaces zstd/lz4/brotli)                  |
|     â€¢ AKAL: ML runtime (replaces ONNX/TensorRT/PyTorch)                      |
|     â€¢ JEJAK: Telemetry (replaces Prometheus/Grafana/Jaeger)                  |
|     â€¢ NADI: Network protocol (replaces HTTPS/gRPC/QUIC)                      |
|     â€¢ BEKAS: Container runtime (replaces Docker/containerd)                  |
|     â€¢ JALINAN: Service mesh (replaces Istio/Linkerd/Envoy)                   |
|                                                                              |
|   FUNDAMENTAL PRINCIPLE:                                                     |
|   TERAS uses ZERO third-party runtime components.                            |
|   Every database, protocol, framework built internally.                      |
|   Every implementation surpasses industry best-in-class by design.           |
|   This is LAW.                                                               |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

# TABLE OF CONTENTS

```
PART I:      IMMUTABLE LAWS .................................................. [Line ~200]
PART II:     TERAS INFRASTRUCTURE SPECIFICATION .............................. [Line ~600]
  II.1       SIMPAN (Database Engine) ........................................ [Line ~650]
  II.2       TUKAR (Binary Protocol) ......................................... [Line ~900]
  II.3       ATUR (Orchestration Engine) ..................................... [Line ~1100]
  II.4       MAMPAT (Compression Engine) ..................................... [Line ~1300]
  II.5       AKAL (ML Runtime) ............................................... [Line ~1450]
  II.6       JEJAK (Telemetry Engine) ........................................ [Line ~1650]
  II.7       NADI (Network Protocol) ......................................... [Line ~1800]
  II.8       BEKAS (Container Runtime) ....................................... [Line ~1950]
  II.9       JALINAN (Service Mesh) .......................................... [Line ~2100]
PART III:    ML TRAINING PIPELINE (BENTENG) .................................. [Line ~2250]
PART IV:     FORENSIC EVIDENCE CHAIN (MENARA) ................................ [Line ~2900]
PART V:      CONTAINER DEPLOYMENT (GAPURA) ................................... [Line ~3500]
PART VI:     SBOM REQUIREMENTS ............................................... [Line ~4200]
PART VII:    VALIDATION CHECKPOINTS .......................................... [Line ~4800]
```

---

# PART I: IMMUTABLE LAWS

These laws **CANNOT** be changed, relaxed, or "temporarily suspended for MVP."

---

## LAW 1: BIOMETRIC DATA LOCALITY

```
+------------------------------------------------------------------------------+
|                                                                              |
|   BIOMETRIC DATA (face images, fingerprints, voice prints, iris scans)       |
|   MUST NEVER leave the user's device in any form that allows reconstruction. |
|                                                                              |
|   PERMITTED:                                                                 |
|   â€¢ Cryptographic hash of biometric (non-reversible)                         |
|   â€¢ Zero-knowledge proof about biometric                                     |
|   â€¢ Encrypted biometric where ONLY user has key                              |
|                                                                              |
|   PROHIBITED:                                                                |
|   â€¢ Raw biometric to any server                                              |
|   â€¢ Encrypted biometric where server has key                                 |
|   â€¢ "Anonymized" biometric (still reconstructable)                           |
|   â€¢ Biometric "for debugging"                                                |
|   â€¢ Biometric "with user consent" (consent doesn't change the law)           |
|   â€¢ Biometric embeddings/vectors to server (reconstructable)                 |
|   â€¢ Face templates to server                                                 |
|                                                                              |
+------------------------------------------------------------------------------+
```

**VALIDATION:** Any network packet containing >1KB of data derived from biometric source MUST be inspectable and proven to be non-reversible.

---

## LAW 2: CRYPTOGRAPHIC NON-NEGOTIABLES

```
+------------------------------------------------------------------------------+
|                                                                              |
|   CRYPTOGRAPHIC REQUIREMENTS                                                 |
|                                                                              |
|   KEY SIZES (MINIMUM):                                                       |
|   â€¢ Symmetric: 256 bits                                                      |
|   â€¢ Asymmetric (classical): 256 bits (EC) or 3072 bits (RSA)                 |
|   â€¢ Post-quantum KEM: ML-KEM-768 (NIST Level 3)                              |
|   â€¢ Post-quantum Signature: ML-DSA-65 (NIST Level 3)                         |
|   â€¢ Hash: 256 bits output minimum                                            |
|                                                                              |
|   ALGORITHMS (ALLOWED - PRIMARY):                                            |
|   â€¢ Symmetric: AES-256-GCM, ChaCha20-Poly1305                                |
|   â€¢ Hash: SHA-3-256, SHA-256, BLAKE3                                         |
|   â€¢ KEM: ML-KEM-768, X25519 (classical), HYBRID of both (RECOMMENDED)        |
|   â€¢ Signature: ML-DSA-65, Ed25519, SLH-DSA-SHAKE-128f                        |
|   â€¢ KDF: HKDF-SHA256, HKDF-SHA3-256, Argon2id (passwords only)               |
|                                                                              |
|   ALGORITHMS (PROHIBITED):                                                   |
|   â€¢ MD5, SHA-1 (any use)                                                     |
|   â€¢ DES, 3DES, RC4, Blowfish                                                 |
|   â€¢ RSA < 3072 bits                                                          |
|   â€¢ ECDSA with curves < 256 bits                                             |
|   â€¢ Any algorithm not explicitly listed above                                |
|                                                                              |
|   HYBRID MODE (MANDATORY FOR ALL NEW DEPLOYMENTS):                           |
|   â€¢ KEM: ML-KEM-768 + X25519 (both must succeed)                             |
|   â€¢ Signature: ML-DSA-65 + Ed25519 (both must verify)                        |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## LAW 3: CONSTANT-TIME REQUIREMENT

```
+------------------------------------------------------------------------------+
|                                                                              |
|   ALL operations on secret data MUST be constant-time.                       |
|                                                                              |
|   SECRET DATA INCLUDES:                                                      |
|   â€¢ Private keys                                                             |
|   â€¢ Session keys                                                             |
|   â€¢ Passwords                                                                |
|   â€¢ Biometric embeddings                                                     |
|   â€¢ Any data used in cryptographic operations                                |
|   â€¢ Comparison results before they are public                                |
|                                                                              |
|   CONSTANT-TIME MEANS:                                                       |
|   â€¢ No branching based on secret values                                      |
|   â€¢ No array indexing based on secret values                                 |
|   â€¢ No early returns based on secret values                                  |
|   â€¢ No variable-time CPU instructions on secrets                             |
|   â€¢ No cache-timing variations based on secrets                              |
|                                                                              |
|   VERIFICATION METHOD:                                                       |
|   â€¢ Run dudect with t-value threshold < 4.5                                  |
|   â€¢ Minimum 1 million measurements                                           |
|   â€¢ Test on target platform (not just dev machine)                           |
|   â€¢ Re-run after ANY change to crypto code                                   |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## LAW 4: SECRET ZEROIZATION

```
+------------------------------------------------------------------------------+
|                                                                              |
|   ALL secrets MUST be zeroized when no longer needed.                        |
|                                                                              |
|   ZEROIZATION REQUIREMENTS:                                                  |
|   â€¢ Use volatile writes (prevent compiler optimization)                      |
|   â€¢ Use memory barriers (prevent CPU reordering)                             |
|   â€¢ Call OS-provided secure zeroization when available                       |
|   â€¢ Verify zeroization in tests                                              |
|                                                                              |
|   RUST IMPLEMENTATION:                                                       |
|   â€¢ Use zeroize crate with Zeroize derive                                    |
|   â€¢ All secret types MUST implement Zeroize                                  |
|   â€¢ Use ZeroizeOnDrop for automatic cleanup                                  |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## LAW 5: DEFENSE IN DEPTH

```
+------------------------------------------------------------------------------+
|                                                                              |
|   Security controls MUST be layered. Single point of failure is PROHIBITED.  |
|                                                                              |
|   MINIMUM LAYERS:                                                            |
|   1. Network layer (TLS 1.3 minimum, certificate pinning)                    |
|   2. Protocol layer (message authentication, replay protection)              |
|   3. Application layer (input validation, output encoding)                   |
|   4. Data layer (encryption at rest, access control)                         |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## LAW 6: FAIL SECURE

```
+------------------------------------------------------------------------------+
|                                                                              |
|   On ANY error, system MUST fail to a SECURE state.                          |
|                                                                              |
|   FAIL SECURE MEANS:                                                         |
|   â€¢ Deny access on authentication error                                      |
|   â€¢ Deny access on authorization error                                       |
|   â€¢ Deny access on cryptographic error                                       |
|   â€¢ Deny access on timeout                                                   |
|   â€¢ Deny access on any unexpected condition                                  |
|                                                                              |
|   NEVER:                                                                     |
|   â€¢ Grant access because error handler failed                                |
|   â€¢ Use default-allow policies                                               |
|   â€¢ Bypass security for "usability"                                          |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## LAW 7: AUDITABILITY

```
+------------------------------------------------------------------------------+
|                                                                              |
|   ALL security-relevant events MUST be logged immutably.                     |
|                                                                              |
|   AUDIT LOG REQUIREMENTS:                                                    |
|   â€¢ Tamper-evident (hash chain, signed with ML-DSA-65)                       |
|   â€¢ Complete (all security events captured)                                  |
|   â€¢ Protected (only security team can access)                                |
|   â€¢ Retained (minimum 7 years for compliance)                                |
|                                                                              |
|   SECURITY-RELEVANT EVENTS:                                                  |
|   â€¢ Authentication success/failure                                           |
|   â€¢ Authorization decisions                                                  |
|   â€¢ Key operations (generation, rotation, destruction)                       |
|   â€¢ Configuration changes                                                    |
|   â€¢ Administrative actions                                                   |
|   â€¢ Cryptographic operations                                                 |
|                                                                              |
|   STORAGE: JEJAK telemetry engine with SIMPAN backend                        |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## LAW 8: ZERO THIRD-PARTY RUNTIME DEPENDENCIES

```
+------------------------------------------------------------------------------+
|                                                                              |
|   TERAS USES ZERO THIRD-PARTY RUNTIME COMPONENTS.                            |
|                                                                              |
|   This is the fundamental principle of v3.2.2.                               |
|                                                                              |
|   PERMITTED DEPENDENCIES:                                                    |
|   â€¢ Rust standard library (foundational, audited)                            |
|   â€¢ OS syscall interfaces (Linux, Windows, macOS)                            |
|   â€¢ Hardware interfaces (TPM, HSM, TEE, GPU)                                 |
|   â€¢ Pre-approved crates with formal waiver:                                  |
|     - tokio (async runtime - foundational)                                   |
|     - hashbrown (hash map - used by std)                                     |
|     - libc (FFI to C library - necessary for OS interface)                   |
|                                                                              |
|   PROHIBITED DEPENDENCIES (RUNTIME):                                         |
|   â€¢ External databases (PostgreSQL, MySQL, SQLite, Redis, MongoDB)           |
|   â€¢ External protocols (JSON, Protobuf, gRPC, GraphQL)                       |
|   â€¢ External orchestration (Kubernetes, Docker, Nomad)                       |
|   â€¢ External ML (PyTorch, TensorFlow, ONNX, TensorRT)                        |
|   â€¢ External monitoring (Prometheus, Grafana, Datadog)                       |
|   â€¢ External compression (zstd, lz4, brotli)                                 |
|   â€¢ External networking (OpenSSL, rustls, quinn)                             |
|   â€¢ ANY component not listed in PERMITTED                                    |
|                                                                              |
|   RATIONALE:                                                                 |
|   1. Supply chain security: No external attack surface                       |
|   2. Performance: Optimized for security workloads                           |
|   3. Auditability: Complete source control                                   |
|   4. Independence: No vendor lock-in or licensing issues                     |
|   5. Sovereignty: Malaysian-owned security stack                             |
|                                                                              |
|   IMPLEMENTATION:                                                            |
|   All functionality from prohibited dependencies is provided by              |
|   TERAS proprietary components detailed in PART II.                          |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

# PART II: TERAS INFRASTRUCTURE SPECIFICATION

## II.0: COMPONENT OVERVIEW

```
+------------------------------------------------------------------------------+
|                                                                              |
|   TERAS INFRASTRUCTURE COMPONENTS                                            |
|                                                                              |
|   +---------------------+--------------------------------------------------+ |
|   | Component           | Replaces                          | Status       | |
|   +---------------------+--------------------------------------------------+ |
|   | SIMPAN              | SQLite, PostgreSQL, DuckDB, Redis | REQUIRED     | |
|   | TUKAR               | JSON, Protobuf, FlatBuffers       | REQUIRED     | |
|   | ATUR                | Kubernetes, Nomad, K3s            | REQUIRED     | |
|   | MAMPAT              | zstd, lz4, brotli, gzip           | REQUIRED     | |
|   | AKAL                | PyTorch, TensorFlow, ONNX, TRT    | REQUIRED     | |
|   | JEJAK               | Prometheus, Grafana, Jaeger, ELK  | REQUIRED     | |
|   | NADI                | HTTPS, gRPC, QUIC, WebSocket      | REQUIRED     | |
|   | BEKAS               | Docker, containerd, runc          | REQUIRED     | |
|   | JALINAN             | Istio, Linkerd, Envoy             | REQUIRED     | |
|   +---------------------+--------------------------------------------------+ |
|                                                                              |
|   Each component is designed to be 10-10,000x better than industry best.     |
|   All components are implemented in Rust with formal verification.           |
|   All components integrate seamlessly with TERAS security infrastructure.    |
|                                                                              |
+------------------------------------------------------------------------------+
```

### COMPONENT DEPENDENCY GRAPH

```
                    +-------+
                    | TUKAR |  â† Foundation (no dependencies)
                    +-------+
                        â†‘
            +-----------+-----------+
            |                       |
        +-------+               +-------+
        |MAMPAT |               | NADI  |
        +-------+               +-------+
            â†‘                       â†‘
            +-----------+-----------+
                        |
                    +-------+
                    |SIMPAN |
                    +-------+
                        â†‘
        +---------------+---------------+
        |               |               |
    +-------+       +-------+       +-------+
    | JEJAK |       |  AKAL |       | ATUR  |
    +-------+       +-------+       +-------+
                                        â†‘
                                +-------+-------+
                                |               |
                            +-------+       +-------+
                            | BEKAS |       |JALINAN|
                            +-------+       +-------+
```

### BUILD ORDER (22 weeks total)

| Phase | Component | Duration | Justification |
|-------|-----------|----------|---------------|
| 1 | TUKAR | 2 weeks | Foundation for all communication |
| 2 | MAMPAT | 2 weeks | Required by storage and network |
| 3 | SIMPAN | 4 weeks | Required by all stateful components |
| 4 | NADI | 3 weeks | Required for distributed operation |
| 5 | JEJAK | 2 weeks | Required for observability |
| 6 | AKAL | 4 weeks | Required for ML-based products |
| 7 | BEKAS | 2 weeks | Required for cloud deployment |
| 8 | ATUR | 3 weeks | Orchestrates all components |
| - | JALINAN | parallel | Integrated into BEKAS |

---

## II.1: SIMPAN â€” TERAS DATABASE ENGINE

### II.1.1 PURPOSE AND PHILOSOPHY

SIMPAN (Malay: "store/keep") is TERAS's proprietary embedded database engine designed specifically for security workloads. Unlike general-purpose databases, SIMPAN is:

1. **Security-First**: Encryption at rest, constant-time operations, audit logging built-in
2. **Hybrid OLTP/OLAP**: Both transactional AND analytical queries optimized
3. **Post-Quantum Authenticated**: All data blocks signed with ML-DSA-65
4. **Tamper-Evident**: Hash chains verify data integrity

### II.1.2 ARCHITECTURE

```
SIMPAN ARCHITECTURE

+-----------------------------------------------------------------------+
|                           SIMPAN ENGINE                               |
+-----------------------------------------------------------------------+
|                                                                       |
|  +---------------------------+  +---------------------------+         |
|  |     QUERY PROCESSOR       |  |    STORAGE ENGINE         |         |
|  +---------------------------+  +---------------------------+         |
|  |                           |  |                           |         |
|  | +---------------------+   |  | +---------------------+   |         |
|  | | SQL Parser (subset) |   |  | | Page Manager        |   |         |
|  | +---------------------+   |  | +---------------------+   |         |
|  |          |                |  |          |                |         |
|  | +---------------------+   |  | +---------------------+   |         |
|  | | Query Planner       |   |  | | B+ Tree (OLTP)      |   |         |
|  | +---------------------+   |  | +---------------------+   |         |
|  |          |                |  |          |                |         |
|  | +---------------------+   |  | +---------------------+   |         |
|  | | Vectorized Executor |   |  | | Columnar Store      |   |         |
|  | +---------------------+   |  | | (OLAP)              |   |         |
|  |                           |  | +---------------------+   |         |
|  +---------------------------+  |          |                |         |
|                                 | +---------------------+   |         |
|                                 | | Encryption Layer    |   |         |
|                                 | | (AES-256-GCM)       |   |         |
|                                 | +---------------------+   |         |
|                                 |          |                |         |
|                                 | +---------------------+   |         |
|                                 | | Integrity Layer     |   |         |
|                                 | | (ML-DSA-65 sigs)    |   |         |
|                                 | +---------------------+   |         |
|                                 +---------------------------+         |
|                                                                       |
|  +---------------------------+  +---------------------------+         |
|  |     AUDIT SUBSYSTEM       |  |    REPLICATION           |         |
|  +---------------------------+  +---------------------------+         |
|  | Every operation logged    |  | Synchronous replication  |         |
|  | Tamper-evident audit log  |  | Raft consensus           |         |
|  | Cryptographic timestamps  |  | Multi-datacenter support |         |
|  +---------------------------+  +---------------------------+         |
|                                                                       |
+-----------------------------------------------------------------------+
```

### II.1.3 PERFORMANCE TARGETS (MUST EXCEED)

| Metric | Industry Best (DuckDB/SQLite) | SIMPAN Target | Factor |
|--------|-------------------------------|---------------|--------|
| Point lookup | 20Î¼s (SQLite) | **2Î¼s** | 10x faster |
| Range scan (1M rows) | 50ms (DuckDB) | **5ms** | 10x faster |
| Aggregation (100M rows) | 500ms (DuckDB) | **50ms** | 10x faster |
| Write throughput | 100K ops/s (RocksDB) | **1M ops/s** | 10x faster |
| Encryption overhead | 30% typical | **<5%** | 6x better |
| Memory efficiency | 2.3GB (DuckDB 100M) | **230MB** | 10x better |

### II.1.4 SECURITY PROPERTIES

| Property | Implementation |
|----------|----------------|
| **Encryption at Rest** | AES-256-GCM per page, keys in teras-kunci |
| **Encryption in Transit** | NADI protocol with ML-KEM-768 |
| **Data Authentication** | ML-DSA-65 signature per page |
| **Audit Logging** | Automatic, tamper-evident, to teras-jejak |
| **Access Control** | Capability-based, per-table granularity |
| **Constant-Time Operations** | No data-dependent timing in key paths |
| **Zeroization** | All sensitive data zeroized on close |

### II.1.5 DATA TYPES

```rust
/// SIMPAN native data types
pub enum SimpanType {
    // Integers (all constant-time comparison)
    I8, I16, I32, I64, I128,
    U8, U16, U32, U64, U128,
    
    // Floating point
    F32, F64,
    
    // Text (UTF-8, length-prefixed)
    Text { max_len: u32 },
    
    // Binary (for cryptographic data)
    Blob { max_len: u32 },
    
    // Timestamps (nanosecond precision)
    Timestamp,
    
    // Boolean
    Bool,
    
    // UUID (128-bit)
    Uuid,
    
    // Security-specific types
    SecretText { max_len: u32 },  // Auto-zeroized
    SecretBlob { max_len: u32 },  // Auto-zeroized
    Signature,                     // ML-DSA-65 signature (3293 bytes)
    PublicKey,                     // ML-DSA-65 or ML-KEM public key
    Hash,                          // SHA3-256 hash (32 bytes)
}
```

### II.1.6 PAGE FORMAT

```
SIMPAN PAGE FORMAT (16KB default)

+----------+--------+----------------------------------------------------+
| Offset   | Size   | Field                                              |
+----------+--------+----------------------------------------------------+
| 0        | 4      | magic (0x53494D50 = "SIMP")                        |
| 4        | 2      | version (0x0100)                                   |
| 6        | 1      | page_type (0=data, 1=index, 2=overflow)            |
| 7        | 1      | flags                                              |
| 8        | 8      | page_id (unique identifier)                        |
| 16       | 8      | sequence_number (monotonic)                        |
| 24       | 32     | prev_page_hash (SHA3-256)                          |
| 56       | 8      | timestamp (nanoseconds since epoch)                |
| 64       | 12     | nonce (for AES-256-GCM)                            |
| 76       | 16     | auth_tag (AES-256-GCM authentication tag)          |
| 92       | 4      | data_len (length of decrypted data)                |
| 96       | 16188  | encrypted_data (AES-256-GCM ciphertext)            |
| 16284    | 100    | reserved (future use)                              |
| 16384    | 3293   | signature (ML-DSA-65 over bytes 0-16383)           |
+----------+--------+----------------------------------------------------+

Total page size: 19677 bytes (16KB data + overhead)
```

---

## II.2: TUKAR â€” TERAS BINARY PROTOCOL

### II.2.1 PURPOSE AND PHILOSOPHY

TUKAR (Malay: "exchange") is TERAS's proprietary binary serialization protocol. Unlike general-purpose protocols:

1. **Zero-Copy Access**: Data can be read directly from buffer without parsing
2. **Schema Enforcement**: Compile-time type safety
3. **Constant-Time Parsing**: No data-dependent branches
4. **Built-in Authentication**: Every message can be signed
5. **Version Evolution**: Forward and backward compatible

### II.2.2 PERFORMANCE TARGETS (MUST EXCEED)

| Metric | Industry Best | TUKAR Target | Factor |
|--------|---------------|--------------|--------|
| Serialization | 660MB/s (LZ4 raw) | **2GB/s** | 3x faster |
| Deserialization | 3.5GB/s (LZ4) | **10GB/s** | 3x faster |
| Parse latency | 77ns (FlatBuffers) | **25ns** | 3x faster |
| Memory allocation | 0 (FlatBuffers) | **0** | Equal |
| Size overhead | ~10% (FlatBuffers) | **<5%** | 2x better |

### II.2.3 MESSAGE FORMAT

```
TUKAR MESSAGE FORMAT

+----------+--------+----------------------------------------------------+
| Offset   | Size   | Field                                              |
+----------+--------+----------------------------------------------------+
| 0        | 4      | magic (0x54554B41 = "TUKA")                        |
| 4        | 2      | version (0x0100)                                   |
| 6        | 2      | schema_id (identifies message type)                |
| 8        | 4      | flags (signed, compressed, encrypted, etc.)        |
| 12       | 4      | payload_len                                        |
| 16       | N      | payload (schema-defined fields)                    |
| 16+N     | 32     | checksum (SHA3-256 of bytes 0 to 16+N-1)           |
| 48+N     | 3293   | signature (ML-DSA-65, optional based on flags)     |
+----------+--------+----------------------------------------------------+
```

### II.2.4 SCHEMA DEFINITION (TUKAR-LANG)

```
// Example TUKAR schema definition
schema ThreatIndicator {
    version: 1;
    
    fields {
        id: u64 @0;                    // Field at offset 0
        indicator_type: u8 @8;         // Field at offset 8
        value: bytes[256] @9;          // Fixed-size field
        confidence: f32 @265;          // Float at offset 265
        first_seen: timestamp @269;    // 8-byte timestamp
        last_seen: timestamp @277;
        source_id: u32 @285;
        signature: sig @289;           // ML-DSA-65 signature
    }
    
    constraints {
        indicator_type in [1, 2, 3, 4, 5, 6, 7];
        confidence >= 0.0 && confidence <= 1.0;
    }
}
```

---

## II.3: ATUR â€” TERAS ORCHESTRATION ENGINE

### II.3.1 PURPOSE AND PHILOSOPHY

ATUR (Malay: "arrange/organize") is TERAS's proprietary workload orchestration engine. Unlike general-purpose orchestrators:

1. **Security-Workload Specific**: Optimized for TERAS components only
2. **Minimal Attack Surface**: Single binary, no plugins
3. **Built-in mTLS**: All communication authenticated
4. **Integrated Identity**: Uses teras-kunci for all crypto
5. **Audit by Default**: All actions logged to teras-jejak

### II.3.2 ARCHITECTURE

```
ATUR ARCHITECTURE

+-----------------------------------------------------------------------+
|                           ATUR CONTROL PLANE                          |
+-----------------------------------------------------------------------+
|                                                                       |
|  +---------------------------+  +---------------------------+         |
|  |     JADUAL (Scheduler)    |  |    DAFTAR (Registry)      |         |
|  +---------------------------+  +---------------------------+         |
|  | Bin-packing algorithm     |  | Service discovery         |         |
|  | Affinity/anti-affinity    |  | Health checking           |         |
|  | Resource accounting       |  | Version management        |         |
|  +---------------------------+  +---------------------------+         |
|                                                                       |
|  +---------------------------+  +---------------------------+         |
|  |   SIMPANAN (State Store)  |  |    DASAR (Policy Engine)  |         |
|  +---------------------------+  +---------------------------+         |
|  | Raft consensus            |  | RBAC enforcement          |         |
|  | SIMPAN-backed             |  | Network policies          |         |
|  | Replicated across nodes   |  | Resource quotas           |         |
|  +---------------------------+  +---------------------------+         |
|                                                                       |
|  +---------------------------+                                        |
|  |    KAWALAN (Control)      |                                        |
|  +---------------------------+                                        |
|  | API server                |                                        |
|  | Auth (NADI)               |                                        |
|  | Admission control         |                                        |
|  +---------------------------+                                        |
|                                                                       |
+-----------------------------------------------------------------------+
                                 |
                                 | NADI (secure channel)
                                 |
+-----------------------------------------------------------------------+
|                           ATUR DATA PLANE                             |
+-----------------------------------------------------------------------+
|                                                                       |
|  +---------------------------+  +---------------------------+         |
|  |     EJEN (Node Agent)     |  |    BEKAS (Runtime)        |         |
|  +---------------------------+  +---------------------------+         |
|  | Resource monitoring       |  | Process isolation         |         |
|  | Health reporting          |  | Namespace/cgroup mgmt     |         |
|  | Log collection            |  | Network virtualization    |         |
|  +---------------------------+  +---------------------------+         |
|                                                                       |
+-----------------------------------------------------------------------+
```

### II.3.3 PERFORMANCE TARGETS

| Metric | Industry Best (K8s/Nomad) | ATUR Target | Factor |
|--------|---------------------------|-------------|--------|
| Schedule latency | 100ms (Nomad) | **10ms** | 10x faster |
| Control plane memory | 512MB (K8s) | **64MB** | 8x better |
| Agent memory | 128MB (kubelet) | **16MB** | 8x better |
| Cluster scale | 5000 nodes (K8s) | **10000 nodes** | 2x better |
| Pod startup | 500ms (K8s) | **50ms** | 10x faster |
| Health check latency | 10ms | **1ms** | 10x faster |
| mTLS handshake | 50ms (Istio) | **5ms** (ML-KEM) | 10x faster |

### II.3.4 SECURITY PROPERTIES

| Property | Implementation |
|----------|----------------|
| **mTLS Everywhere** | All node communication via NADI with ML-KEM-768 |
| **No External Etcd** | SIMPAN-backed state store |
| **Signed Deployments** | All deployment specs ML-DSA-65 signed |
| **Network Isolation** | eBPF-based network policies |
| **Secret Management** | Integrated with teras-kunci |
| **Audit Logging** | All operations to teras-jejak |

---

## II.4: MAMPAT â€” TERAS COMPRESSION ENGINE

### II.4.1 PURPOSE AND PHILOSOPHY

MAMPAT (Malay: "compress/compact") is TERAS's proprietary compression engine. Unlike general-purpose compressors:

1. **Constant-Time Decompression**: No data-dependent timing leaks
2. **Security-Aware**: Resistant to compression oracle attacks (CRIME/BREACH)
3. **Multi-Level**: Different algorithms for different use cases
4. **Integrated Integrity**: Compressed data includes checksum

### II.4.2 COMPRESSION LEVELS

| Level | Name | Algorithm Basis | Use Case |
|-------|------|-----------------|----------|
| **0** | MAMPAT-CEPAT (fast) | LZ4-inspired | Real-time streams |
| **1** | MAMPAT-BIASA (normal) | zstd-inspired | General storage |
| **2** | MAMPAT-KUAT (strong) | LZMA-inspired | Archival |
| **3** | MAMPAT-SELAMAT (secure) | Constant-time LZ | Encrypted data |

### II.4.3 PERFORMANCE TARGETS

| Level | Compression Speed | Decompression Speed | Ratio |
|-------|-------------------|---------------------|-------|
| MAMPAT-CEPAT | **1.5 GB/s** | **5 GB/s** | 2.0:1 |
| MAMPAT-BIASA | **300 MB/s** | **2 GB/s** | 3.0:1 |
| MAMPAT-KUAT | **30 MB/s** | **500 MB/s** | 4.0:1 |
| MAMPAT-SELAMAT | **200 MB/s** | **1 GB/s** | 2.5:1 |

### II.4.4 COMPRESSED BLOCK FORMAT

```
MAMPAT BLOCK FORMAT

+----------+--------+----------------------------------------------------+
| Offset   | Size   | Field                                              |
+----------+--------+----------------------------------------------------+
| 0        | 4      | magic (0x4D414D50 = "MAMP")                        |
| 4        | 1      | version                                            |
| 5        | 1      | level (0-3)                                        |
| 6        | 2      | flags                                              |
| 8        | 4      | original_size                                      |
| 12       | 4      | compressed_size                                    |
| 16       | 32     | checksum (SHA3-256 of original data)               |
| 48       | N      | compressed_data                                    |
+----------+--------+----------------------------------------------------+
```

### II.4.5 MAMPAT-SELAMAT (Secure Mode)

```
+------------------------------------------------------------------------------+
|                                                                              |
|   MAMPAT-SELAMAT is specifically designed for encrypted/sensitive data:      |
|                                                                              |
|   â€¢ Constant-time decompression (no timing side channels)                    |
|   â€¢ Resistant to compression oracle attacks (CRIME/BREACH)                   |
|   â€¢ Deterministic output (same input = same output)                          |
|   â€¢ Suitable for encrypted data compression                                  |
|                                                                              |
|   USE CASES:                                                                 |
|   â€¢ Forensic evidence compression                                            |
|   â€¢ Encrypted database pages                                                 |
|   â€¢ Secure network transmission                                              |
|   â€¢ Audit log compression                                                    |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## II.5: AKAL â€” TERAS ML RUNTIME

### II.5.1 PURPOSE AND PHILOSOPHY

AKAL (Malay: "intelligence/wisdom") is TERAS's proprietary ML inference runtime. Unlike general-purpose ML frameworks:

1. **Inference-Only**: No training, minimal attack surface
2. **Deterministic**: Bit-exact reproducible results
3. **Security-Focused**: Constant-time where possible, no external models
4. **Optimized for Security ML**: Face detection, liveness, anomaly detection

### II.5.2 SUPPORTED OPERATIONS

| Category | Operations |
|----------|------------|
| **Linear Algebra** | MatMul, Conv2D, Dense, BatchNorm |
| **Activations** | ReLU, Sigmoid (constant-time), Tanh (constant-time), Softmax (constant-time) |
| **Pooling** | MaxPool, AvgPool, GlobalAvgPool |
| **Normalization** | LayerNorm, BatchNorm, InstanceNorm |
| **Special** | Attention, Embedding, Dropout (inference=identity), Resize, Concat, Split |
| **Quantization** | Quantize, Dequantize |

### II.5.3 MODEL FORMAT

```
AKAL MODEL FORMAT (.akal)

+----------+--------+----------------------------------------------------+
| Offset   | Size   | Field                                              |
+----------+--------+----------------------------------------------------+
| 0        | 4      | magic (0x414B414C = "AKAL")                        |
| 4        | 2      | version (0x0001)                                   |
| 6        | 2      | model_type                                         |
| 8        | 4      | flags (quantized, constant_time, etc.)             |
| 12       | 32     | model_hash (SHA3-256 of weights)                   |
| 44       | 32     | training_hash (SHA3-256 of training data manifest) |
| 76       | 8      | timestamp (training completion time)               |
| 84       | 8      | weights_offset                                     |
| 92       | 8      | weights_size                                       |
| 100      | 8      | graph_offset                                       |
| 108      | 8      | graph_size                                         |
| 116      | 8      | metadata_offset                                    |
| 124      | 8      | metadata_size                                      |
| 132      | 3293   | signature (ML-DSA-65 over header + weights)        |
| 3425     | ...    | [weights section - MAMPAT compressed]              |
| ...      | ...    | [graph section - TUKAR encoded]                    |
| ...      | ...    | [metadata section - TUKAR encoded]                 |
+----------+--------+----------------------------------------------------+
```

### II.5.4 PERFORMANCE TARGETS

| Model Type | Industry Best | AKAL Target | Factor |
|------------|---------------|-------------|--------|
| Face Detection | 5ms (RetinaFace) | **1ms** | 5x faster |
| Liveness Check | 10ms | **2ms** | 5x faster |
| Deepfake Detection | 50ms | **10ms** | 5x faster |
| Anomaly Detection | 1ms | **0.2ms** | 5x faster |

### II.5.5 AKAL GRAPH OPERATORS (TUKAR SCHEMA)

```
enum AkalOp {
    // Tensor operations
    MATMUL = 0x01,
    CONV2D = 0x02,
    DEPTHWISE_CONV2D = 0x03,
    DENSE = 0x04,
    
    // Activations (constant-time implementations)
    RELU = 0x10,
    SIGMOID_CT = 0x11,       // Constant-time sigmoid
    TANH_CT = 0x12,          // Constant-time tanh
    SOFTMAX_CT = 0x13,       // Constant-time softmax
    GELU = 0x14,
    
    // Normalization
    BATCH_NORM = 0x20,
    LAYER_NORM = 0x21,
    INSTANCE_NORM = 0x22,
    
    // Pooling
    MAX_POOL = 0x30,
    AVG_POOL = 0x31,
    GLOBAL_AVG_POOL = 0x32,
    
    // Special
    ATTENTION = 0x40,        // Self-attention block
    EMBEDDING = 0x41,
    DROPOUT = 0x42,          // Identity in inference
    RESIZE = 0x43,
    CONCAT = 0x44,
    SPLIT = 0x45,
    
    // Quantization
    QUANTIZE = 0x50,
    DEQUANTIZE = 0x51,
}
```

---

## II.6: JEJAK â€” TERAS TELEMETRY ENGINE

### II.6.1 PURPOSE AND PHILOSOPHY

JEJAK (Malay: "trace/footprint") is TERAS's proprietary telemetry and observability engine:

1. **Unified Telemetry**: Metrics, logs, traces in one system
2. **Tamper-Evident**: All logs cryptographically chained
3. **Real-Time Analysis**: Stream processing for threat detection
4. **Long-Term Storage**: Compressed archival with integrity

### II.6.2 TELEMETRY TYPES

| Type | Format | Retention | Use Case |
|------|--------|-----------|----------|
| **Metrics** | Time-series (SIMPAN) | 90 days hot, 7 years cold | Performance monitoring |
| **Logs** | Structured (TUKAR) | 30 days hot, 7 years cold | Debugging, compliance |
| **Traces** | Distributed (TUKAR) | 7 days hot, 90 days cold | Request tracking |
| **Audit** | Signed events (TUKAR) | 7 years (LAW 7) | Compliance, forensics |

### II.6.3 QUERY LANGUAGE (JEJAK-QL)

```sql
// Find all failed authentication attempts in last hour
FROM audit
WHERE event_type = 'auth_failed'
  AND timestamp > now() - 1h
GROUP BY source_ip
HAVING count() > 10
ORDER BY count() DESC;

// Trace a request across services
TRACE request_id = 'abc123'
WITH metrics, logs
SHOW timeline;

// Anomaly detection
FROM metrics
WHERE metric = 'request_latency'
  AND value > percentile(0.99, 1h)
ALERT 'latency_spike';
```

---

## II.7: NADI â€” TERAS NETWORK PROTOCOL

### II.7.1 PURPOSE AND PHILOSOPHY

NADI (Malay: "pulse/vein") is TERAS's proprietary secure network protocol:

1. **Post-Quantum Secure**: ML-KEM-768 key exchange
2. **Zero-RTT Option**: Resumption for known peers
3. **Built-in Reliability**: Retransmission, ordering
4. **Multiplexed Streams**: Multiple logical channels per connection

### II.7.2 PROTOCOL STACK

```
NADI PROTOCOL STACK

+-----------------------------------------------------------------------+
|                        APPLICATION LAYER                              |
|   (TUKAR messages, SIMPAN replication, JEJAK telemetry)               |
+-----------------------------------------------------------------------+
|                        STREAM LAYER                                   |
|   Stream multiplexing, flow control, prioritization                   |
+-----------------------------------------------------------------------+
|                        RELIABILITY LAYER                              |
|   ACKs, retransmission, ordering, FEC                                 |
+-----------------------------------------------------------------------+
|                        SECURITY LAYER                                 |
|   ML-KEM-768 handshake, AES-256-GCM encryption                        |
+-----------------------------------------------------------------------+
|                        TRANSPORT LAYER                                |
|   UDP datagrams, congestion control                                   |
+-----------------------------------------------------------------------+
```

### II.7.3 HANDSHAKE

```
NADI HANDSHAKE (Post-Quantum)

1. Client â†’ Server: ClientHello + ML-KEM-768 ephemeral public key
2. Server â†’ Client: ServerHello + ML-KEM-768 encapsulation + certificate
3. Client â†’ Server: Finished (encrypted with derived key)
4. [Optional] 0-RTT resumption using session tickets

SECURITY FEATURES:
â€¢ ML-KEM-768 key exchange (post-quantum)
â€¢ AES-256-GCM transport encryption
â€¢ ML-DSA-65 server authentication
â€¢ Perfect forward secrecy
â€¢ Zero-RTT resumption (with replay protection)
â€¢ Multiplexed streams (no head-of-line blocking)
```

---

## II.8: BEKAS â€” TERAS CONTAINER RUNTIME

### II.8.1 PURPOSE AND PHILOSOPHY

BEKAS (Malay: "container/vessel") is TERAS's proprietary container runtime:

1. **Minimal**: Only features needed for TERAS workloads
2. **Security-Hardened**: Seccomp, namespaces, capabilities restricted
3. **Integrated Identity**: Containers have cryptographic identity
4. **No Image Registry**: Images embedded in deployment specs

### II.8.2 CONTAINER SPECIFICATION

```rust
/// BEKAS container specification
pub struct BekasSpec {
    /// Container identity (cryptographic, signed by deployment)
    pub identity: ContainerIdentity,
    
    /// Executable (embedded, not pulled from registry)
    pub executable: Vec<u8>,
    pub executable_hash: [u8; 32],
    
    /// Resource limits
    pub resources: ResourceLimits,
    
    /// Network configuration
    pub network: NetworkConfig,
    
    /// Allowed syscalls (whitelist)
    pub syscalls: Vec<Syscall>,
    
    /// Capabilities (minimal set)
    pub capabilities: Capabilities,
    
    /// Environment (non-secret)
    pub environment: HashMap<String, String>,
    
    /// Secrets (from teras-kunci)
    pub secrets: Vec<SecretRef>,
    
    /// Health probes
    pub liveness_probe: Probe,
    pub readiness_probe: Probe,
    pub startup_probe: Probe,
    
    /// ML-DSA-65 signature over entire spec
    pub signature: [u8; 3293],
}
```

### II.8.3 SECURITY FEATURES

| Feature | Implementation |
|---------|----------------|
| Cryptographic identity | ML-KEM-768 key pair per container |
| Embedded executables | No registry pull (no Docker Hub, no gcr.io) |
| Syscall whitelist | Seccomp with minimal allowed syscalls |
| Namespace isolation | PID, NET, MNT, UTS, IPC, USER |
| Capability dropping | Only NET_BIND_SERVICE for 80/443 |
| Read-only rootfs | No writes to root filesystem |
| No privilege escalation | no_new_privileges enforced |

---

## II.9: JALINAN â€” TERAS SERVICE MESH

### II.9.1 PURPOSE AND PHILOSOPHY

JALINAN (Malay: "connection/weave") is TERAS's proprietary service mesh:

1. **mTLS Everywhere**: ML-KEM-768 handshake for all service communication
2. **No Sidecar Proxies**: Integrated directly into BEKAS runtime
3. **Native Service Discovery**: Via DAFTAR registry
4. **All Telemetry to JEJAK**: Unified observability

### II.9.2 FEATURES

```
+------------------------------------------------------------------------------+
|                                                                              |
|   JALINAN SERVICE MESH FEATURES                                              |
|                                                                              |
|   â€¢ mTLS everywhere (ML-KEM-768 handshake, AES-256-GCM transport)            |
|   â€¢ No sidecar proxies (integrated into BEKAS runtime)                       |
|   â€¢ Native service discovery (via DAFTAR registry)                           |
|   â€¢ Load balancing (round-robin, least-connections, weighted)                |
|   â€¢ Circuit breaking (configurable thresholds)                               |
|   â€¢ Retry policies (with jitter)                                             |
|   â€¢ Timeout enforcement                                                      |
|   â€¢ Rate limiting (per-service, per-source)                                  |
|   â€¢ All telemetry to JEJAK                                                   |
|                                                                              |
+------------------------------------------------------------------------------+
```

### II.9.3 CIRCUIT BREAKER CONFIGURATION

```rust
pub struct CircuitBreakerConfig {
    pub max_connections: u32,         // Max concurrent connections
    pub max_pending_requests: u32,    // Max queued requests
    pub max_requests: u32,            // Max requests per connection
    pub max_retries: u32,             // Max retries
    pub consecutive_errors: u32,      // Errors to trip circuit
    pub interval_seconds: u32,        // Sliding window
    pub base_ejection_time_ms: u32,   // Initial ejection duration
    pub max_ejection_percent: u8,     // Max % of hosts ejected
}
```

### II.9.4 RETRY POLICY

```rust
pub struct RetryPolicy {
    pub max_attempts: u32,
    pub per_try_timeout_ms: u32,
    pub retry_on: Vec<RetryCondition>,
    pub backoff_base_ms: u32,
    pub backoff_max_ms: u32,
}

pub enum RetryCondition {
    CONNECT_FAILURE,
    REFUSED_STREAM,
    UNAVAILABLE,
    CANCELLED,
    DEADLINE_EXCEEDED,
    INTERNAL,
    RESOURCE_EXHAUSTED,
}
```

---

# PART III: ML TRAINING PIPELINE (BENTENG)

This section specifies the ML model training, validation, and deployment requirements for BENTENG eKYC/identity verification.

**ALL ML INFERENCE USES AKAL. NO PYTORCH, NO TENSORFLOW, NO ONNX IN PRODUCTION.**

---

## LAW B-8: ML MODEL GOVERNANCE

```
+------------------------------------------------------------------------------+
|                                                                              |
|   ALL ML models used in BENTENG MUST be:                                     |
|                                                                              |
|   1. PROPRIETARY: Trained and owned by TERAS, no external models             |
|   2. VERIFIED: Model weights signed with ML-DSA-65                           |
|   3. DETERMINISTIC: Bit-exact reproducible inference                         |
|   4. AUDITABLE: Complete training provenance recorded                        |
|   5. FAIR: Bias testing across all demographic groups                        |
|                                                                              |
|   External ML frameworks (PyTorch, TensorFlow, ONNX) are PROHIBITED          |
|   in production. Training may use external tools, but deployment             |
|   MUST convert to AKAL format (.akal) with full verification.                |
|                                                                              |
|   RUNTIME: AKAL (TERAS proprietary) ONLY                                     |
|   MODEL FORMAT: .akal (TERAS proprietary) ONLY                               |
|   TELEMETRY: JEJAK (TERAS proprietary) ONLY                                  |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## III.1: MODEL REGISTRY

All BENTENG ML models are registered, versioned, and governed through the TERAS Model Registry backed by SIMPAN.

| Model ID | Name | Purpose | Input | Output | Performance Target |
|----------|------|---------|-------|--------|-------------------|
| **BENT-001** | LivenessDetector | Detect live human vs replay/print | 224x224 RGB | probability [0,1] | **<1ms** inference |
| **BENT-002** | DeepfakeDetector | Detect AI-generated faces | 256x256 RGB | probability [0,1] | **<10ms** inference |
| **BENT-003** | FaceQuality | Assess face image quality | 112x112 RGB | quality score [0,100] | **<0.5ms** inference |
| **BENT-004** | PADModel | Presentation Attack Detection | 224x224 RGB | attack_type, confidence | **<2ms** inference |
| **BENT-005** | AdversarialRobust | Detect adversarial perturbations | 224x224 RGB | perturbed: bool, type | **<5ms** inference |
| **BENT-006** | BiasMitigation | Calibrate predictions across groups | features | calibrated_score | **<0.1ms** inference |

---

## III.2: TRAINING DATA REQUIREMENTS

```
+------------------------------------------------------------------------------+
|                       TRAINING DATA DIVERSITY REQUIREMENTS                   |
+------------------------------------------------------------------------------+
|                                                                              |
|   ALL training datasets for face-related models MUST meet these quotas:      |
|                                                                              |
|   AGE DISTRIBUTION (within Â±5% tolerance):                                   |
|   +------------------+------------------+                                    |
|   | Age Range        | Required %       |                                    |
|   +------------------+------------------+                                    |
|   | 18-30            | 25%              |                                    |
|   | 31-50            | 35%              |                                    |
|   | 51-70            | 25%              |                                    |
|   | 70+              | 15%              |                                    |
|   +------------------+------------------+                                    |
|                                                                              |
|   GENDER DISTRIBUTION:                                                       |
|   â€¢ Male: 45-55%                                                             |
|   â€¢ Female: 45-55%                                                           |
|                                                                              |
|   SKIN TONE DISTRIBUTION (Monk Skin Tone Scale):                             |
|   â€¢ Each of 10 Monk scale tones: 8-12% representation                        |
|   â€¢ Maximum variance between any two tones: 4%                               |
|                                                                              |
|   GEOGRAPHIC REPRESENTATION:                                                 |
|   â€¢ Southeast Asia (primary market): â‰¥40%                                    |
|   â€¢ East Asia: â‰¥15%                                                          |
|   â€¢ South Asia: â‰¥15%                                                         |
|   â€¢ Middle East/North Africa: â‰¥10%                                           |
|   â€¢ Sub-Saharan Africa: â‰¥10%                                                 |
|   â€¢ Europe/Americas: â‰¥10%                                                    |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## III.3: ATTACK SAMPLE REQUIREMENTS

| Attack Type | Minimum Samples | Variety Requirements |
|-------------|-----------------|----------------------|
| **Print Attack** | 10,000 | â‰¥5 printer types, â‰¥10 paper types, â‰¥3 lighting conditions |
| **Replay Attack** | 10,000 | â‰¥10 screen types, â‰¥5 resolutions, â‰¥3 refresh rates |
| **2D Mask** | 5,000 | â‰¥20 mask styles, â‰¥5 materials |
| **3D Mask** | 2,000 | â‰¥10 mask types, silicon/resin/paper |
| **3D Model** | 2,000 | â‰¥5 3D printing methods |
| **Deepfake** | 20,000 | â‰¥10 generation methods (StyleGAN, etc.) |
| **Face Swap** | 10,000 | â‰¥5 swap algorithms |
| **Adversarial** | 10,000 | â‰¥5 perturbation methods (FGSM, PGD, C&W) |

---

## III.4: PERFORMANCE THRESHOLDS

```rust
/// Required performance thresholds for BENTENG models
/// These are MINIMUM requirements, not targets

pub const PERFORMANCE_THRESHOLDS: ModelThresholds = ModelThresholds {
    // Accuracy metrics
    accuracy: Threshold::min(0.990),           // â‰¥99.0%
    false_accept_rate: Threshold::max(0.001),  // â‰¤0.1% (FAR)
    false_reject_rate: Threshold::max(0.020),  // â‰¤2.0% (FRR)
    auc_roc: Threshold::min(0.995),            // â‰¥0.995
    
    // Latency metrics (on reference hardware)
    inference_latency_p50: Threshold::max(Duration::from_millis(1)),
    inference_latency_p99: Threshold::max(Duration::from_millis(5)),
    
    // Resource metrics
    peak_memory: Threshold::max(100 * 1024 * 1024),  // â‰¤100MB
    model_size: Threshold::max(50 * 1024 * 1024),    // â‰¤50MB compressed
    
    // Security metrics
    adversarial_accuracy: Threshold::min(0.950),     // â‰¥95% under attack
};

/// Reference hardware for latency measurements
pub const REFERENCE_HARDWARE: HardwareSpec = HardwareSpec {
    cpu: "Apple M1",  // Or equivalent: Intel i7-1165G7
    memory: "8GB",
    accelerator: None,  // CPU-only measurements
};
```

---

## III.5: BIAS TESTING REQUIREMENTS

```
+------------------------------------------------------------------------------+
|                         BIAS TESTING REQUIREMENTS                            |
+------------------------------------------------------------------------------+
|                                                                              |
|   ALL models MUST pass bias testing before deployment:                       |
|                                                                              |
|   ACCURACY VARIANCE BY DEMOGRAPHIC:                                          |
|   â€¢ Maximum accuracy variance across age groups: â‰¤5%                         |
|   â€¢ Maximum accuracy variance across gender: â‰¤3%                             |
|   â€¢ Maximum accuracy variance across skin tones: â‰¤5%                         |
|   â€¢ Maximum accuracy variance across geographic origin: â‰¤5%                  |
|                                                                              |
|   FALSE REJECTION RATE (FRR) VARIANCE:                                       |
|   â€¢ Maximum FRR variance across any demographic: â‰¤3%                         |
|   â€¢ No single demographic group FRR > 5% (absolute)                          |
|                                                                              |
|   FALSE ACCEPTANCE RATE (FAR) VARIANCE:                                      |
|   â€¢ Maximum FAR variance across any demographic: â‰¤0.05%                      |
|   â€¢ No single demographic group FAR > 0.2% (absolute)                        |
|                                                                              |
|   TESTING METHODOLOGY:                                                       |
|   â€¢ Stratified test set with â‰¥1,000 samples per demographic group            |
|   â€¢ 5-fold cross-validation for stability                                    |
|   â€¢ Statistical significance testing (p < 0.05)                              |
|                                                                              |
|   Models failing ANY bias threshold are REJECTED.                            |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## III.6: DEPLOYMENT PIPELINE

```
DEPLOYMENT PIPELINE
Using TERAS proprietary infrastructure ONLY

â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                             â”‚
â”‚  STAGE 1: TRAINING                                                          â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                                       â”‚
â”‚  â€¢ Environment: Isolated training cluster (air-gapped optional)             â”‚
â”‚  â€¢ Framework: Internal training framework (PyTorch allowed for training)    â”‚
â”‚  â€¢ Data: Verified training data with provenance                             â”‚
â”‚  â€¢ Output: Raw model weights + training logs                                â”‚
â”‚  â€¢ Logging: All to JEJAK (training telemetry)                               â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 2: CONVERSION                                                        â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                                        â”‚
â”‚  â€¢ Input: Trained weights (any format)                                      â”‚
â”‚  â€¢ Process: Convert to AKAL format (.akal)                                  â”‚
â”‚  â€¢ Optimization: Graph optimization, constant folding                       â”‚
â”‚  â€¢ Quantization: INT8 where applicable                                      â”‚
â”‚  â€¢ Output: Optimized AKAL model                                             â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 3: VALIDATION                                                        â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                                       â”‚
â”‚  â€¢ Accuracy testing (â‰¥99.0%)                                                â”‚
â”‚  â€¢ Bias testing (all demographics)                                          â”‚
â”‚  â€¢ Performance testing (latency, memory)                                    â”‚
â”‚  â€¢ Security testing (adversarial robustness)                                â”‚
â”‚  â€¢ Output: Validation report (TUKAR format)                                 â”‚
â”‚  â€¢ Storage: Report to SIMPAN (model registry)                               â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 4: SIGNING                                                           â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                                           â”‚
â”‚  â€¢ Compute model hash (SHA3-256)                                            â”‚
â”‚  â€¢ Sign with ML-DSA-65 (model signing key)                                  â”‚
â”‚  â€¢ Embed signature in .akal file                                            â”‚
â”‚  â€¢ Register hash in model registry (SIMPAN)                                 â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 5: STAGING                                                           â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                                           â”‚
â”‚  â€¢ Deploy to staging environment (ATUR orchestration)                       â”‚
â”‚  â€¢ Integration testing with full BENTENG pipeline                           â”‚
â”‚  â€¢ Load testing (10x expected production load)                              â”‚
â”‚  â€¢ Duration: Minimum 72 hours                                               â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 6: CANARY                                                            â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                                            â”‚
â”‚  â€¢ Deploy to 10% of production traffic                                      â”‚
â”‚  â€¢ Monitor: Error rates, latency, accuracy (JEJAK)                          â”‚
â”‚  â€¢ Duration: Minimum 72 hours                                               â”‚
â”‚  â€¢ Rollback trigger: Any metric degradation >1%                             â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 7: PRODUCTION                                                        â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                                       â”‚
â”‚  â€¢ Full production deployment (ATUR rolling update)                         â”‚
â”‚  â€¢ Continuous monitoring (JEJAK)                                            â”‚
â”‚  â€¢ Model hash verified on every inference request                           â”‚
â”‚                                                                             â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

---

## III.7: AKAL RUNTIME IMPLEMENTATION

```rust
use teras_akal::{Model, InferenceSession, Tensor};
use teras_kunci::verify_signature;
use teras_mampat::decompress;

/// AKAL inference session
/// NO ONNX Runtime. NO TensorRT. AKAL ONLY.
pub struct AkalSession {
    model: Model,
    model_hash: [u8; 32],
}

impl AkalSession {
    /// Load and verify AKAL model
    pub fn load(model_bytes: &[u8]) -> Result<Self, AkalError> {
        // Parse header
        let header = AkalHeader::parse(&model_bytes[0..3425])?;
        
        // Verify magic
        if header.magic != 0x414B414C {
            return Err(AkalError::InvalidMagic);
        }
        
        // Verify signature BEFORE loading weights
        let signature = &model_bytes[132..3425];
        let signed_data = &model_bytes[0..132];
        
        if !verify_signature(signature, signed_data, &MODEL_SIGNING_KEY)? {
            return Err(AkalError::InvalidSignature);
        }
        
        // Decompress weights (MAMPAT)
        let weights_compressed = &model_bytes[header.weights_offset as usize..
                                              (header.weights_offset + header.weights_size) as usize];
        let weights = teras_mampat::decompress(weights_compressed)?;
        
        // Verify weights hash
        let weights_hash = teras_kunci::sha3_256(&weights);
        if weights_hash != header.model_hash {
            return Err(AkalError::WeightsHashMismatch);
        }
        
        // Parse graph (TUKAR format)
        let graph_bytes = &model_bytes[header.graph_offset as usize..
                                       (header.graph_offset + header.graph_size) as usize];
        let graph = AkalGraph::from_tukar(graph_bytes)?;
        
        // Build model
        let model = Model::from_graph_and_weights(graph, weights)?;
        
        Ok(Self {
            model,
            model_hash: header.model_hash,
        })
    }
    
    /// Run inference (constant-time for sensitive operations)
    pub fn infer(&self, input: &Tensor) -> Result<Tensor, AkalError> {
        // Verify input shape
        if input.shape() != self.model.input_shape() {
            return Err(AkalError::ShapeMismatch);
        }
        
        // Run inference
        // AKAL uses constant-time implementations for sigmoid/softmax
        // to prevent timing side-channel attacks
        let output = self.model.forward(input)?;
        
        Ok(output)
    }
    
    /// Get model hash for verification
    pub fn model_hash(&self) -> &[u8; 32] {
        &self.model_hash
    }
}
```

---

## III.8: RETRAINING TRIGGERS

| Trigger | Condition | Action |
|---------|-----------|--------|
| **Performance Degradation** | Accuracy drops >2% from baseline | Immediate investigation, retraining if confirmed |
| **New Attack Type** | Novel attack method detected | Collect samples, retrain with new attack class |
| **Bias Detection** | Demographic variance exceeds threshold | Retrain with rebalanced data |
| **Quarterly Review** | Every 90 days | Scheduled evaluation and potential update |
| **Security Advisory** | ML vulnerability disclosed | Evaluate impact, patch if affected |
| **Regulatory Change** | Compliance requirement update | Adapt model/pipeline as needed |

---

# PART IV: FORENSIC EVIDENCE CHAIN (MENARA)

This section specifies the forensic evidence collection and chain-of-custody requirements for MENARA mobile security.

**ALL STORAGE USES SIMPAN. NO THIRD-PARTY DATABASES.**

---

## LAW M-7: FORENSIC EVIDENCE INTEGRITY

```
+------------------------------------------------------------------------------+
|                                                                              |
|   ALL forensic evidence collected by MENARA MUST be:                         |
|                                                                              |
|   1. TAMPER-EVIDENT: Any modification is detectable                          |
|   2. LEGALLY ADMISSIBLE: Chain of custody maintained                         |
|   3. COMPLETE: All relevant context preserved                                |
|   4. TIMESTAMPED: Accurate, verifiable timestamps                            |
|   5. SIGNED: Cryptographically authenticated (ML-DSA-65)                     |
|                                                                              |
|   Evidence that does not meet ALL criteria is INADMISSIBLE.                  |
|                                                                              |
|   STORAGE: SIMPAN embedded database ONLY                                     |
|   SERIALIZATION: TUKAR binary protocol ONLY                                  |
|   COMPRESSION: MAMPAT-SELAMAT (constant-time) ONLY                           |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## IV.1: EVIDENCE TYPES

| Evidence Type | ID | Description | Collection Trigger |
|---------------|-----|-------------|-------------------|
| **PROCESS** | 0x01 | Process execution evidence | Suspicious process detected |
| **NETWORK** | 0x02 | Network connection evidence | Malicious connection detected |
| **FILE** | 0x03 | File system evidence | Malicious file detected |
| **REGISTRY** | 0x04 | Configuration/registry evidence | Suspicious config change |
| **MEMORY** | 0x05 | Memory snapshot evidence | Memory anomaly detected |
| **LOG** | 0x06 | System log evidence | Security event logged |
| **ARTIFACT** | 0x07 | General artifact evidence | IOC match detected |

---

## IV.2: EVIDENCE BLOCK STRUCTURE (TUKAR FORMAT)

```
FORENSIC EVIDENCE BLOCK FORMAT (TUKAR Schema)
Using TERAS proprietary binary protocol - NO JSON, NO PROTOBUF

+----------+--------+----------------------------------------------------+
| Offset   | Size   | Field                                              |
+----------+--------+----------------------------------------------------+
| 0        | 4      | magic (0x54455246 = "TERF" - TERAS Forensic)       |
| 4        | 2      | version (0x0001)                                   |
| 6        | 2      | schema_id (TUKAR schema: forensic_evidence)        |
| 8        | 32     | previous_hash (SHA3-256 of previous block)         |
| 40       | 8      | timestamp (nanoseconds since epoch)                |
| 48       | 8      | sequence_number (monotonic, LE)                    |
| 56       | 32     | device_id (SHA3-256 of device identity)            |
| 88       | 1      | evidence_type (see table above)                    |
| 89       | 32     | evidence_hash (SHA3-256 of raw evidence)           |
| 121      | 4      | evidence_size (uncompressed size, LE)              |
| 125      | 4      | compressed_size (MAMPAT-SELAMAT output size)       |
| 129      | N      | payload (MAMPAT-SELAMAT compressed evidence)       |
| 129+N    | 2      | collector_version (MENARA version)                 |
| 131+N    | 32     | payload_checksum (SHA3-256 of compressed payload)  |
| 163+N    | 3293   | signature (ML-DSA-65 signature over bytes 0-163+N) |
+----------+--------+----------------------------------------------------+

Total size: 3456 bytes + payload
```

---

## IV.3: TUKAR SCHEMA DEFINITION

```
// TUKAR schema for forensic evidence
// Compiled to Rust at build time

schema ForensicEvidenceBlock {
    version: 1;
    schema_id: 0x0001;
    
    fields {
        magic: u32 @0 = 0x54455246;
        version: u16 @4 = 0x0001;
        schema_id: u16 @6;
        previous_hash: hash @8;
        timestamp: timestamp @40;
        sequence_number: u64 @48;
        device_id: hash @56;
        evidence_type: u8 @88;
        evidence_hash: hash @89;
        evidence_size: u32 @121;
        compressed_size: u32 @125;
        payload: bytes[max: 10485760] @129;  // 10MB max
        collector_version: u16 @variable;
        payload_checksum: hash @variable;
        signature: sig @variable;
    }
    
    constraints {
        evidence_type in [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07];
        sequence_number > 0 || previous_hash == zeros;
        evidence_size <= 10485760;
    }
}

schema GenesisBlock {
    version: 1;
    schema_id: 0x0002;
    
    fields {
        magic: u32 @0 = 0x54455246;
        version: u16 @4 = 0x0001;
        schema_id: u16 @6 = 0x0002;
        previous_hash: hash @8 = zeros;      // Genesis has no previous
        timestamp: timestamp @40;
        sequence_number: u64 @48 = 0;        // Genesis is always 0
        device_id: hash @56;
        evidence_type: u8 @88 = 0x00;        // Genesis type
        attestation: DeviceAttestation @89;
        signature: sig @variable;
    }
}

schema DeviceAttestation {
    version: 1;
    
    fields {
        manufacturer: text[64] @0;
        model: text[64] @64;
        os_version: text[32] @128;
        security_patch: text[16] @160;
        key_attestation: bytes[max: 4096] @176;
        menara_version: text[16] @variable;
    }
}
```

---

## IV.4: SIMPAN STORAGE SCHEMA

```rust
/// SIMPAN table definitions for forensic evidence
/// NO SQLITE. NO POSTGRESQL. SIMPAN ONLY.

// Create evidence chain table
simpan::create_table!(
    EvidenceBlocks,
    columns: {
        id: U64 PRIMARY KEY AUTO_INCREMENT,
        sequence_number: U64 UNIQUE NOT NULL,
        version: U16 NOT NULL,
        previous_hash: Hash NOT NULL,
        timestamp: Timestamp NOT NULL,
        device_id: Hash NOT NULL,
        evidence_type: U8 NOT NULL,
        evidence_hash: Hash NOT NULL,
        evidence_size: U32 NOT NULL,
        compressed_size: U32 NOT NULL,
        payload: SecretBlob NOT NULL,  // Auto-zeroized
        collector_version: U16 NOT NULL,
        payload_checksum: Hash NOT NULL,
        signature: Signature NOT NULL,
        created_at: Timestamp NOT NULL DEFAULT NOW(),
    },
    indexes: {
        idx_timestamp: (timestamp),
        idx_evidence_type: (evidence_type),
        idx_sequence: (sequence_number),
    },
    constraints: {
        valid_sequence: sequence_number >= 0,
        valid_type: evidence_type BETWEEN 0 AND 7,
    },
    security: {
        encryption: AES_256_GCM,
        page_signatures: ML_DSA_65,
        audit_logging: ENABLED,
    }
);
```

---

## IV.5: CHAIN VALIDATION IMPLEMENTATION

```rust
use teras_core::ForensicError;
use teras_kunci::{verify_signature, sha3_256};
use teras_simpan::Database;

/// Validates entire evidence chain integrity
/// Uses SIMPAN queries for efficient validation
pub fn validate_chain(db: &Database) -> Result<ChainValidation, ForensicError> {
    // Get total block count
    let count: u64 = db.query_one("SELECT COUNT(*) FROM evidence_blocks")?;
    
    if count == 0 {
        return Err(ForensicError::EmptyChain);
    }
    
    // Validate genesis block
    let genesis: EvidenceBlock = db.query_one(
        "SELECT * FROM evidence_blocks WHERE sequence_number = 0"
    )?;
    
    if genesis.previous_hash != [0u8; 32] {
        return Err(ForensicError::InvalidGenesis("previous_hash must be zeros"));
    }
    
    if !verify_signature(&genesis.signature, &genesis.to_bytes())? {
        return Err(ForensicError::InvalidSignature(0));
    }
    
    let device_id = genesis.device_id;
    
    // Validate chain in batches (SIMPAN efficient batch query)
    const BATCH_SIZE: u64 = 1000;
    let mut validated = 0u64;
    
    while validated < count {
        // Use SIMPAN's vectorized execution for batch validation
        let batch_results: Vec<ValidationResult> = db.query(
            r#"
            SELECT 
                e.sequence_number,
                e.device_id = ?1 as device_ok,
                e.previous_hash = LAG(sha3_256(e.*)) OVER (ORDER BY sequence_number) as hash_ok,
                e.sequence_number = LAG(sequence_number) OVER (ORDER BY sequence_number) + 1 as seq_ok,
                e.timestamp >= LAG(timestamp) OVER (ORDER BY sequence_number) as ts_ok,
                verify_signature(e.signature, e.*) as sig_ok
            FROM evidence_blocks e
            WHERE e.sequence_number >= ?2 AND e.sequence_number < ?3
            ORDER BY e.sequence_number
            "#,
            (device_id, validated, validated + BATCH_SIZE)
        )?;
        
        for result in batch_results {
            if !result.device_ok {
                return Err(ForensicError::DeviceIdMismatch(result.sequence_number));
            }
            if !result.hash_ok && result.sequence_number > 0 {
                return Err(ForensicError::ChainBroken(result.sequence_number));
            }
            if !result.seq_ok && result.sequence_number > 0 {
                return Err(ForensicError::SequenceGap(result.sequence_number));
            }
            if !result.ts_ok && result.sequence_number > 0 {
                return Err(ForensicError::TimestampRegression(result.sequence_number));
            }
            if !result.sig_ok {
                return Err(ForensicError::InvalidSignature(result.sequence_number));
            }
        }
        
        validated += BATCH_SIZE;
    }
    
    Ok(ChainValidation {
        block_count: count,
        device_id,
        chain_valid: true,
    })
}
```

---

## IV.6: COMPRESSION SPECIFICATION

```rust
/// Evidence compression using MAMPAT-SELAMAT (constant-time)
/// NO ZSTD. NO LZ4. MAMPAT ONLY.
///
/// MAMPAT-SELAMAT is specifically designed for encrypted/sensitive data:
/// - Constant-time decompression (no timing side channels)
/// - Resistant to compression oracle attacks (CRIME/BREACH)
/// - Deterministic output for same input

use teras_mampat::{Level, compress, decompress};

pub fn compress_evidence(raw_evidence: &[u8]) -> Result<Vec<u8>, MampatError> {
    // ALWAYS use SELAMAT level for forensic evidence
    // This ensures constant-time decompression
    compress(raw_evidence, Level::Selamat)
}

pub fn decompress_evidence(compressed: &[u8]) -> Result<Vec<u8>, MampatError> {
    decompress(compressed)
}

/// Compression configuration for forensic evidence
pub const FORENSIC_COMPRESSION_CONFIG: MampatConfig = MampatConfig {
    level: Level::Selamat,
    max_input_size: 10 * 1024 * 1024,  // 10MB
    deterministic: true,
    constant_time: true,
};
```

---

## IV.7: STORAGE REQUIREMENTS

```
+------------------------------------------------------------------------------+
|                                                                              |
|   STORAGE REQUIREMENTS                                                       |
|                                                                              |
|   DATABASE: SIMPAN embedded (TERAS proprietary)                              |
|   - NO SQLite                                                                |
|   - NO PostgreSQL                                                            |
|   - NO Redis                                                                 |
|   - NO external databases of any kind                                        |
|                                                                              |
|   ENCRYPTION: AES-256-GCM with device-bound key (teras-kunci)                |
|   SIGNATURES: ML-DSA-65 per page (SIMPAN built-in)                           |
|   LOCATION: App-private storage (not accessible to other apps)               |
|   BACKUP: Via NADI protocol to enterprise SIEM (optional)                    |
|                                                                              |
|   RETENTION POLICY:                                                          |
|   - Minimum retention: 90 days                                               |
|   - Maximum on-device: 365 days (configurable)                               |
|   - Remote archive: 7 years (enterprise, per LAW 7)                          |
|                                                                              |
|   SIZE LIMITS:                                                               |
|   - Per-block payload: 10 MB maximum                                         |
|   - Total chain size: 1 GB maximum on device                                 |
|   - Compression: MAMPAT-SELAMAT level (constant-time)                        |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## IV.8: REMOTE SYNC SPECIFICATION (ENTERPRISE)

```
REMOTE SYNC PROTOCOL (Optional, Enterprise Only)
Using NADI protocol - NO HTTPS, NO gRPC, NO external protocols

Purpose: Backup evidence chain to enterprise SIEM/SOAR

TRANSPORT:
- Protocol: NADI (TERAS proprietary, post-quantum secure)
- Authentication: ML-KEM-768 handshake + device attestation
- Encryption: AES-256-GCM (negotiated via NADI)

SYNC STRATEGY:
- Incremental: Only new blocks since last sync
- Batched: Up to 100 blocks per NADI message
- Compressed: MAMPAT-BIASA for batch (not SELAMAT, as transport is encrypted)
- Signed: Batch signature for integrity

MESSAGE FORMAT (TUKAR):

schema SyncRequest {
    version: 1;
    schema_id: 0x0010;
    
    fields {
        device_id: hash @0;
        batch_start_seq: u64 @32;
        batch_end_seq: u64 @40;
        blocks: ForensicEvidenceBlock[] @48;
        batch_hash: hash @variable;
        device_signature: sig @variable;
    }
}

schema SyncResponse {
    version: 1;
    schema_id: 0x0011;
    
    fields {
        status: u8 @0;  // 0=accepted, 1=rejected, 2=retry
        last_accepted_seq: u64 @1;
        server_timestamp: timestamp @9;
        next_sync_after: u32 @17;  // seconds
        server_signature: sig @21;
    }
}

ERROR HANDLING:
- Network failure: Retry with exponential backoff via NADI
- Signature failure: Alert admin, suspend sync
- Storage full: Alert admin, continue local collection
```

---

## IV.9: FORENSIC API

```rust
/// ForensicChain - Main API for evidence management
/// All storage via SIMPAN. All serialization via TUKAR.
pub struct ForensicChain {
    db: simpan::Database,
    device_key: teras_kunci::DeviceSigningKey,
    config: ForensicConfig,
}

impl ForensicChain {
    /// Create new evidence chain (genesis block)
    pub fn initialize(
        db_path: &Path,
        device_attestation: DeviceAttestation
    ) -> Result<Self, ForensicError> {
        let db = simpan::Database::create(db_path, simpan::Config {
            encryption: simpan::Encryption::Aes256Gcm,
            page_size: simpan::PageSize::K16,
            page_signatures: true,
            audit_logging: true,
        })?;
        
        // Create genesis block
        let genesis = GenesisBlock::new(device_attestation);
        db.insert("evidence_blocks", genesis.to_tukar())?;
        
        Ok(Self { db, device_key, config })
    }
    
    /// Add evidence to chain
    pub fn add_evidence(&mut self, evidence: Evidence) -> Result<u64, ForensicError> {
        // Get previous block
        let prev: EvidenceBlock = self.db.query_one(
            "SELECT * FROM evidence_blocks ORDER BY sequence_number DESC LIMIT 1"
        )?;
        
        // Compress evidence
        let compressed = teras_mampat::compress(
            &evidence.data,
            teras_mampat::Level::Selamat
        )?;
        
        // Build new block
        let block = EvidenceBlock {
            previous_hash: sha3_256(&prev.to_tukar()),
            timestamp: teras_core::now_nanos(),
            sequence_number: prev.sequence_number + 1,
            device_id: self.device_key.device_id(),
            evidence_type: evidence.evidence_type,
            evidence_hash: sha3_256(&evidence.data),
            evidence_size: evidence.data.len() as u32,
            compressed_size: compressed.len() as u32,
            payload: compressed,
            collector_version: MENARA_VERSION,
            payload_checksum: sha3_256(&compressed),
            signature: [0u8; 3293],  // Placeholder
        };
        
        // Sign block
        let block_bytes = block.to_tukar_unsigned();
        let signature = self.device_key.sign(&block_bytes)?;
        let block = block.with_signature(signature);
        
        // Insert via SIMPAN
        self.db.insert("evidence_blocks", block.to_tukar())?;
        
        Ok(block.sequence_number)
    }
    
    /// Validate entire chain integrity
    pub fn validate(&self) -> Result<ChainValidation, ForensicError> {
        validate_chain(&self.db)
    }
    
    /// Export chain for legal/compliance purposes
    pub fn export(&self, range: Option<SequenceRange>) -> Result<Vec<u8>, ForensicError> {
        let blocks: Vec<EvidenceBlock> = match range {
            Some(r) => self.db.query(
                "SELECT * FROM evidence_blocks WHERE sequence_number >= ?1 AND sequence_number <= ?2",
                (r.start, r.end)
            )?,
            None => self.db.query("SELECT * FROM evidence_blocks ORDER BY sequence_number", ())?
        };
        
        // Serialize to TUKAR format
        let export = ForensicExport {
            version: 1,
            export_timestamp: teras_core::now_nanos(),
            block_count: blocks.len() as u64,
            blocks,
        };
        
        Ok(export.to_tukar())
    }
}
```

---

# PART V: CONTAINER DEPLOYMENT (GAPURA)

This section specifies the container deployment and orchestration requirements for GAPURA WAF using TERAS proprietary infrastructure.

**ALL ORCHESTRATION USES ATUR. NO KUBERNETES. NO DOCKER. NO NOMAD.**

---

## LAW G-8: CONTAINER ORCHESTRATION

```
+------------------------------------------------------------------------------+
|                                                                              |
|   ALL GAPURA deployments MUST use TERAS proprietary orchestration:           |
|                                                                              |
|   1. ATUR: TERAS orchestration engine (replaces Kubernetes)                  |
|   2. BEKAS: TERAS container runtime (replaces Docker/containerd)             |
|   3. JALINAN: TERAS service mesh (replaces Istio/Linkerd)                    |
|   4. JEJAK: TERAS telemetry (replaces Prometheus/Grafana)                    |
|   5. NADI: TERAS network protocol (replaces HTTPS/gRPC)                      |
|                                                                              |
|   External orchestration systems are PROHIBITED:                             |
|   - NO Kubernetes, K3s, or any K8s distribution                              |
|   - NO Docker, containerd, or CRI-O                                          |
|   - NO Istio, Linkerd, or Envoy                                              |
|   - NO Prometheus, Grafana, or Datadog                                       |
|   - NO external container registries (no gcr.io, no Docker Hub)              |
|                                                                              |
|   Container images are EMBEDDED in deployment specifications,                |
|   not pulled from external registries.                                       |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## V.1: BEKAS CONTAINER SPECIFICATION (TUKAR)

```rust
/// BEKAS container specification (TUKAR format)
/// Replaces Docker/OCI container spec

schema BekasSpec {
    version: 1;
    schema_id: 0x0200;
    
    fields {
        // Identity (cryptographic)
        identity: ContainerIdentity @0;
        
        // Executable (EMBEDDED, not pulled)
        executable_hash: hash @variable;
        executable_size: u64 @variable;
        executable_data: bytes[max: 52428800] @variable;  // 50MB max
        
        // Resource limits
        cpu_millicores_request: u32 @variable;
        cpu_millicores_limit: u32 @variable;
        memory_bytes_request: u64 @variable;
        memory_bytes_limit: u64 @variable;
        
        // Security context
        run_as_uid: u32 @variable;
        run_as_gid: u32 @variable;
        read_only_rootfs: bool @variable;
        no_new_privileges: bool @variable;
        
        // Allowed syscalls (whitelist)
        allowed_syscalls: Syscall[] @variable;
        
        // Capabilities (minimal set)
        capabilities: Capability[] @variable;
        
        // Network configuration
        network_mode: NetworkMode @variable;
        exposed_ports: Port[] @variable;
        
        // Health checks
        liveness_probe: Probe @variable;
        readiness_probe: Probe @variable;
        startup_probe: Probe @variable;
        
        // Environment (non-secret only)
        environment: EnvVar[] @variable;
        
        // Secret references (from teras-kunci)
        secrets: SecretRef[] @variable;
        
        // Signature over entire spec
        signature: sig @variable;
    }
}

schema ContainerIdentity {
    version: 1;
    
    fields {
        service_id: uuid @0;
        deployment_id: uuid @16;
        replica_id: u32 @32;
        public_key: bytes[1312] @36;  // ML-KEM-768 public key
        attestation: bytes[max: 4096] @variable;
    }
}

enum NetworkMode {
    NONE = 0x00,        // No network access
    HOST = 0x01,        // Host network (restricted)
    BRIDGE = 0x02,      // Bridge network (default)
    JALINAN = 0x03,     // Service mesh network
}
```

---

## V.2: GAPURA CONTAINER DEFAULTS

```rust
/// Default GAPURA container configuration
/// Security-hardened for WAF workload

pub const GAPURA_CONTAINER_DEFAULTS: BekasDefaults = BekasDefaults {
    // Resource defaults
    cpu_millicores_request: 100,      // 0.1 CPU request
    cpu_millicores_limit: 2000,       // 2 CPU limit
    memory_bytes_request: 134_217_728,   // 128 MiB request
    memory_bytes_limit: 2_147_483_648,   // 2 GiB limit
    
    // Security context (MANDATORY)
    run_as_uid: 65532,                // nonroot user
    run_as_gid: 65532,                // nonroot group
    read_only_rootfs: true,           // No writes to root
    no_new_privileges: true,          // No privilege escalation
    
    // Allowed capabilities (MINIMAL)
    capabilities: &[
        Capability::NET_BIND_SERVICE, // Only for binding 80/443
    ],
    
    // Syscall whitelist (RESTRICTIVE)
    allowed_syscalls: GAPURA_SYSCALL_WHITELIST,
    
    // Health checks
    liveness_probe: Probe {
        probe_type: ProbeType::HTTP,
        path: "/healthz",
        port: 8080,
        initial_delay_seconds: 5,
        period_seconds: 5,
        timeout_seconds: 2,
        failure_threshold: 3,
    },
    
    readiness_probe: Probe {
        probe_type: ProbeType::HTTP,
        path: "/ready",
        port: 8080,
        initial_delay_seconds: 10,
        period_seconds: 10,
        timeout_seconds: 3,
        failure_threshold: 3,
    },
    
    startup_probe: Probe {
        probe_type: ProbeType::HTTP,
        path: "/healthz",
        port: 8080,
        initial_delay_seconds: 0,
        period_seconds: 5,
        timeout_seconds: 2,
        failure_threshold: 30,  // 150s max startup
    },
};

/// GAPURA syscall whitelist (minimal set for WAF operation)
pub const GAPURA_SYSCALL_WHITELIST: &[Syscall] = &[
    // File operations (read-only)
    Syscall::READ, Syscall::STAT, Syscall::FSTAT, Syscall::OPEN, Syscall::CLOSE,
    
    // Memory
    Syscall::MMAP, Syscall::MPROTECT, Syscall::MUNMAP, Syscall::BRK,
    
    // Network (essential for WAF)
    Syscall::SOCKET, Syscall::BIND, Syscall::LISTEN, Syscall::ACCEPT,
    Syscall::CONNECT, Syscall::SENDTO, Syscall::RECVFROM,
    
    // I/O multiplexing
    Syscall::EPOLL_CREATE, Syscall::EPOLL_CTL, Syscall::EPOLL_WAIT, Syscall::SELECT,
    
    // Process (minimal)
    Syscall::CLONE, Syscall::FUTEX, Syscall::EXIT,
    
    // Time
    Syscall::CLOCK_GETTIME, Syscall::GETTIMEOFDAY,
    
    // Misc
    Syscall::WRITE, Syscall::FCNTL, Syscall::IOCTL,
];
```

---

## V.3: JALINAN SERVICE MESH CONFIGURATION

```rust
/// JALINAN service mesh configuration for GAPURA
pub const GAPURA_JALINAN_CONFIG: JalinanConfig = JalinanConfig {
    mtls_enabled: true,
    mtls_mode: MtlsMode::Strict,
    load_balancer: LoadBalancer::LeastConnections,
    circuit_breaker: CircuitBreakerConfig {
        max_connections: 100,
        max_pending_requests: 1000,
        max_requests: 1000,
        max_retries: 3,
        consecutive_errors: 5,
        interval_seconds: 30,
        base_ejection_time_ms: 30000,
        max_ejection_percent: 50,
    },
    retry_policy: RetryPolicy {
        max_attempts: 3,
        per_try_timeout_ms: 10000,
        retry_on: vec![
            RetryCondition::CONNECT_FAILURE,
            RetryCondition::REFUSED_STREAM,
            RetryCondition::UNAVAILABLE,
        ],
        backoff_base_ms: 100,
        backoff_max_ms: 5000,
    },
    timeout_seconds: 30,
    rate_limit: RateLimitConfig::Disabled,  // Rate limiting at WAF layer
};
```

---

## V.4: GAPURA DEFAULT DEPLOYMENT

```rust
/// Default GAPURA deployment configuration
pub const GAPURA_DEPLOYMENT_DEFAULTS: GapuraDeploymentDefaults = GapuraDeploymentDefaults {
    // Replica configuration
    replicas_min: 3,                // Always at least 3 for HA
    replicas_max: 20,               // Max scale-out
    
    // Update strategy
    update_strategy: UpdateStrategy {
        strategy_type: StrategyType::RollingUpdate,
        max_unavailable: 1,         // At most 1 pod down during update
        max_surge: 2,               // Up to 2 extra pods during update
        min_ready_seconds: 30,      // Must be ready for 30s
    },
    
    // Autoscaling
    autoscale: AutoscaleConfig {
        enabled: true,
        target_cpu_percent: 70,
        target_memory_percent: 80,
        target_requests_per_second: 10000,
        scale_up_stabilization_seconds: 60,
        scale_down_stabilization_seconds: 300,
        min_replicas: 3,
        max_replicas: 20,
    },
    
    // Network policy (RESTRICTIVE)
    network_policy: NetworkPolicy {
        default_deny_ingress: true,
        default_deny_egress: true,
        ingress_rules: vec![
            IngressRule {
                from: Source::Any,         // Accept from anywhere
                ports: vec![80, 443],      // Only HTTP/HTTPS
            },
        ],
        egress_rules: vec![
            EgressRule {
                to: Destination::TerasServices,  // Only to other TERAS services
            },
        ],
    },
    
    // Affinity rules
    affinity: AffinityRules {
        // Spread across availability zones
        pod_anti_affinity: AntiAffinity::PreferredSpread {
            topology_key: "zone",
            weight: 100,
        },
        // Prefer nodes with SSD
        node_affinity: NodeAffinity::Preferred {
            selector: "storage=ssd",
            weight: 50,
        },
    },
};
```

---

## V.5: JEJAK OBSERVABILITY FOR GAPURA

```
JEJAK OBSERVABILITY FOR GAPURA
TERAS Proprietary - NO Prometheus, NO Grafana, NO Datadog

â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                             â”‚
â”‚   JEJAK-native observability replaces ALL external monitoring:              â”‚
â”‚                                                                             â”‚
â”‚   METRICS (replaces Prometheus):                                            â”‚
â”‚   â€¢ Request count, latency histograms, error rates                          â”‚
â”‚   â€¢ Resource utilization (CPU, memory, network)                             â”‚
â”‚   â€¢ WAF-specific: attacks blocked, rules triggered                          â”‚
â”‚   â€¢ Custom metrics via JEJAK SDK                                            â”‚
â”‚                                                                             â”‚
â”‚   LOGS (replaces ELK/Loki):                                                 â”‚
â”‚   â€¢ Structured logging (TUKAR format)                                       â”‚
â”‚   â€¢ Automatic context injection (request ID, trace ID)                      â”‚
â”‚   â€¢ Log levels: DEBUG, INFO, WARN, ERROR, FATAL                             â”‚
â”‚   â€¢ Full-text search via SIMPAN                                             â”‚
â”‚                                                                             â”‚
â”‚   TRACES (replaces Jaeger/Zipkin):                                          â”‚
â”‚   â€¢ Distributed tracing across TERAS services                               â”‚
â”‚   â€¢ Automatic span creation for service calls                               â”‚
â”‚   â€¢ Context propagation via NADI headers                                    â”‚
â”‚                                                                             â”‚
â”‚   ALERTS (replaces Alertmanager/PagerDuty):                                 â”‚
â”‚   â€¢ Rule-based alerting in JEJAK-QL                                         â”‚
â”‚   â€¢ Notification channels: NADI webhook, email, SMS                         â”‚
â”‚   â€¢ Alert aggregation and deduplication                                     â”‚
â”‚                                                                             â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

---

## V.6: GAPURA ALERT RULES

```rust
/// JEJAK alert rules for GAPURA
pub const GAPURA_ALERTS: &[JejakAlert] = &[
    JejakAlert {
        name: "GapuraHighErrorRate",
        query: r#"
            FROM metrics
            WHERE service = 'gapura'
              AND metric = 'request_error_rate'
              AND value > 0.01  -- More than 1% errors
              AND window = '5m'
            ALERT severity = 'critical'
        "#,
        for_duration: Duration::from_secs(60),
        severity: Severity::Critical,
    },
    
    JejakAlert {
        name: "GapuraHighLatency",
        query: r#"
            FROM metrics
            WHERE service = 'gapura'
              AND metric = 'request_latency_p99'
              AND value > 0.5  -- More than 500ms P99
              AND window = '5m'
            ALERT severity = 'warning'
        "#,
        for_duration: Duration::from_secs(300),
        severity: Severity::Warning,
    },
    
    JejakAlert {
        name: "GapuraAttackSpike",
        query: r#"
            FROM metrics
            WHERE service = 'gapura'
              AND metric = 'attacks_blocked'
              AND rate_increase > 10  -- 10x increase
              AND window = '5m'
            ALERT severity = 'warning'
        "#,
        for_duration: Duration::from_secs(60),
        severity: Severity::Warning,
    },
    
    JejakAlert {
        name: "GapuraPodCrashLoop",
        query: r#"
            FROM events
            WHERE service = 'gapura'
              AND event_type = 'container_restart'
              AND count > 3
              AND window = '10m'
            ALERT severity = 'critical'
        "#,
        for_duration: Duration::from_secs(0),  // Immediate
        severity: Severity::Critical,
    },
];
```

---

## V.7: ATUR PERFORMANCE TARGETS

| Metric | Kubernetes/Nomad Best | ATUR Target | Factor |
|--------|----------------------|-------------|--------|
| Schedule latency | 100ms | **10ms** | 10x faster |
| Control plane memory | 512MB | **64MB** | 8x less |
| Agent memory (per node) | 128MB | **16MB** | 8x less |
| Cluster scale | 5,000 nodes | **10,000 nodes** | 2x larger |
| Pod startup | 500ms | **50ms** | 10x faster |
| Health check latency | 10ms | **1ms** | 10x faster |
| mTLS handshake | 50ms (Istio) | **5ms** (ML-KEM) | 10x faster |

---

# PART VI: SBOM REQUIREMENTS

This section specifies Software Bill of Materials (SBOM) generation, validation, and attestation requirements for all TERAS products.

**ALL SBOM OPERATIONS USE TERAS PROPRIETARY FORMATS. NO SPDX. NO CycloneDX.**

---

## LAW UNIVERSAL-9: SOFTWARE TRANSPARENCY

```
+------------------------------------------------------------------------------+
|                                                                              |
|   ALL TERAS products MUST maintain complete software transparency:           |
|                                                                              |
|   1. COMPLETE: Every component, dependency, and transitive dep documented    |
|   2. SIGNED: SBOM cryptographically signed with ML-DSA-65                    |
|   3. VERIFIABLE: Build reproducibility from SBOM alone                       |
|   4. AUDITABLE: Full provenance chain for every component                    |
|   5. CURRENT: Updated with every build, release, and security patch          |
|                                                                              |
|   TERAS uses PROPRIETARY SBOM format (TERAS-BOM):                            |
|   - NOT SPDX (too permissive, lacks security focus)                          |
|   - NOT CycloneDX (external standard, not optimized for TERAS)               |
|   - NOT SWID (Windows-centric, not applicable)                               |
|                                                                              |
|   TERAS-BOM is designed specifically for:                                    |
|   - Zero third-party dependency verification                                 |
|   - Post-quantum signature verification                                      |
|   - Integration with TERAS build pipeline                                    |
|   - Security vulnerability correlation                                       |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## VI.1: TERAS-BOM FORMAT

```
TERAS-BOM FORMAT (TUKAR Schema)
TERAS Proprietary - NO SPDX, NO CycloneDX

+----------+--------+----------------------------------------------------+
| Offset   | Size   | Field                                              |
+----------+--------+----------------------------------------------------+
| 0        | 4      | magic (0x54424F4D = "TBOM")                        |
| 4        | 2      | version (0x0001)                                   |
| 6        | 2      | schema_id (0x0300)                                 |
| 8        | 32     | document_hash (SHA3-256 of entire SBOM)            |
| 40       | 8      | generation_timestamp                               |
| 48       | 32     | build_hash (SHA3-256 of build artifacts)           |
| 80       | 64     | product_name                                       |
| 144      | 32     | product_version                                    |
| 176      | 32     | supplier (always "TERAS Security Sdn Bhd")         |
| 208      | 4      | component_count                                    |
| 212      | 4      | dependency_count                                   |
| 216      | 4      | vulnerability_count (known at generation time)     |
| 220      | ...    | [components section]                               |
| ...      | ...    | [dependencies section]                             |
| ...      | ...    | [vulnerabilities section]                          |
| ...      | ...    | [build_info section]                               |
| ...      | ...    | [attestations section]                             |
| ...      | 3293   | signature (ML-DSA-65)                              |
+----------+--------+----------------------------------------------------+
```

---

## VI.2: COMPONENT ORIGINS

```
+------------------------------------------------------------------------------+
|                    ZERO THIRD-PARTY DEPENDENCY VERIFICATION                  |
+------------------------------------------------------------------------------+
|                                                                              |
|   The TERAS-BOM includes MANDATORY attestation for zero third-party deps.    |
|                                                                              |
|   PERMITTED COMPONENT ORIGINS:                                               |
|   +---------------------+------------------------------------------------+   |
|   | Origin              | Description                         | Status   |   |
|   +---------------------+------------------------------------------------+   |
|   | TERAS_INTERNAL      | Code written by TERAS team          | REQUIRED |   |
|   | RUST_STD            | Rust standard library               | PERMITTED|   |
|   | OS_INTERFACE        | OS syscalls (Linux, Windows, macOS) | PERMITTED|   |
|   | HARDWARE_INTERFACE  | TPM, HSM, TEE APIs                  | PERMITTED|   |
|   | APPROVED_CRATE      | Pre-approved crate (with waiver)    | RESTRICTED|  |
|   +---------------------+------------------------------------------------+   |
|                                                                              |
|   APPROVED CRATE WHITELIST (requires formal waiver):                         |
|   - tokio (async runtime - foundational, approved in architecture)           |
|   - hashbrown (hash map - used by std, approved)                             |
|   - libc (FFI to C library - necessary for OS interface)                     |
|                                                                              |
|   ALL OTHER EXTERNAL CRATES ARE PROHIBITED.                                  |
|                                                                              |
|   Verification process:                                                      |
|   1. Build system generates dependency graph                                 |
|   2. Each dependency checked against whitelist                               |
|   3. Non-whitelisted deps FAIL the build immediately                         |
|   4. ZERO_THIRD_PARTY attestation generated if all deps approved             |
|   5. Attestation signed with build system's ML-DSA-65 key                    |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## VI.3: TUKAR SCHEMA DEFINITIONS

```
// Component schema
schema Component {
    version: 1;
    
    fields {
        component_id: uuid @0;
        name: text[128] @16;
        version: text[32] @144;
        component_type: ComponentType @176;
        origin: ComponentOrigin @177;
        supplier: text[64] @178;
        sha3_256: hash @242;
        blake3: hash @274;
        license: LicenseInfo @306;
        security_critical: bool @variable;
        contains_crypto: bool @variable;
        network_capable: bool @variable;
        source_uri: text[256] @variable;
        source_commit: hash @variable;
        dependency_indices: u32[] @variable;
    }
}

enum ComponentType {
    LIBRARY = 0x01,
    FRAMEWORK = 0x02,
    APPLICATION = 0x03,
    OPERATING_SYSTEM = 0x04,
    CONTAINER = 0x05,
    FIRMWARE = 0x06,
    FILE = 0x07,
    DATA = 0x08,
}

enum ComponentOrigin {
    TERAS_INTERNAL = 0x01,       // Developed internally (REQUIRED for most)
    RUST_STD = 0x02,             // Rust standard library (PERMITTED)
    OS_INTERFACE = 0x03,         // OS syscall interface (PERMITTED)
    HARDWARE_INTERFACE = 0x04,   // Hardware API (PERMITTED)
    APPROVED_CRATE = 0x05,       // Pre-approved external (RESTRICTED)
}

// License types (Permitted)
enum LicenseType {
    TERAS_PROPRIETARY = 0x00,    // TERAS internal (default)
    MIT = 0x01,                  // Permitted for approved deps
    APACHE_2 = 0x02,             // Permitted for approved deps
    BSD_2 = 0x03,                // Permitted
    BSD_3 = 0x04,                // Permitted
    ISC = 0x05,                  // Permitted
    UNLICENSE = 0x06,            // Permitted
    // GPL variants NOT PERMITTED
    // LGPL variants NOT PERMITTED
    // AGPL variants NOT PERMITTED
}

// Vulnerability schema
schema Vulnerability {
    version: 1;
    
    fields {
        vuln_id: text[32] @0;
        component_index: u32 @32;
        severity: VulnerabilitySeverity @36;
        score: f32 @37;  // 0.0 - 10.0
        status: VulnerabilityStatus @41;
        description: text[512] @42;
        remediation: text[256] @variable;
        remediation_deadline: timestamp @variable;
    }
}

enum VulnerabilitySeverity {
    NONE = 0x00,
    LOW = 0x01,
    MEDIUM = 0x02,
    HIGH = 0x03,
    CRITICAL = 0x04,
}

enum VulnerabilityStatus {
    OPEN = 0x00,
    IN_PROGRESS = 0x01,
    MITIGATED = 0x02,
    RESOLVED = 0x03,
    ACCEPTED_RISK = 0x04,
    FALSE_POSITIVE = 0x05,
}

// Attestation schema
schema Attestation {
    version: 1;
    
    fields {
        attestation_type: AttestationType @0;
        attester_identity: hash @1;
        attestation_timestamp: timestamp @33;
        statement: text[512] @41;
        evidence_hash: hash @variable;
        signature: sig @variable;
    }
}

enum AttestationType {
    BUILD_PROVENANCE = 0x01,      // Build was from stated source
    CODE_REVIEW = 0x02,           // Code was reviewed
    SECURITY_AUDIT = 0x03,        // Security audit completed
    VULNERABILITY_SCAN = 0x04,    // Vulnerability scan completed
    LICENSE_COMPLIANCE = 0x05,    // License compliance verified
    DEPENDENCY_VERIFICATION = 0x06, // Dependencies verified
    ZERO_THIRD_PARTY = 0x07,      // Zero third-party dep attestation (MANDATORY)
}
```

---

## VI.4: SBOM GENERATION PIPELINE

```
TERAS-BOM GENERATION PIPELINE
Integrated into TERAS build system

â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                             â”‚
â”‚  STAGE 1: DEPENDENCY RESOLUTION                                             â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                         â”‚
â”‚  â€¢ Parse Cargo.toml/Cargo.lock                                              â”‚
â”‚  â€¢ Resolve all direct and transitive dependencies                           â”‚
â”‚  â€¢ Check each against APPROVED_CRATE whitelist                              â”‚
â”‚  â€¢ FAIL BUILD if non-whitelisted dep found                                  â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 2: COMPONENT ANALYSIS                                                â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                               â”‚
â”‚  â€¢ For each component:                                                      â”‚
â”‚    - Compute SHA3-256 and BLAKE3 hashes                                     â”‚
â”‚    - Extract license information                                            â”‚
â”‚    - Determine security properties (crypto, network, etc.)                  â”‚
â”‚    - Record source reference (commit hash, branch)                          â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 3: VULNERABILITY SCAN                                                â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                             â”‚
â”‚  â€¢ Scan against internal vulnerability database (SIMPAN)                    â”‚
â”‚  â€¢ Cross-reference with TERAS security advisories                           â”‚
â”‚  â€¢ Record all known vulnerabilities with status                             â”‚
â”‚  â€¢ FAIL BUILD if CRITICAL vulnerability unresolved                          â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 4: BUILD INFO COLLECTION                                             â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                            â”‚
â”‚  â€¢ Record build environment (Rust version, target, flags)                   â”‚
â”‚  â€¢ Record source information (repo, commit, branch)                         â”‚
â”‚  â€¢ Generate builder attestation                                             â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 5: ATTESTATION GENERATION                                            â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                            â”‚
â”‚  â€¢ BUILD_PROVENANCE attestation                                             â”‚
â”‚  â€¢ ZERO_THIRD_PARTY attestation (MANDATORY)                                 â”‚
â”‚  â€¢ VULNERABILITY_SCAN attestation                                           â”‚
â”‚  â€¢ LICENSE_COMPLIANCE attestation                                           â”‚
â”‚  â€¢ Each attestation signed with appropriate key                             â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 6: SBOM ASSEMBLY                                                     â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                                   â”‚
â”‚  â€¢ Assemble all sections into TERAS-BOM format (TUKAR)                      â”‚
â”‚  â€¢ Compute document hash                                                    â”‚
â”‚  â€¢ Sign entire SBOM with release signing key (ML-DSA-65)                    â”‚
â”‚                                                                             â”‚
â”‚           â†“                                                                 â”‚
â”‚                                                                             â”‚
â”‚  STAGE 7: STORAGE & DISTRIBUTION                                            â”‚
â”‚  â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•â•                                            â”‚
â”‚  â€¢ Store in SIMPAN (SBOM registry)                                          â”‚
â”‚  â€¢ Embed reference in release artifacts                                     â”‚
â”‚  â€¢ Publish to authorized consumers via NADI                                 â”‚
â”‚                                                                             â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

---

## VI.5: SIMPAN STORAGE SCHEMA

```rust
/// SIMPAN tables for SBOM storage
/// NO external SBOM databases. SIMPAN ONLY.

simpan::create_table!(
    SbomDocuments,
    columns: {
        id: U64 PRIMARY KEY AUTO_INCREMENT,
        document_hash: Hash UNIQUE NOT NULL,
        product_name: Text NOT NULL,
        product_version: Text NOT NULL,
        generation_timestamp: Timestamp NOT NULL,
        build_hash: Hash NOT NULL,
        component_count: U32 NOT NULL,
        vulnerability_count: U32 NOT NULL,
        sbom_data: Blob NOT NULL,  // Full TERAS-BOM (TUKAR format)
        signature: Signature NOT NULL,
        created_at: Timestamp NOT NULL DEFAULT NOW(),
    },
    indexes: {
        idx_product_version: (product_name, product_version),
        idx_build_hash: (build_hash),
        idx_timestamp: (generation_timestamp),
    },
    security: {
        encryption: AES_256_GCM,
        audit_logging: ENABLED,
    }
);

simpan::create_table!(
    SbomComponents,
    columns: {
        id: U64 PRIMARY KEY AUTO_INCREMENT,
        sbom_id: U64 NOT NULL REFERENCES SbomDocuments(id),
        component_id: Uuid NOT NULL,
        name: Text NOT NULL,
        version: Text NOT NULL,
        component_type: U8 NOT NULL,
        origin: U8 NOT NULL,
        sha3_hash: Hash NOT NULL,
        blake3_hash: Hash NOT NULL,
        security_critical: Bool NOT NULL,
        contains_crypto: Bool NOT NULL,
    },
    indexes: {
        idx_sbom_component: (sbom_id, component_id) UNIQUE,
        idx_name_version: (name, version),
        idx_hash: (sha3_hash),
    }
);

simpan::create_table!(
    SbomVulnerabilities,
    columns: {
        id: U64 PRIMARY KEY AUTO_INCREMENT,
        sbom_id: U64 NOT NULL REFERENCES SbomDocuments(id),
        vuln_id: Text NOT NULL,
        component_id: Uuid NOT NULL,
        severity: U8 NOT NULL,
        score: F32 NOT NULL,
        status: U8 NOT NULL,
        description: Text NOT NULL,
        remediation: Text,
        created_at: Timestamp NOT NULL DEFAULT NOW(),
        updated_at: Timestamp NOT NULL DEFAULT NOW(),
    },
    indexes: {
        idx_sbom_vuln: (sbom_id, vuln_id) UNIQUE,
        idx_severity: (severity),
        idx_status: (status),
    }
);

simpan::create_table!(
    SbomAttestations,
    columns: {
        id: U64 PRIMARY KEY AUTO_INCREMENT,
        sbom_id: U64 NOT NULL REFERENCES SbomDocuments(id),
        attestation_type: U8 NOT NULL,
        attester_identity: Hash NOT NULL,
        attestation_timestamp: Timestamp NOT NULL,
        statement: Text NOT NULL,
        evidence_hash: Hash NOT NULL,
        signature: Signature NOT NULL,
    },
    indexes: {
        idx_sbom_type: (sbom_id, attestation_type),
        idx_attester: (attester_identity),
    }
);
```

---

## VI.6: SBOM QUERY INTERFACE (JEJAK-QL)

```sql
-- Example JEJAK-QL queries for SBOM analysis
-- Uses SIMPAN tables, NOT external databases

-- Find all products with critical vulnerabilities
FROM sbom_vulnerabilities v
JOIN sbom_documents d ON v.sbom_id = d.id
WHERE v.severity = 4  -- CRITICAL
  AND v.status = 0    -- OPEN
GROUP BY d.product_name, d.product_version
ORDER BY v.score DESC;

-- List all components from non-TERAS origin
FROM sbom_components c
JOIN sbom_documents d ON c.sbom_id = d.id
WHERE c.origin != 1  -- NOT TERAS_INTERNAL
ORDER BY d.product_name, c.name;

-- Verify zero third-party attestation for all products
FROM sbom_documents d
LEFT JOIN sbom_attestations a ON d.id = a.sbom_id 
  AND a.attestation_type = 7  -- ZERO_THIRD_PARTY
WHERE a.id IS NULL
-- Returns products MISSING zero third-party attestation (VIOLATION);

-- Find components with cryptographic functionality
FROM sbom_components c
JOIN sbom_documents d ON c.sbom_id = d.id
WHERE c.contains_crypto = true
ORDER BY d.product_name, c.name;
```

---

## VI.7: COMPLIANCE REQUIREMENTS

```
+------------------------------------------------------------------------------+
|                         SBOM COMPLIANCE REQUIREMENTS                         |
+------------------------------------------------------------------------------+
|                                                                              |
|   REGULATORY COMPLIANCE:                                                     |
|   +----------------------------+----------------------------------------+    |
|   | Regulation                 | TERAS-BOM Compliance                   |    |
|   +----------------------------+----------------------------------------+    |
|   | US EO 14028                | Full component inventory, VEX support  |    |
|   | EU Cyber Resilience Act    | Vulnerability disclosure, updates      |    |
|   | NIST SP 800-218            | Secure SDLC attestations               |    |
|   | PCI DSS 4.0 (6.3)          | Software inventory, security patches   |    |
|   | ISO 27001 (A.12.6)         | Technical vulnerability management     |    |
|   | SOC 2 Type II              | Change management, integrity           |    |
|   +----------------------------+----------------------------------------+    |
|                                                                              |
|   TERAS-SPECIFIC REQUIREMENTS:                                               |
|   â€¢ ZERO_THIRD_PARTY attestation MANDATORY for all releases                  |
|   â€¢ All vulnerabilities tracked with remediation deadlines                   |
|   â€¢ SBOM generated for EVERY build (not just releases)                       |
|   â€¢ Attestation chain verifiable back to source commit                       |
|   â€¢ Build reproducibility verified (rebuild matches original hash)           |
|                                                                              |
|   RETENTION:                                                                 |
|   â€¢ SBOMs retained for life of product + 7 years                             |
|   â€¢ Vulnerability records retained indefinitely                              |
|   â€¢ Attestations retained with SBOM                                          |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

# PART VII: VALIDATION CHECKPOINTS

All code, deployments, and releases MUST pass these validation checkpoints. **NO EXCEPTIONS.**

---

## VII.1: INFRASTRUCTURE VALIDATION CHECKPOINT

```
+------------------------------------------------------------------------------+
|   INFRASTRUCTURE VALIDATION CHECKPOINT                                       |
+------------------------------------------------------------------------------+
|                                                                              |
|   Before any deployment is considered production-ready:                      |
|                                                                              |
|   ZERO THIRD-PARTY (LAW 8):                                                  |
|   [ ] NO external databases (PostgreSQL, Redis, etc.)                        |
|   [ ] NO external protocols (JSON, Protobuf, gRPC, etc.)                     |
|   [ ] NO external orchestration (Kubernetes, Docker, etc.)                   |
|   [ ] NO external ML (PyTorch, TensorFlow, ONNX, etc.)                       |
|   [ ] NO external monitoring (Prometheus, Grafana, etc.)                     |
|   [ ] NO external compression (zstd, lz4, etc.)                              |
|   [ ] NO external networking libraries                                       |
|                                                                              |
|   TERAS COMPONENTS:                                                          |
|   [ ] All storage via SIMPAN                                                 |
|   [ ] All serialization via TUKAR                                            |
|   [ ] All compression via MAMPAT                                             |
|   [ ] All networking via NADI                                                |
|   [ ] All telemetry via JEJAK                                                |
|   [ ] All ML via AKAL                                                        |
|   [ ] All containers via BEKAS                                               |
|   [ ] All orchestration via ATUR                                             |
|   [ ] All service mesh via JALINAN                                           |
|                                                                              |
|   PERFORMANCE:                                                               |
|   [ ] All components meet 10x industry-best targets                          |
|   [ ] Latency benchmarks passing                                             |
|   [ ] Throughput benchmarks passing                                          |
|   [ ] Memory footprint within limits                                         |
|                                                                              |
|   SECURITY:                                                                  |
|   [ ] All data encrypted at rest (AES-256-GCM)                               |
|   [ ] All data signed (ML-DSA-65)                                            |
|   [ ] All network traffic encrypted (NADI)                                   |
|   [ ] All audit logging enabled (JEJAK)                                      |
|   [ ] All secrets zeroized on drop                                           |
|                                                                              |
|   ALL boxes MUST be checked before production deployment.                    |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## VII.2: ML TRAINING PIPELINE VALIDATION CHECKPOINT

```
+------------------------------------------------------------------------------+
|   ML TRAINING PIPELINE VALIDATION CHECKPOINT                                 |
+------------------------------------------------------------------------------+
|                                                                              |
|   Before any ML model is deployed to production:                             |
|                                                                              |
|   MODEL FORMAT (AKAL):                                                       |
|   [ ] Model uses AKAL format (.akal) ONLY (no ONNX, no SavedModel)           |
|   [ ] Model signed with ML-DSA-65 (signature verified on load)               |
|   [ ] Weights hash matches header (SHA3-256)                                 |
|   [ ] Graph encoded in TUKAR format                                          |
|   [ ] Weights compressed with MAMPAT                                         |
|                                                                              |
|   PERFORMANCE:                                                               |
|   [ ] Accuracy â‰¥99.0% on validation set                                      |
|   [ ] FAR â‰¤0.1%                                                              |
|   [ ] FRR â‰¤2.0%                                                              |
|   [ ] AUC-ROC â‰¥0.995                                                         |
|   [ ] P50 latency â‰¤1ms on reference hardware                                 |
|   [ ] P99 latency â‰¤5ms on reference hardware                                 |
|   [ ] Peak memory â‰¤100MB                                                     |
|                                                                              |
|   BIAS:                                                                      |
|   [ ] Accuracy variance across age groups â‰¤5%                                |
|   [ ] Accuracy variance across gender â‰¤3%                                    |
|   [ ] Accuracy variance across skin tones â‰¤5%                                |
|   [ ] FRR variance across demographics â‰¤3%                                   |
|   [ ] FAR variance across demographics â‰¤0.05%                                |
|                                                                              |
|   SECURITY:                                                                  |
|   [ ] Adversarial accuracy â‰¥95%                                              |
|   [ ] Constant-time sigmoid/softmax enabled                                  |
|   [ ] Model hash registered in SIMPAN registry                               |
|                                                                              |
|   DEPLOYMENT:                                                                |
|   [ ] Staging test passed (72 hours minimum)                                 |
|   [ ] Canary deployment passed (72 hours, 10% traffic)                       |
|   [ ] Deployment uses ATUR orchestration                                     |
|   [ ] Monitoring via JEJAK telemetry                                         |
|                                                                              |
|   APPROVALS:                                                                 |
|   [ ] ML Engineering Lead signature                                          |
|   [ ] Security Team signature                                                |
|   [ ] Product Owner signature                                                |
|                                                                              |
|   ALL boxes MUST be checked before production deployment.                    |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## VII.3: FORENSIC EVIDENCE CHAIN VALIDATION CHECKPOINT

```
+------------------------------------------------------------------------------+
|   FORENSIC EVIDENCE CHAIN VALIDATION CHECKPOINT                              |
+------------------------------------------------------------------------------+
|                                                                              |
|   Before any forensic evidence implementation is considered complete:        |
|                                                                              |
|   STORAGE (SIMPAN):                                                          |
|   [ ] Uses SIMPAN embedded database ONLY (no SQLite, no PostgreSQL)          |
|   [ ] Storage encrypted with AES-256-GCM via teras-kunci                     |
|   [ ] Page signatures enabled (ML-DSA-65)                                    |
|   [ ] Audit logging enabled                                                  |
|                                                                              |
|   SERIALIZATION (TUKAR):                                                     |
|   [ ] All messages use TUKAR binary protocol (no JSON, no Protobuf)          |
|   [ ] Schema validated at compile time                                       |
|   [ ] Zero-copy access for read paths                                        |
|                                                                              |
|   COMPRESSION (MAMPAT):                                                      |
|   [ ] Uses MAMPAT-SELAMAT for evidence (constant-time)                       |
|   [ ] No zstd, no lz4, no external compression                               |
|                                                                              |
|   CHAIN INTEGRITY:                                                           |
|   [ ] Genesis block creates valid chain with seq=0, prev_hash=zeros          |
|   [ ] All evidence blocks have valid ML-DSA-65 signatures                    |
|   [ ] Chain validation detects any tampering                                 |
|   [ ] Sequence numbers are strictly monotonic with no gaps                   |
|   [ ] Timestamps are monotonically increasing                                |
|                                                                              |
|   NETWORK (NADI):                                                            |
|   [ ] Remote sync uses NADI protocol ONLY (no HTTPS, no gRPC)                |
|   [ ] ML-KEM-768 key exchange for post-quantum security                      |
|                                                                              |
|   ALL boxes MUST be checked before code is accepted.                         |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## VII.4: CONTAINER DEPLOYMENT VALIDATION CHECKPOINT

```
+------------------------------------------------------------------------------+
|   CONTAINER DEPLOYMENT VALIDATION CHECKPOINT                                 |
+------------------------------------------------------------------------------+
|                                                                              |
|   Before any GAPURA deployment is considered production-ready:               |
|                                                                              |
|   ORCHESTRATION (ATUR):                                                      |
|   [ ] Uses ATUR orchestration ONLY (no Kubernetes, no Nomad)                 |
|   [ ] Deployment spec in TUKAR format                                        |
|   [ ] Deployment signed with ML-DSA-65                                       |
|   [ ] State stored in SIMPAN (not etcd, not Consul)                          |
|                                                                              |
|   CONTAINER (BEKAS):                                                         |
|   [ ] Uses BEKAS runtime ONLY (no Docker, no containerd)                     |
|   [ ] Executable embedded in spec (not pulled from registry)                 |
|   [ ] Runs as non-root (UID 65532)                                           |
|   [ ] Read-only root filesystem enabled                                      |
|   [ ] no_new_privileges enabled                                              |
|   [ ] Capabilities restricted to NET_BIND_SERVICE only                       |
|   [ ] Syscall whitelist enforced (no unrestricted syscalls)                  |
|   [ ] All capabilities except NET_BIND_SERVICE dropped                       |
|                                                                              |
|   SERVICE MESH (JALINAN):                                                    |
|   [ ] mTLS enabled (ML-KEM-768 handshake, AES-256-GCM)                       |
|   [ ] Circuit breaker configured                                             |
|   [ ] Retry policy configured                                                |
|   [ ] Timeout configured                                                     |
|                                                                              |
|   NETWORK:                                                                   |
|   [ ] Default deny ingress policy                                            |
|   [ ] Default deny egress policy                                             |
|   [ ] Only required ports exposed (80, 443)                                  |
|   [ ] Egress restricted to TERAS services only                               |
|                                                                              |
|   AVAILABILITY:                                                              |
|   [ ] Minimum 3 replicas configured                                          |
|   [ ] Pod anti-affinity across zones                                         |
|   [ ] Autoscaling enabled                                                    |
|   [ ] Liveness probe configured                                              |
|   [ ] Readiness probe configured                                             |
|   [ ] Startup probe configured                                               |
|                                                                              |
|   OBSERVABILITY (JEJAK):                                                     |
|   [ ] Metrics exported to JEJAK (not Prometheus)                             |
|   [ ] Logs in TUKAR format to JEJAK                                          |
|   [ ] Traces propagated via NADI headers                                     |
|   [ ] Alert rules configured                                                 |
|                                                                              |
|   ALL boxes MUST be checked before production deployment.                    |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

## VII.5: SBOM REQUIREMENTS VALIDATION CHECKPOINT

```
+------------------------------------------------------------------------------+
|   SBOM REQUIREMENTS VALIDATION CHECKPOINT                                    |
+------------------------------------------------------------------------------+
|                                                                              |
|   Before any release is approved:                                            |
|                                                                              |
|   FORMAT (TERAS-BOM):                                                        |
|   [ ] Uses TERAS-BOM format ONLY (no SPDX, no CycloneDX)                     |
|   [ ] Serialized in TUKAR format                                             |
|   [ ] Signed with ML-DSA-65 release signing key                              |
|   [ ] Document hash verified                                                 |
|                                                                              |
|   COMPONENTS:                                                                |
|   [ ] ALL components inventoried                                             |
|   [ ] ALL components have SHA3-256 and BLAKE3 hashes                         |
|   [ ] ALL component origins documented                                       |
|   [ ] ALL licenses verified and approved                                     |
|   [ ] NO prohibited third-party dependencies                                 |
|                                                                              |
|   VULNERABILITIES:                                                           |
|   [ ] Vulnerability scan completed                                           |
|   [ ] NO unresolved CRITICAL vulnerabilities                                 |
|   [ ] All HIGH vulnerabilities have remediation plan                         |
|   [ ] Vulnerability status tracked in SIMPAN                                 |
|                                                                              |
|   ATTESTATIONS:                                                              |
|   [ ] BUILD_PROVENANCE attestation present and signed                        |
|   [ ] ZERO_THIRD_PARTY attestation present and signed                        |
|   [ ] VULNERABILITY_SCAN attestation present and signed                      |
|   [ ] LICENSE_COMPLIANCE attestation present and signed                      |
|   [ ] All attestations verified                                              |
|                                                                              |
|   STORAGE:                                                                   |
|   [ ] SBOM stored in SIMPAN (not external database)                          |
|   [ ] SBOM reference embedded in release artifacts                           |
|   [ ] SBOM queryable via JEJAK-QL                                            |
|                                                                              |
|   ALL boxes MUST be checked before release approval.                         |
|                                                                              |
+------------------------------------------------------------------------------+
```

---

# DOCUMENT END

```
+------------------------------------------------------------------------------+
|                                                                              |
|   TERAS MASTER ARCHITECTURE v3.2.2 â€” CONSOLIDATED AUTHORITATIVE DOCUMENT     |
|                                                                              |
|   ZERO THIRD-PARTY DEPENDENCIES EDITION                                      |
|                                                                              |
|   This document is LAW.                                                      |
|   Every component is proprietary.                                            |
|   Every implementation surpasses industry best.                              |
|   There are NO exceptions.                                                   |
|                                                                              |
|   SINGLE SOURCE OF TRUTH:                                                    |
|   â€¢ This document contains ALL specifications                                |
|   â€¢ NO external references are needed                                        |
|   â€¢ NO appendices in separate files                                          |
|   â€¢ EVERYTHING is here                                                       |
|                                                                              |
|   TERAS: Total Enterprise Resource Assurance System                          |
|   Built in Malaysia. Trusted Worldwide.                                      |
|                                                                              |
|   Document Statistics:                                                       |
|   â€¢ Version: 3.2.2 CONSOLIDATED                                              |
|   â€¢ Date: 2026-01-01                                                         |
|   â€¢ Status: BINDING LAW                                                      |
|                                                                              |
+------------------------------------------------------------------------------+
```
