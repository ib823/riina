# RIINA Research Domain χ (Chi): Verified Metadata Privacy

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-CHI-METADATA-PRIVACY |
| Version | 1.0.0 |
| Date | 2026-01-17 |
| Domain | χ: Verified Metadata Privacy |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |
| Status | FOUNDATIONAL DEFINITION |

---

# χ-01: The "Metadata Leakage" Problem & The RIINA Solution

## 1. The Existential Threat

**Context:**
RIINA's Non-Interference guarantees that `Secret` data cannot influence `Public` outputs.

**The Reality:**
Even with perfect content security, attackers learn:
- **WHO** communicates with whom (network graph)
- **WHEN** communication occurs (temporal patterns)
- **HOW MUCH** is communicated (message sizes)
- **HOW OFTEN** communication happens (frequency analysis)

**Real-World Impact:**
- NSA's metadata collection: "We kill people based on metadata" (former NSA director)
- Traffic analysis revealed CIA agents in Iran (2011)
- Metadata correlation unmasked Tor users (multiple academic papers)

**The Current RIINA Reality:**
```riina
// Content is protected
biar mesej: Rahsia<Teks> = Rahsia::baru("secret");
hantar(bob, mesej);

// But attacker sees:
// - Alice → Bob (who)
// - At 15:42:03.127 (when)
// - 256 bytes (size)
// - 47th message today (frequency)
```

## 2. The Solution: Metadata-Level Security Types

### 2.1 The Four Dimensions of Metadata

| Dimension | Threat | RIINA Protection |
|-----------|--------|------------------|
| **WHO** | Social graph analysis | `RahsiaMeta<IdPengguna>` |
| **WHEN** | Timing correlation | `RahsiaMeta<CapMasa>` |
| **SIZE** | Message fingerprinting | `RahsiaMeta<u64>` |
| **FREQUENCY** | Activity inference | `RahsiaMeta<Kadar>` |

### 2.2 Metadata Security Lattice

```
                MetaHidden
                    │
                    ▼
                MetaAnon
                    │
                    ▼
               MetaUnlinked
                    │
                    ▼
                MetaPublic
```

| Level | Who Protection | Timing Protection | Size Protection |
|-------|----------------|-------------------|-----------------|
| `MetaPublic` | Visible | Visible | Visible |
| `MetaUnlinked` | Unlinkable across sessions | Unlinkable | Unlinkable |
| `MetaAnon` | Anonymous | Anonymous | Uniform |
| `MetaHidden` | Existence hidden | Deniable | Cover traffic |

## 3. Mathematical Framework

### 3.1 Formal Definitions

```coq
(* Metadata security levels *)
Inductive metadata_level : Type :=
  | MetaPublic   : metadata_level
  | MetaUnlinked : metadata_level
  | MetaAnon     : metadata_level
  | MetaHidden   : metadata_level.

(* Metadata security ordering *)
Definition meta_leq (l1 l2 : metadata_level) : Prop :=
  match l1, l2 with
  | MetaPublic, _ => True
  | MetaUnlinked, MetaPublic => False
  | MetaUnlinked, _ => True
  | MetaAnon, MetaPublic => False
  | MetaAnon, MetaUnlinked => False
  | MetaAnon, _ => True
  | MetaHidden, MetaHidden => True
  | MetaHidden, _ => False
  end.

(* Message with metadata security *)
Record SecureMessage (T : Type) := {
  content : T;
  content_level : security_level;
  sender_meta : metadata_level;
  timing_meta : metadata_level;
  size_meta : metadata_level;
}.
```

### 3.2 Metadata Non-Interference

```coq
(* Low-equivalence extended to metadata *)
Definition meta_low_equiv (m1 m2 : SecureMessage T) (obs : observer) : Prop :=
  (* Content low-equiv as before *)
  low_equiv m1.content m2.content obs /\
  (* Plus metadata protection *)
  (m1.sender_meta >= MetaAnon -> m1.sender = m2.sender \/ unobservable obs m1.sender) /\
  (m1.timing_meta >= MetaAnon -> m1.timing = m2.timing \/ unobservable obs m1.timing) /\
  (m1.size_meta >= MetaAnon -> m1.size = m2.size \/ unobservable obs m1.size).

(* Metadata Non-Interference Theorem *)
Theorem metadata_non_interference : forall P s1 s2 obs,
  meta_low_equiv s1 s2 obs ->
  meta_low_equiv (step P s1) (step P s2) obs.
```

### 3.3 Sender Unlinkability

```coq
(* Two messages from same sender are unlinkable if sender_meta >= MetaUnlinked *)
Definition sender_unlinkable (m1 m2 : SecureMessage T) : Prop :=
  m1.sender_meta >= MetaUnlinked ->
  m2.sender_meta >= MetaUnlinked ->
  forall adversary,
    advantage adversary (link_sender m1 m2) <= negligible.
```

## 4. RIINA Language Extensions

### 4.1 Metadata Type Annotations

```riina
// Metadata-secure type wrapper
bentuk RahsiaMeta<T> {
    nilai: T,
    tahap: TahapMeta,
}

senum TahapMeta {
    Awam,       // MetaPublic
    TakPautan,  // MetaUnlinked
    TanpaNama,  // MetaAnon
    Tersembunyi, // MetaHidden
}

// Message with metadata security
bentuk MesejMeta<T> {
    kandungan: Rahsia<T>,
    penghantar: RahsiaMeta<IdPengguna>,
    masa: RahsiaMeta<CapMasa>,
    saiz: RahsiaMeta<u64>,
}
```

### 4.2 Metadata Annotations

```riina
// Function-level metadata protection
#[metadata(penghantar = "tanpa_nama")]
#[metadata(masa = "kabur")]
#[metadata(saiz = "seragam")]
fungsi hantar_selamat<T>(mesej: MesejMeta<T>) kesan KesanRangkaian {
    // Compiler enforces:
    // 1. Sender anonymization
    // 2. Timing obfuscation
    // 3. Size padding
}
```

### 4.3 Typing Rules Extension

```coq
(* Extended typing judgment *)
Inductive has_meta_type : context -> meta_context -> expr -> ty -> meta_level -> Prop :=

  (* Message send must respect metadata levels *)
  | T_Send : forall G M msg chan T sender_meta timing_meta size_meta,
      has_meta_type G M msg (TMessage T) sender_meta ->
      has_meta_type G M chan TChannel MetaPublic ->
      sender_meta >= required_sender_level chan ->
      timing_meta >= required_timing_level chan ->
      size_meta >= required_size_level chan ->
      has_meta_type G M (ESend chan msg) TUnit sender_meta

  (* Metadata cannot be downgraded without explicit declassification *)
  | T_MetaDeclass : forall G M e T l_from l_to policy,
      has_meta_type G M e T l_from ->
      meta_leq l_to l_from ->
      valid_meta_declass_policy policy l_from l_to ->
      has_meta_type G M (EMetaDeclass e policy) T l_to.
```

## 5. Implementation Strategy

### 5.1 Coq Files to Create

| File | Purpose | Dependencies |
|------|---------|--------------|
| `MetadataLevels.v` | Metadata lattice | Syntax.v |
| `MetadataTyping.v` | Extended typing rules | Typing.v, MetadataLevels.v |
| `MetadataSemantics.v` | Operational semantics | Semantics.v, MetadataLevels.v |
| `MetadataProgress.v` | Progress theorem | MetadataTyping.v, MetadataSemantics.v |
| `MetadataPreservation.v` | Preservation theorem | MetadataTyping.v, MetadataSemantics.v |
| `MetadataNonInterference.v` | Security theorem | All above + NonInterference.v |

### 5.2 Proof Strategy

1. **Extend syntax** with metadata annotations
2. **Extend typing** with metadata-aware rules
3. **Extend semantics** with metadata transformations
4. **Prove Progress** for metadata-secure programs
5. **Prove Preservation** for metadata types
6. **Prove Metadata Non-Interference** (main security theorem)

### 5.3 Estimated Effort

| Task | Effort | Blocking |
|------|--------|----------|
| MetadataLevels.v | 2 days | None |
| MetadataTyping.v | 5 days | MetadataLevels.v |
| MetadataSemantics.v | 5 days | MetadataLevels.v |
| MetadataProgress.v | 3 days | Typing, Semantics |
| MetadataPreservation.v | 5 days | Typing, Semantics |
| MetadataNonInterference.v | 10 days | All above + Track A complete |

**Total: ~30 days**

## 6. Security Properties

### 6.1 Properties to Prove

| Property | Formal Name | Status |
|----------|-------------|--------|
| Sender Anonymity | `sender_anonymous` | TO BE PROVEN |
| Sender Unlinkability | `sender_unlinkable` | TO BE PROVEN |
| Timing Unlinkability | `timing_unlinkable` | TO BE PROVEN |
| Size Uniformity | `size_uniform` | TO BE PROVEN |
| Metadata Non-Interference | `meta_non_interference` | TO BE PROVEN |
| Metadata Type Safety | `meta_type_safety` | TO BE PROVEN |

### 6.2 Threat Model

**In Scope:**
- Global passive adversary (sees all network traffic)
- Active adversary (can inject/modify traffic)
- Compromised network nodes
- Statistical traffic analysis

**Out of Scope (addressed by other tracks):**
- Endpoint compromise (Track U: Runtime Guardian)
- Side-channel attacks (Track S: Hardware Contracts)
- Physical attacks (Track Φ: Verified Hardware)

## 7. Dependencies

| Dependency | Direction | Nature |
|------------|-----------|--------|
| Track A (Non-Interference) | χ requires A | Foundation for content security |
| Track η (Traffic Resistance) | χ integrates η | Traffic shaping for size uniformity |
| Track ι (Anonymity) | χ integrates ι | Mixnet for sender anonymity |
| Track Ω (Network Defense) | χ extends Ω | Secure channel foundation |

## 8. Obsolescence of Threats

When Track χ is complete:

| Threat | Status | Mechanism |
|--------|--------|-----------|
| Social graph analysis | OBSOLETE | Sender anonymity |
| Communication pattern analysis | OBSOLETE | Timing unlinkability |
| Message fingerprinting | OBSOLETE | Size uniformity |
| Activity detection | OBSOLETE | Cover traffic |
| Correlation attacks | OBSOLETE | Full unlinkability |

---

**"Metadata is data about data. RIINA protects both."**

*Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE*
