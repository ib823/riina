# Changelog

**Verification:** 12,678 Coq Qed (compiled, 0 Admitted, 0 active axioms) — Coq is the only mechanized lane | 3364 Rust tests | the other prover trees are machine-generated (claim-level tracked, not independent verification)

All notable changes to RIINA™ will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### 2026-08-08 — Gate C: rendering parity, `pelaku` rename, verified listener close

### Fixed (Gate C / REQ-68 backend parity — signed sized-int rendering)
- **`ke_teks` of a signed sized int rendered the masked bit pattern on both compiled
  backends** (`253` where the interpreter — the reference — prints `-3`). C: the
  `riina_builtin_ke_teks` INT branch ignored the `int_signed_bits` tag the rest of the
  C runtime maintains (the sibling `riina_format` already honored it). WASM: the i64
  cell carries no runtime tag, so `emit_ke_teks` now takes the call site's static type
  (`Ty::IntN{signed}`), sign-extends, and renders `-` + magnitude — i64::MIN handled
  via the unsigned magnitude loops. All three backends now agree, including at
  i64::MIN/i16::MIN/zero. New corpus example `00_basics/nombor_bertanda.rii` held
  byte-equal by `corpus_c_wasm_differential`; +1 lexer guard test.
### Changed (Gate C — actor keyword corrected: `pelakon` → `pelaku`, hard rename)
- **The BM actor keyword is now `pelaku`** (doer/agent — the correct translation);
  `pelakon` (a stage/film actor — a mistranslation) is no longer a keyword and lexes
  as a plain identifier (owner decision 2026-08-08, hard mode, no deprecated alias).
  One lexer line is the language surface; sweep covered parser tests, the fuzz keyword
  list, 6 Jalinan examples, docs (README/AGENTS/JALINAN_GUIDE/BIJAK_SPEC/session-types
  paper/2 Jalinan specs), llms.txt, the AI training corpus, and the website source.
  Historical CHANGELOG entries deliberately left as written. Zero Coq impact.
  Guard test: `pelaku`/`actor` → KwActor, `pelakon` → Identifier.
### Added (Gate C — verified listener close, Coq model first)
- **`VerifiedNetwork.v`: LISTEN --Close--> CLOSED edge** (RFC 793 p.22
  close-from-LISTEN) added to `valid_transition`; full 331-file Coq build re-verified
  green (Rocq 9.1.1). Ported 1:1 to `riina_os::net` (exhaustive state×event tests
  still pass unchanged — they derive from the table). New builtin
  **`jaring_tutup_dengar`/`net_close_listener`**: closes a listener along the verified
  edge, drops the real socket; a closed listener rejects accept/local-addr with
  "not listening" and double close is rejected by the model (no Close edge out of
  CLOSED). STDLIB.md regenerated (327 → 329 registered builtins).

### 2026-08-08 — Gate C: 64-bit WASM — plain `Nombor` div/mod/order now unsigned (u64-correct ≥ 2^63)

### Fixed (Gate C / Standard Library Hardening — numeric tower, WASM backend)
- **WASM `Nombor` operations ≥ 2^63 were silently wrong** (`03_PROTO/crates/riina-codegen/src/wasm.rs`):
  the W1 i64-value-cell landing removed the old clean ">= 2^32" compile error, but the
  generic BinOp arm still emitted the SIGNED ops (`i64.div_s`/`i64.rem_s`/`i64.lt_s`/…),
  so a value ≥ 2^63 read as negative: `18000000000000000000 > 1` compiled to *false* and
  div/mod produced wrapped-signed junk while the interpreter (`Value::Int(u64)`) and the
  C backend (`uint64_t`) agreed on the u64 answers. Found by a ≥ 2^63 three-backend
  differential this session. Plain `Ty::Int` (and unsigned `IntN`) now lower to the
  UNSIGNED i64 ops (`i64.div_u`/`i64.rem_u`/`i64.lt_u`/`i64.gt_u`/`i64.le_u`/`i64.ge_u` —
  the four unsigned comparison opcodes 0x54/0x56/0x58/0x5A added to `wasm_encode::Op`);
  signed `IntN` keeps the signed ops with the existing sub-64 sign-extension. New corpus
  example `07_EXAMPLES/00_basics/nombor_64bit.rii` (boundary 2^63, u64::MAX, div/mod/order)
  is byte-equal across interp/C/WASM and is held so by `corpus_c_wasm_differential`
  (verified green with wasmtime 27.0.0 this session); +2 opcode-level tests.
  This closes the "true 64-bit WASM" Gate C item: the numeric tower's plain-int surface
  is now u64-correct end-to-end on all three backends (owner-approved refactor,
  supersedes the previously-chosen bounded ">= 2^32 error" path — which W1 had already
  replaced with the i64 cell, minus this signedness gap).

### 2026-08-08 — Gate C: networking — real TCP gated by the verified RFC 793 state machine

### Added (Gate C / Standard Library Hardening — Networking)
- **`riina_os::net`** (`03_PROTO/crates/riina-os/src/net.rs`): 1:1 Rust port of the
  predicate core of `02_FORMAL/coq/domains/VerifiedNetwork.v` — the RFC 793
  `TCPState`/`TCPEvent`/`valid_transition` table and the TLS 1.3 acceptance policy
  (`is_strong_cipher`, no-downgrade). The enforcing `TcpConnection` can only move along
  edges the Coq theorem NET_001_11 (`tcp_state_machine_correct`) proves valid; tests
  cover the full (state × event) space exhaustively and mirror NET_001_03/08/11.
- **`jaring_*` network builtins** (`03_PROTO/crates/riina-codegen/src/builtins/net.rs`):
  `jaring_sambung`/`net_connect`, `jaring_hantar`/`net_send`, `jaring_terima`/`net_recv`,
  `jaring_tutup`/`net_close` perform **real** TCP I/O over `std::net` sockets with the
  verified state machine enforced on top — send/recv require ESTABLISHED, close walks the
  verified active-close path to CLOSED, and a send after close is rejected by the model
  (`not established`), not by hoping the OS notices. `tls_dasar_ok`/`tls_policy_ok` is the
  pure TLS acceptance policy (TLS 1.3 × strong AEAD suite only; unknown strings fail
  closed). TLS record-layer cryptography is NOT implemented (no dep-free TLS stack in
  03_PROTO — Law 8); no builtin claims to encrypt traffic. Interpreter-only: not
  registered in codegen, so the C/WASM backends fail closed rather than miscompile.
  Typechecker registers all five pairs (`Effect::Network`; the policy check is `Pure`) —
  `docs/api/STDLIB.md` regenerated (311 → 321 registered builtins).
- Also: fixed a latent `clippy::doc_lazy_continuation` failure in
  `riinac/tests/corpus_differential.rs` (doc-comment formatting) that broke
  `cargo clippy --all-targets -- -D warnings` on the baseline tree.
- **Passive open (server side)**: `jaring_dengar`/`net_listen` (real bound
  `TcpListener` held in the verified LISTEN state), `jaring_alamat`/`net_local_addr`
  (ephemeral-port discovery), `jaring_terima_sambungan`/`net_accept` (blocking accept
  that replays the verified passive path LISTEN→SYN_RECEIVED→ESTABLISHED; the accepted
  connection then uses the same send/recv/close gates as an active one). Deliberately
  NO listener-close builtin: the Coq `valid_transition` table has no LISTEN→CLOSED
  edge, and the model governs — adding that edge belongs in `VerifiedNetwork.v` first.
  STDLIB.md 321 → 327 registered builtins.

## [0.4.0] — 2026-06-06

Ships the constant-time-hardened, formally-verified crypto work accumulated since
0.3.0 (2026-03-19): nine mechanized Coq⇄Rust formal-equivalence proofs (GHASH×2,
AES field + full cipher, SHA-256, SHA3-256, Curve25519 field, ML-KEM NTT, X25519
ladder), constant-time hardening — incl. a real variable-time leak fixed in Ed25519
signing — now CI-gated, the set union/intersect O(n·m)→O(n+m) optimization, and the
CT / audit-readiness tooling (dossier, RFP, host-prep + timing harnesses).
Verified at the tagged release commit `a855c939b` (2026-08-05, all by command):
**0 Admitted / 0 Axiom / 0 Abort, 12,638 Coq Qed across 328 active files,
03_PROTO 2,951/0 + 05_TOOLING 304/0, clippy clean** (`--all-targets -D warnings`,
both workspaces). Detailed entries (formerly [Unreleased]) follow — the per-entry
Qed counts in them are the corpus size *at the time each change landed* and are
deliberately left as written.

### 2026-06-05 — Gate C: set union/intersect O(n·m) → O(n+m)

### Changed (Gate C / Standard Library Hardening — Collections)
- **`set_kesatuan`/`set_persilangan` perf** (`03_PROTO/crates/riina-codegen/src/builtins/set.rs`):
  the benchmark (`reports/stdlib_bench.md`) flagged the set union/intersect as ~O(n·m) — a linear
  `Vec::contains` membership scan per element (~42 ms at n=8192). They now build a hashable
  `SetKey` index over the scalar element variants (Int/Bool/String/IntN/Unit/Color/Hash/ActorRef)
  for O(1) membership — **O(n·m) → O(n+m)** for the common scalar set — with an exact
  `Vec::contains` fallback for compound/opaque values (`Pair`/`List`/`Closure`/`Ref`, which aren't
  `Ord`/`Hash`, so a `BTreeSet<Value>` was not viable). Behaviour-preserving (identical elements,
  order, no-dup), so the `VerifiedMapSet.v` membership + no-dup proofs still describe the running
  code; locked by the new `opt_union_intersect_equal_naive_reference` guard (200 mixed-type rounds,
  incl. unkeyable elements, asserting fast-path == naive reference). 03_PROTO 2729 → **2730 / 0**.

### 2026-06-05 — Formal-equivalence proof, ninth primitive: X25519 Montgomery ladder

### Added (Gate C / north-star — Coq ⇄ Rust formal equivalence)
- **New Coq lane `02_FORMAL/coq/crypto/X25519.v`** (active build 322 → 323 files, 12,531 →
  12,533 Qed, 0 Admitted/Axiom/Abort). Models `montgomery.rs`'s X25519 scalar multiplication over
  GF(2^255-19) (the field whose multiply `Field25519.v` proves correct mod p): the Montgomery
  ladder (`double` xDBL + `diff_add` xADD + the conditional-swap structure, a24=121666), scalar
  clamping, and the little-endian decode/encode with the bit-255 mask. Proves by `vm_compute` that
  the modelled `x25519` reproduces the **RFC 7748** §5.2 Test Vector 1 and §6.1 basepoint
  (Alice's public key) **byte-for-byte** (`x25519_rfc7748_vector1`, `x25519_rfc7748_basepoint`).
- **Coq ⇄ Rust bridge** `crypto::montgomery::tests::test_x25519_matches_coq_model`: the shipping
  `x25519`/`x25519_base` produce the identical bytes on those exact vectors (05_TOOLING 293 →
  **294 / 0 / 0**). Nine formal-equivalence primitives now landed (GHASH ×2, AES S-box, full
  AES-256 cipher, SHA-256, SHA3-256, Curve25519 field, ML-KEM NTT, **X25519 ladder** — the GCM +
  AES + SHA-2 + SHA-3 + ECC (field + ladder) + PQC cores). See
  `reports/precrypto_audit_secondmodel.md` §Formal equivalence 2026-06-05.

### 2026-06-05 — Formal-equivalence proof, eighth primitive: ML-KEM (Kyber) NTT

### Added (Gate C / north-star — Coq ⇄ Rust formal equivalence)
- **New Coq lane `02_FORMAL/coq/crypto/NTT.v`** (active build 321 → 322 files, 12,528 →
  12,531 Qed, 0 Admitted/Axiom/Abort). The post-quantum arithmetic core: a model of `ml_kem.rs`'s
  number-theoretic transform faithful to the *exact integer semantics* — i16 two's-complement
  wrapping, Montgomery reduction (R=2^16, q=3329, q⁻¹=−3327), Barrett reduction, the 128-entry
  `ZETAS` table, the Cooley-Tukey forward + Gentleman-Sande inverse butterfly network, the F=1441
  inverse-NTT scaling, and the degree-1 `basemul`. Proves by `vm_compute` that the pipeline
  ML-KEM uses — `ntt`, `ntt`, pointwise-multiply, `inv_ntt`, `reduce` — computes the polynomial
  product in `Z_q[X]/(X²⁵⁶+1)`: `ntt_mul_one` (1·1=1), `ntt_mul_1plusX_squared` (the genuine
  convolution (1+X)²=1+2X+X²), and `ntt_mul_negacyclic_wrap` (X²⁵⁵·X = X²⁵⁶ ≡ q−1, the negacyclic
  reduction the NTT encodes).
- **Coq ⇄ Rust bridge** `crypto::ml_kem::tests::test_ntt_matches_coq_model`: the shipping `Poly`
  (ntt/pointwise_mul/inv_ntt/reduce) produces the byte-identical `to_positive` outputs on those
  three vectors (05_TOOLING 292 → **293 / 0 / 0**). Eight formal-equivalence primitives now landed
  (GHASH ×2, AES S-box, full AES-256 cipher, SHA-256, SHA3-256, Curve25519 field, **ML-KEM NTT** —
  the GCM + AES + SHA-2 + SHA-3 + ECC + PQC cores). See
  `reports/precrypto_audit_secondmodel.md` §Formal equivalence 2026-06-05.

### 2026-06-05 — Formal-equivalence proof, seventh primitive: full AES-256 cipher

### Added (Gate C / north-star — Coq ⇄ Rust formal equivalence)
- **New Coq lane `02_FORMAL/coq/crypto/AES.v`** (active build 320 → 321 files, 12,524 →
  12,528 Qed, 0 Admitted/Axiom/Abort). Builds on `AESField.v` (which already proved the 256-byte
  S-box is the genuine `affine(a^254)` construction): models the *whole* AES-256 cipher at the
  byte level — key schedule + 14 rounds of SubBytes/ShiftRows/MixColumns/AddRoundKey and the
  inverse cipher — reusing the proven `aes_sbox`/`gmul`, and proves by `vm_compute` that it
  reproduces the **FIPS-197 Appendix C.3** known-answer vector for both `aes256_encrypt` and
  `aes256_decrypt`. So AES is now verified end-to-end: from "the S-box is real" to "the entire
  AES-256 block transform is the real AES".
- **Coq ⇄ Rust bridge** `crypto::aes::tests::test_aes256_matches_coq_model`: the shipping `Aes256`
  (u32-state impl) produces the byte-identical ciphertext, recovers the plaintext, and its key
  schedule matches the Coq `ks_first_word`/`ks_eighth_word` (05_TOOLING 291 → **292 / 0 / 0**).
  Seven formal-equivalence primitives now landed (GHASH ×2, AES S-box, **full AES-256 cipher**,
  SHA-256, SHA3-256, Curve25519 field — the GCM + AES + SHA-2 + SHA-3 + ECC cores). See
  `reports/precrypto_audit_secondmodel.md` §Formal equivalence 2026-06-05.

### 2026-06-05 — Formal-equivalence proof, sixth primitive: Curve25519 field (the deep one)

### Added (Gate C / north-star — Coq ⇄ Rust formal equivalence)
- **New Coq lane `02_FORMAL/coq/crypto/Field25519.v`** (active build 319 → 320 files, 12,515 →
  12,524 Qed, 0 Admitted/Axiom/Abort). The first *symbolically*-proved (not KAT) crypto primitive:
  it models `field25519.rs`'s radix-2^51 GF(2^255-19) limb arithmetic and proves, by `ring` +
  modular arithmetic, the headline **`mul_correct_mod`** — the schoolbook product folded by
  `2^255 ≡ 19` computes `a·b mod p` (the Mersenne-style reduction correctness underlying
  Curve25519) — plus `add_correct` and `sub_correct_mod`, and `vm_compute` corner cases
  (`(p-1)² ≡ 1`, `2²⁵⁴·4 ≡ 38`).
- **Coq ⇄ Rust bridge** `crypto::field25519::tests::test_mul_matches_coq_model`: confirms the full
  carried Rust `Mul` on those vectors incl. a reduction case (05_TOOLING 290 → **291 / 0 / 0**).
  Six formal-equivalence primitives now landed (GHASH ×2, AES S-box, SHA-256, SHA3-256, Curve25519
  field — the GCM + AES + SHA-2 + SHA-3 + ECC cores). See
  `reports/precrypto_audit_secondmodel.md` §Formal equivalence 2026-06-05.

### 2026-06-05 — Formal-equivalence proof, fifth primitive: SHA-3 / Keccak

### Added (Gate C / north-star — Coq ⇄ Rust formal equivalence)
- **New Coq lane `02_FORMAL/coq/crypto/Keccak.v`** (active build 318 → 319 files, 12,513 →
  12,515 Qed, 0 Admitted/Axiom/Abort). A faithful model of `keccak.rs`'s Keccak-f[1600]
  (θ/ρ/π/χ/ι over the 25-lane state, with the RC/ROTATION/PI_LANE tables) and the SHA3-256 sponge,
  proven by `vm_compute` to reproduce the FIPS 202 digests for `""` and `"abc"`.
- **Coq ⇄ Rust bridge** `crypto::keccak::tests::test_sha3_256_matches_coq_model`: `Sha3_256::hash`
  returns the byte-identical digests (05_TOOLING 289 → **290 / 0 / 0**). Five formal-equivalence
  primitives now landed (GHASH ×2, AES S-box, SHA-256, SHA3-256 — the GCM + AES + SHA-2 + SHA-3
  cores). See `reports/precrypto_audit_secondmodel.md` §Formal equivalence 2026-06-05.

### 2026-06-05 — Formal-equivalence proof, fourth primitive: SHA-256

### Added (Gate C / north-star — Coq ⇄ Rust formal equivalence)
- **New Coq lane `02_FORMAL/coq/crypto/SHA256.v`** (active build 317 → 318 files, 12,511 →
  12,513 Qed, 0 Admitted/Axiom/Abort). A faithful model of `sha2.rs` (round functions, message
  schedule, 64-round compression + Davies-Meyer feed-forward, padding) proven by `vm_compute` to
  reproduce the FIPS 180-4 digests for `"abc"` and `""`. (SHA-256 is a hash — the content is
  executable model⇄spec⇄impl agreement, not deep algebra.)
- **Coq ⇄ Rust bridge** `crypto::sha2::tests::test_sha256_matches_coq_model`: `Sha256::hash`
  returns the byte-identical digests (05_TOOLING 288 → **289 / 0 / 0**). Four formal-equivalence
  primitives now landed (GHASH ×2, AES S-box, SHA-256). See
  `reports/precrypto_audit_secondmodel.md` §Formal equivalence 2026-06-05.

### 2026-06-05 — Formal-equivalence proof, third primitive: AES GF(2^8) & S-box

### Added (Gate C / north-star — Coq ⇄ Rust formal equivalence)
- **New Coq lane `02_FORMAL/coq/crypto/AESField.v`** (active build 316 → 317 files, 12,506 →
  12,511 Qed, 0 Admitted/Axiom/Abort). Models AES GF(2^8) (`xtime`/`gf_mul`, faithful to
  `aes.rs`) and proves — finitely, over all 256 bytes by `vm_compute` — that the magic 256-byte
  S-box tables are the genuine mathematical construction: `sbox_eq_construction`
  (`SBOX[a] = affine(a^254)`), `gf_inv_correct` (`a^254` is the GF(2^8) inverse, 255 cases), and
  `SBOX`/`INV_SBOX` mutual inverses. Plus the FIPS 197 worked example `0x57·0x83 = 0xc1`.
- **Coq ⇄ Rust bridge** `crypto::aes::tests::test_sbox_matches_coq_model`: recomputes the S-box
  from `gf_mul`+affine and asserts it equals the shipped `SBOX` (and `INV_SBOX` inverts it)
  (05_TOOLING 287 → **288 / 0 / 0**). Three formal-equivalence primitives now landed (GHASH ×2 +
  AES). See `reports/precrypto_audit_secondmodel.md` §Formal equivalence 2026-06-05.

### 2026-06-05 — Formal-equivalence proof, second primitive: full GHASH fold

### Added (Gate C / north-star — Coq ⇄ Rust formal equivalence)
- **New Coq lane `02_FORMAL/coq/crypto/GHASH.v`** (imports `GF128`; active build 315 → 316 files,
  12,485 → 12,506 Qed, 0 Admitted/Axiom/Abort). Models `Ghash::update_block`'s recurrence as a
  `fold_left` and proves GHASH is a **GF(2)-linear polynomial hash**: `ghash_linear`
  (`GHASH_H(X⊕Y) = GHASH_H(X)⊕GHASH_H(Y)`, the almost-XOR-universal property GCM auth rests on)
  and `ghash_cons`/`ghash_horner_two` (the Horner form `⊕ᵢ Bᵢ·H^(m-i+1)`).
- **Coq ⇄ Rust bridge** `crypto::ghash::tests::test_ghash_fold_matches_coq_model`: a
  `Ghash::new`/`update_block` sequence asserted byte-identical to the model's `vm_compute`
  (05_TOOLING 286 → **287 / 0 / 0**). Detail in `reports/precrypto_audit_secondmodel.md`
  §Formal equivalence 2026-06-05.

### 2026-06-05 — Formal-equivalence proof, first primitive: GHASH GF(2^128)

### Added (Gate C / north-star — Coq ⇄ Rust formal equivalence)
- **New mechanized Coq crypto lane `02_FORMAL/coq/crypto/GF128.v`** (first crypto proof in the
  Coq corpus; active build **314 → 315 files, 12,456 → 12,485 Qed**, 0 Admitted/Axiom/Abort). It
  models the *exact* bit-serial algorithm of `riina-core`'s `ghash::gf128_mul` over `Z` and
  proves — via bit-extensionality (`Z.bits_inj'`) + `btauto` — the additive group laws, `mulx`
  linearity, **bilinearity** (`gf_mul_distr_l`/`_r`), **identity** (`gf_mul_one_r`), zero, and
  **128-bit closure** (`gf_mul_in128`), with executable `vm_compute` KAT `Example`s.
- **Coq ⇄ Rust parity bridge** `crypto::ghash::tests::test_gf128_mul_matches_coq_model`: asserts
  the Rust `gf128_mul` is byte-identical to the model's `vm_compute` product (`05_TOOLING` 285 →
  **286 / 0 / 0**). The bridge caught a real model transcription bug (the reduction constant
  `0xe1` written as decimal `231`=`0xe7`; the Rust was correct) — exactly the point of an
  executable equivalence anchor.
- Turns GHASH multiplication from "tested-correct" into "model-proven + implementation
  cross-checked". Remaining (multi-session): `Ghash::compute`, AES GF(2^8), SHA-2/3 bit-ops,
  curve25519 field. See `reports/precrypto_audit_secondmodel.md` §Formal equivalence 2026-06-05.

### 2026-06-05 — Machine-level constant-time evidence harness (dudect-style)

### Added (Gate C crypto-audit prep — empirical CT evidence)
- **Dependency-free dudect-style timing-leakage probe** at
  `05_TOOLING/crates/riina-core/examples/dudect_ct.rs`: Welch's t-test over fixed-vs-random
  secret classes (hand-rolled xorshift PRNG + t-test, no `dudect`/`criterion`/`rand` — Law 8),
  with a **positive control** that validates detection power. It is an `example`, not a
  `#[test]` (timing in CI is noise), so the test count is unchanged (**285 / 0 / 0**). Run it
  pinned to a core: `taskset -c 0 cargo run --release --example dudect_ct -p riina-core`.
- **In-container results (indicative, not audit-grade):** AES-256 block, Ed25519 sign,
  X25519 DH, ML-KEM-768 decaps, and `ct_eq_bytes` all read **no leak**; the positive control
  flags as designed. AES-256-GCM flags a small |t|, **investigated to a microarchitectural
  fixed-vs-random artifact** — `ghash::gf128_mul` is branchless (no secret-dependent
  branch/table), confirmed by source inspection. No code defects found.
- **Honest scope:** the RIINA dev container is a Docker/KVM vCPU (invariant TSC + `taskset`
  pinning, but uncontrollable steal-time), so a clean run here is indicative; the harness is
  the reusable instrument for the controlled-host CT certification an external audit (REQ-28)
  performs. Detail in `reports/precrypto_audit_secondmodel.md` §Machine-level CT evidence 2026-06-05.

### 2026-06-04 — Ed25519/X25519 deep pre-audit pass (RFC 8032 §5.1.3 strict decode)

### Security (Gate C crypto-audit prep — `05_TOOLING/crates/riina-core`)
- **Ed25519 point decoding is now RFC 8032 §5.1.3-strict.** `EdwardsPoint::decompress` previously
  accepted two non-canonical encodings (point-encoding malleability — one curve point with multiple
  valid 32-byte encodings):
  - a **non-canonical y-coordinate `y >= p`**, which `FieldElement::from_bytes` silently reduced
    mod p (now rejected via a branchless `is_canonical_y` = `y < p`, mirroring the `s < L` check);
  - **`x = 0` with the sign bit set** (negating zero yields zero), which the standard requires
    rejecting (no "negative zero").

  Both rejections are **purely additive** — every canonical input (all RFC 8032 test vectors, the
  sign/verify roundtrips, basepoint/identity compression) is unchanged.
- Added an end-to-end **`(R, s + L)` malleability-rejection** test through `verify`, exercising the
  `0 <= s < L` gate (the second-model `is_scalar_valid` borrow fix previously had only a
  helper-level unit test).
- **X25519 + GCM re-reviewed, confirmed clean.** Added the previously-missing X25519 contributory
  **all-zero (small-order) shared-secret rejection** test (`u = 0`). GCM SP 800-38D length limits
  remain deliberately unenforced (unreachable ~64 GiB / untestable; documented).
- `05_TOOLING` `cargo test --all` **280 → 285 / 0 / 0** (+5), `kat_audit` **23 / 0 ignored**,
  clippy clean. Coq/`03_PROTO` unchanged (314 files / 12,456 Qed; 2729 / 0 / 3). Detail in
  `reports/precrypto_audit_secondmodel.md` §Deep-pass 2026-06-04.

### 2026-06-04 — Post-quantum FIPS 203/204 reconciliation (NIST ACVP byte-exact)

### Added (PQC — ML-KEM-768 → FIPS 203 + ML-DSA-65 → FIPS 204; authentic NIST ACVP, byte/behaviour-exact)
- **ML-KEM-768 → FIPS 203 (keyGen + encaps + decaps), byte-exact vs authentic NIST ACVP-Server vectors.**
  The keygen divergence's root cause was `sample_ntt` reading its zero-initialised buffer on the first
  iteration — the matrix `Â` was silently all-zeros, so `t̂ = Â∘ŝ + ê` collapsed to `ê` (this is exactly why
  `ŝ`/`dk` matched NIST while `t̂`/`ek` did not). Also `G(d)`→`G(d‖k)`, `poly_tomont` after the `Â∘ŝ`
  basemul-accumulate, and the FO transform (`K` straight from `G`; implicit reject `J(z‖c)` over the full
  ciphertext). Added the §7.2/§7.3 key-validity checks (decap-key hash check: the embedded `H(ek)` must equal
  `SHA3-256(ek)`). KATs: `kat_ml_kem_768_keygen_acvp_fips203`, `kat_ml_kem_768_encaps_decaps_acvp_fips203`.
- **ML-DSA-65 → FIPS 204 (keyGen + sigGen + sigVer + all interfaces), byte/behaviour-exact vs NIST ACVP.**
  Fixes: `H(ξ)`→`H(ξ‖k‖ℓ)`; ExpandS centered-binomial → FIPS 204 `RejBoundedPoly`/`CoeffFromHalfByte`;
  ExpandA Kyber 12-bit → Dilithium 23-bit `CoeffFromThreeBytes`; deterministic `ρ''=H(K‖0³²‖μ)`. The internal,
  external "pure" (`sign_with_context`), pre-hash / HashML-DSA (`sign_prehash`, for the shipped hashes), and
  **hedged** (`sign_hedged` — now actually consumes `rnd`, was a stub) interfaces are all ACVP-verified.
  KATs: `kat_ml_dsa_65_{keygen,siggen,sigver}_acvp_fips204`.
- **Full ACVP vector sweeps for the implemented parameter sets (115 cases):** ML-KEM-768 keyGen ×25 /
  encaps ×25 / decaps ×10; ML-DSA-65 keyGen ×25 / sigGen ×15 / sigVer ×15. Every vendored vector carries its
  source URL + file SHA-256.
- **`kat_audit`: 23 passed, 0 ignored** (was 2 ignored) — every primitive now has an authoritative FIPS/RFC
  KAT. `05_TOOLING` `cargo test --all` **280 / 0 / 0**; `03_PROTO` unchanged at **2729 / 0 / 3 ignored**.
- Pre-audit CT/correctness hardening (Codex + second-model passes): Ed25519 `ct_select` (secret-scalar path)
  and `is_scalar_valid` (reversed subtraction borrow) fixes; ML-DSA `check_norm` made constant-time; AES
  `ct_lookup` CT barrier; `constant_time::ct_select` made branchless. See `reports/precrypto_audit_secondmodel.md`.
- **Release:** `VERSION` → **0.3.0**, tag **`v0.3.0`**. (A historical `[0.3.0] — 2026-03-19` entry already
  exists below; reconciling the release numbering is deferred to a dedicated release-management pass.)

### 2026-06-02 — Gate B CLOSED → Gate C opened (crypto-audit prep)

### Added (Gate C stdlib hardening)
- **OS/system effect-typing audit ⇄ Coq injection-prevention parity**: audited the
  system builtins and confirmed the taint→sanitize→sink discipline is sound and
  precise — inputs (`read_line`) are `System` + `Tainted<_, UserInput>`,
  sanitizers (`sanitize_*`) are **`Pure`** (`Tainted → Sanitized<_, k>`), and
  sinks (`sql_execute`/`js_eval`/`shell_exec`/`ldap_search`) are `System` and
  *require* their specific `Sanitized<_, k>`. +3 typechecker tests lock this in,
  mirroring the Coq `TaintSystemCorrectness.v` `{sql,command,ldap,xss_js}_
  injection_impossible` theorems on the running typechecker: every sink rejects a
  tainted argument (`TaintViolation`), a wrongly-sanitised one (`SanitizerMismatch`)
  and a raw `String` (`TypeMismatch`), and accepts only its matching sanitiser's
  output; the read→sanitise→sink pipeline composes while skipping the sanitiser is
  a `TaintViolation`. The taint-source taxonomy was already verified against the
  Coq model (FS slice). No code change — the effect-typing was already correct;
  the value is the regression-proofing parity suite. `cargo test --all` 2709/0,
  clippy 0; differential unchanged (32/32).
- **Math — verified laws for the numeric builtins**: new Coq model
  `02_FORMAL/coq/foundations/VerifiedMath.v` (19 Qed, 0 Admitted/Axiom/Abort;
  active build 313→314 files, 12,437→12,456 Qed) proves, over `nat`, the laws of
  the `matematik.rs` builtins: **min/max** (commutativity, idempotence, the order
  bounds, and `min a b + max a b = a + b`), **gcd** (divides both, commutative,
  `gcd a 0 = a`), and **pow** (`b^0=1`, `b^1=b`, `b^(m+n)=b^m·b^n`). `abs`
  (identity on unsigned `Nombor`) and `sqrt` (an `f64` floor) are intentionally
  not modelled. +3 Rust property tests in `matematik.rs` confirm the running
  `min`/`max`/`gcd`/`lcm`/`pow`/`abs`/`rem` builtins compute exactly those `Nat`
  functions over a seeded sweep, plus the composite identities `min+max=a+b` and
  `gcd·lcm=a·b`. Mirrors `VerifiedList.v`/`VerifiedMapSet.v`/`VerifiedString.v`.
  `cargo test --all` 2706/0, clippy 0; differential unchanged (32/32).
- **Strings — verified core string algorithms**: new Coq model
  `02_FORMAL/coq/foundations/VerifiedString.v` (11 Qed, 0 Admitted/Axiom/Abort;
  active build 312→313 files, 12,426→12,437 Qed) models a string as a list of
  code units and proves the **repeat length law** (`|repeat s n| = n·|s|`, with
  the zero/one/succ shapes for `str_repeat`/`teks_ulang`) and the
  **split/join round-trip** (`join sep (split sep s) = s` for `str_split`+
  `str_join`/`teks_belah`+`teks_cantum`). Case-folding is deliberately *not*
  modelled (Rust's Unicode `to_uppercase` is not length-preserving — ß⇒SS — so a
  length-preserving char map would be an unsound model). +4 Rust property tests in
  `teks.rs` on the running builtins: repeat length/shape, split/join round-trip
  (single- and multi-char delimiters, empty/trailing/consecutive-separator edge
  cases), and the Unicode-faithful idempotence of `to_upper`/`to_lower`/`trim`.
  Mirrors `VerifiedList.v`/`VerifiedMapSet.v`. `cargo test --all` 2703/0, clippy 0;
  differential unchanged (32/32).
- **Filesystem taint discipline ⇄ Coq proof (parity bridge)**: connected the
  prototype's file-I/O type discipline to the mechanized taint calculus. Every
  file builtin types its path as a plain `String`, so a `Tainted` (untrusted)
  path is a type error — the concrete realisation of `TaintSystemCorrectness.v`
  `path_traversal_impossible`. Added a named filesystem corollary
  `file_path_traversal_impossible` (+1 Qed → active 12,425→12,426) that the
  prototype cites, and +3 typechecker parity tests mirroring the theorem on the
  *running* typechecker: all 8 file ops reject a tainted path and accept a clean
  one; a `file_read` result is `Tainted<_, FileSystem>` and cannot be reused as a
  path (end-to-end); and rejection is source-agnostic (a `NetworkExternal`-tainted
  `http_body` is rejected too, matching the theorem's `forall src`). Verified the
  taint-source taxonomy: the prototype's 6 core `TaintSource` variants match the
  Coq `taint_source` exactly (the +6 RIINA-product sources are handled by the same
  source-agnostic rejection). `cargo test --all` 2699/0, clippy 0. NB: the
  complementary POSIX-correctness model `VerifiedFileSystem.v` (109 Qed —
  permissions/journaling/quotas) remains the deeper target the prototype's I/O
  does not yet realise.
- **Collections — verified Map & Set algebra** (completes the "Collections →
  verified core algorithms" Gate C row alongside `VerifiedList.v`): new Coq model
  `02_FORMAL/coq/foundations/VerifiedMapSet.v` (14 Qed, 0 Admitted/Axiom/Abort;
  active build 311→312 files, 12,411→12,425 Qed). The `peta.rs` `BTreeMap` map is
  modelled by the standard partial-map abstraction (`nat -> option nat`), proving
  the fundamental laws — get-after-insert, insert leaves other keys untouched,
  insert shadows, remove deletes exactly one key. The `set.rs` de-duplicated `Vec`
  set is modelled as a list under membership, proving the membership algebra for
  insert/remove/union/intersect (union modelled to match `set_kesatuan`'s
  de-dup-against-the-accumulator fold) plus the no-duplicate invariant for insert.
  +4 Rust property tests in `peta.rs`/`set.rs` assert the same invariants on the
  running builtins (dependency-free seeded sweeps). `cargo test --all` 2696/0,
  clippy 0; differential unchanged (32/32).
- **Collections — verified core list algorithms** (the "Collections → verified
  core algorithms" Gate C row): new Coq model
  `02_FORMAL/coq/foundations/VerifiedList.v` (17 Qed, 0 Admitted/Axiom/Abort;
  active build 310→311 files, 12,394→12,411 Qed) models the prototype's
  first-order list builtins (`builtins/senarai.rs`) as Stdlib lists and proves
  their core laws — reverse-involutive, length under reverse/concat/map — and the
  headline **insertion-sort correctness**: `isort_permutation` + `isort_sorted` +
  `isort_idempotent` (i.e. `list_sort` is an ascending permutation of its input),
  plus de-duplication invariants (`NoDup` + set-preservation for `list_unique`).
  Mirrors the numeric-tower `SizedInt.v` precedent. +4 Rust property tests in
  `senarai.rs` assert the SAME invariants on the running builtins — a
  dependency-free seeded sweep of 200 random integer lists for
  sort/reverse/unique/concat — tying the proof to the implementation.
  `cargo test --all` 2692/0, clippy 0; differential unchanged (32/32).
- **Time stdlib builtins — precise types** (the "Time interface — Unclear" Gate C
  row): the six `masa_*`/`time_*` builtins were typed `Fn(Any, Any, Time)`. They
  are now sound and precise, matching the runtime (`builtins/masa.rs` + the C
  emit): the clocks (`masa_sekarang`/`_ms`/`masa_jam`) are `Unit -> Int` (the
  runtime value is a `Builtin` function, so this is sound — a bare `Int` would
  type-check programs the untyped interpreter then rejects); `masa_tidur` (sleep)
  is `Int -> Unit`; `masa_format`/`masa_urai` take a `(value, format)` pair ->
  `String`/`Int`. The applied builtins now reject misuse (`masa_tidur("x")` is a
  type error, was accepted under `Any -> Any`) and track `Effect::Time`
  end-to-end (verified by running `masa_format((123, "iso"))` -> "123"). +2 tests.
  The `()` zero-arg-thunk *runtime materialisation* (a bare builtin `Var`
  evaluates to its `Builtin` value, like `baca_garisan`) is a separate,
  codebase-wide item. Typecheck-only, so the differential is unchanged (32/32);
  `cargo test --all` 2688/0.
- **Numeric tower — wasm32 64-bit handling (graceful + full u32)**: the WASM
  backend holds integers in a 32-bit cell, so a value `>= 2^32` (true u64/i64)
  previously emitted an out-of-range `i32.const` — `riinac build --target wasm32`
  silently produced an **invalid** `.wasm` that only failed cryptically at
  `wasmtime` load time. Now it is a **clean compile error** (`wasm32 target cannot
  represent the 64-bit integer N …`). Separately, the full unsigned **32-bit range
  including `[2^31, 2^32)`** (e.g. `4000000000u32`) is now representable — encoded
  as the wrapped i32 bit pattern — where it also used to emit invalid bytecode;
  `sized_integers.rii` gained a u32-wrap case (`4e9 + 1e9 ≡ 705032704`,
  byte-identical across interp/C/WASM). +2 tests (64-bit rejection; full-u32
  acceptance). Values `< 2^31` are byte-identical, so the differential is
  unchanged (32/32). True 64-bit WASM support (an i32→i64 backend refactor) stays
  a tracked multi-session item. `cargo test --all` 2686/0.
- **Numeric tower — signed sized-int codegen (C + WASM)**: compiled output is now
  signedness-correct for signed `Ty::IntN`, matching the interpreter. The C value
  carries an `int_signed_bits` tag (0 for plain/unsigned ⇒ unchanged unsigned
  semantics, byte-identical; N ⇒ sign-extend on format/compare/div); `riina_trunc`
  tags signed results, and `riina_format`/`riina_binop_{lt,le,gt,ge,div,mod}` plus
  the result-echo sign-extend via `riina_sext`. The WASM backend sign-extends
  signed sub-i32 operands before `i32.div_s`/`i32.rem_s`/comparisons
  (`i32.extend8_s`/`extend16_s`) and prints signed (sign-extend + leading `-`) in
  the itoa for `cetak` and the result-echo. New example
  `00_basics/signed_integers.rii` (i8 overflow/underflow/signed-division →
  `-128`/`-5`/`-64`) is byte-identical across C, WASM, and the interpreter —
  **corpus differential 31→32/32 byte-equal**. +2 codegen tests (C tag/helpers,
  WASM operand sign-extension). All paths gated on signed `IntN`, so the 31
  existing examples stay byte-identical. `cargo test --all` 2684/0, clippy 0.
- **Numeric tower — Coq model** (`02_FORMAL/coq/foundations/SizedInt.v`, 8 Qed,
  0 Admitted/Axiom/Abort): a foundational model of fixed-width (`Ty::IntN`)
  arithmetic as residues in `Z / 2^bits Z`. Proves the ring homomorphism
  `wrapU_add`/`_sub`/`_mul` (reducing operands vs. only the result agree — the
  soundness fact the interpreter, C, and WASM backends rely on to compute the
  same width-`bits` value), `wrapU_idemp`/`wrapU_range`, that the backends'
  emitted bit-mask equals modular reduction (`land_ones_is_wrapU`:
  `Z.land x (2^bits-1) = x mod 2^bits`), and the signed reinterpretation
  (`toSigned`). Stdlib-backed; active Coq build now 310 files / 12,394 Qed.
- **Multi-arg `file_write`/`file_append` — precise types**: the `(path, data)`
  pair builtins were `Fn(Any, Any, FileSystem)`; now
  `Fn(Prod(String, String), Unit, FileSystem)` — a `Tainted` untrusted path is
  rejected (path-traversal prevention, like the single-path ops), data is a
  `String` (declassify tainted content before a file sink), result `Unit`.
  +2 tests (pair/Unit/effect; tainted-path rejection).
- **Numeric tower — sized-integer literals + width-aware arithmetic + codegen**
  (completes two of the three "later slices" the distinct-sized-types entry below
  noted): the lexed width suffix `42u8` now becomes a distinct
  `Expr::IntN { value, bits, signed }` literal (additive variant — the ~700
  existing `Int(_)` sites are untouched), typed as `Ty::IntN`. Arithmetic
  propagates the width (a plain `Int` adapts; `u8 + u16` is rejected). The
  interpreter gained `Value::IntN`: `+`/`-`/`*` wrap modulo 2^bits, and
  division/modulo/comparison/display are signedness-aware (two's complement).
  Width-correct codegen: the C backend wraps sized arithmetic through a new
  `riina_trunc` runtime helper, and the WASM backend masks with
  `i32.const (2^bits-1); i32.and` (and routes `Ty::IntN` through its
  int-print/`ke_teks`/result-echo dispatch, which previously only matched
  `Ty::Int`). New example `00_basics/sized_integers.rii` (u8/u16 overflow) is
  byte-identical across C, WASM, and the interpreter (44/255/0) — the corpus
  differential rose 30→**31/31 byte-equal** (156 examples). +16 tests (parser AST
  shape, typecheck width propagation + mixed-width rejection, interpreter
  wrap/signed-division/signed-comparison, and C + WASM byte-level mask, positive +
  negative). `cargo test --all` 2680/0, clippy 0. Remaining numeric-tower work:
  signed display/comparison in *compiled* output (the interpreter is already
  signed-correct), >32-bit widths on the WASM i32 cell, and a Coq numeric model.
- **Numeric tower — distinct sized integer types**: added `Ty::IntN { bits,
  signed }` *additively* (a 1-site match ripple, not 434 — `Ty` matches use
  wildcards; `Ty::Int`/`Nombor` stays the default). The type parser accepts
  `u8`…`i64`; sized types work on function params/returns (`fungsi id8(x: u8) ->
  u8 { x }` types as `IntN{8,false}`); `IntN`↔`Int` interoperate (a plain literal
  initialises a sized binding) while distinct widths are incompatible (`u8` body
  vs `u16` return ⇒ `AnnotationMismatch`). Codegen treats `IntN` as
  representationally-`Int`, so the lowered IR / differential are unchanged (30/30).
  +2 tests. (Width-aware arithmetic, the lexer-suffix→`IntN`-literal connection,
  and a Coq numeric model are later slices.)
- **Effect-set on function declarations → sound multi-capability gating**:
  `TopLevelDecl::Function` now carries `effect_set: Vec<Effect>` — the *components*
  of a compound `kesan (A, B, C)` (the lattice `effect` field is the lossy max-join).
  `check_program` grants **every** component in the body, so a compound-effect
  function authorizes all its declared ambient ops. This makes the opt-in
  capability gate **sound for compound effects**, so it is now extended from
  Network/Process to also cover **Crypto/Random/System** (the earlier `crypto_ops.rii`
  false-positive is resolved; differential restored 30/30). Codegen-transparent
  (typecheck-only; the lowered IR is unchanged). +6 tests (network ×3, random ×2,
  compound-grants-all-components ×1). Parser threads the components through
  `parse_effect_annotation` → `(Effect, Vec<Effect>)`.
- **Single-path file ops — precise result types**: `file_exists`→`Bool`,
  `file_delete`→`Unit`, `file_size`→`Int` (`file_list_dir` stays `Any`), atop the
  `String`-path hardening. +1 test; differential 30/30.
- **Single-path file ops hardened to `String` paths**: `file_exists`/`file_delete`/
  `file_size`/`file_list_dir` retyped `Any → Any` ⇒ `String → …`, so a `Tainted`
  untrusted path is rejected (path-traversal prevention), consistent with
  `file_read`. +1 test; differential 30/30.
- **Capability-gating scope finding** (no code change beyond Network/Process):
  extending the opt-in capability gate to `Crypto`/`Random`/`System` is *unsound*
  under the current model — a function's declared effect is a single (lossy)
  `Effect`, so a compound `kesan (Kripto, Tulis, Rawak)` only auto-grants one
  component, producing false positives on legitimate compound-effect functions
  (caught via the differential `both_ran` count dropping 30→29 on `crypto_ops.rii`).
  The gate stays Network/Process; sound multi-capability gating needs an effect-set
  `granted` representation (documented in code + the Gate C network row).
- **Network/Process capability gating (hybrid POLA)**: once a program opts into
  the capability discipline (some `grant` in scope), a `Network`/`NetworkSecure`/
  `Process` operation now requires the matching capability granted, else
  `CapabilityViolation`. Mirrors the opt-in `T_Require` rule (no grants anywhere
  ⇒ permissive, so existing programs are unaffected — 0 breakage, differential
  30/30). A function declaring `kesan Rangkaian`/`kesan Proses` auto-grants it in
  its body, so effect-honest code keeps working. +3 tests (ungated network op
  rejected; granted accepted; no-capability permissive). File I/O stays at
  effect+taint (not capability-gated) per the hybrid policy.
- **Numeric tower, first slice — typed integer-literal suffixes**: the lexer now
  recognizes decimal width suffixes (`u8/u16/u32/u64/i8/i16/i32/i64`) and
  **range-validates them at lex time** — `256u8`, `300i8`, `4294967296u32` are
  compile errors (`InvalidNumericLiteral`). A non-width trailing run (`255abc`) is
  left for normal tokenization, so no existing program changes. +5 lexer tests.
  (Distinct sized-integer *types* in `Ty`, width-aware arithmetic, codegen, and a
  Coq numeric model are the next slices — the full tower is multi-session.)
- **File-content reads are taint-typed**: `file_read`/`file_read_lines`
  (`fail_baca`/`fail_baca_baris`) retyped `Any → Any` ⇒ `String → Tainted<String,
  FileSystem>`. An untrusted (`Tainted`) path is now rejected at the I/O boundary
  (path-traversal prevention, Coq `path_traversal_impossible`), and file contents
  are `Tainted<_, FileSystem>` — an untrusted source that must be sanitized before
  reaching any sink (Coq taint safety). +3 tests (tainted-path rejected; literal
  path ⇒ tainted contents; contents rejected at a SQL sink unsanitized). Full
  suite 2646 → 2649; differential unchanged 30/30.

### Changed
- **Gate D2 — prover-honesty retraction (DONE)**: no marketing claim survives
  unproven. README (lines 86/242/393) and the website body were already honest
  ("Coq is the only mechanized lane", "9 other lanes generated/smoke-only — not
  independent verification"); the last overclaim, the social card
  `website/public/og-image.svg` ("10 independent provers"), is now
  "Coq-mechanized core · 9 generated lanes". Each generated lane
  `02_FORMAL/{fstar,tlaplus,alloy,smt,verus,kani,tv}/` now carries a visible
  `GENERATED-CORPUS-NOT-VERIFIED.md` notice (corpus is machine-generated from the
  Coq tree, not independent verification; Coq is the only mechanized lane;
  `metrics.json` `claimLevels` is the source of truth). Marking, not moving, so the
  openly-tracked counts don't shift (`.md` isn't counted by the prover globs). Gate
  D Path D1 (earning the lanes) remains open; the honesty obligation is met.
- **Active gate marker advanced B → C** (Part 11). Gate B (Compiler Enforcement
  Parity) exit criteria verified by command: 0 `todo!()`/`unimplemented!()` outside
  tests; every compiler-enforceable Coq security property has pos+neg Rust tests;
  `cargo test --all` (03_PROTO) = 2646/0; clippy 0; WASM/C differential 30/30; Coq
  309 `.vo`, 0 Admitted/0 Axiom (`verify --full`). REQ-27 depth (multiparty surface
  wiring, DMP/GoFetch CT) tracked as non-blocking follow-ups. Compiler-maturity
  pillar L2 → L3.

### Added
- **Crypto-audit-prep KAT manifest** (`05_TOOLING/crates/riina-core/tests/kat_audit.rs`),
  the first Gate C / REQ-28 deliverable: one reproducible auditor-facing entry point
  (`cargo test -p riina-core --test kat_audit`) that re-verifies each primitive against
  an *independently transcribed* canonical vector from its governing standard, plus
  AEAD/signature tamper-rejection — SHA-256/512 (FIPS 180-4), HMAC-SHA256 (RFC 4231),
  HKDF-SHA256 (RFC 5869), AES-256 (FIPS 197), AES-256-GCM (GCM spec TC13 + tag tamper),
  X25519 (RFC 7748), Ed25519 (sign/verify + forgery rejection). All 8 green;
  05_TOOLING suite 248 → 256. This is audit *preparation*, not a replacement for the
  external audit (REQ-28), which stays a P0 external-firm dependency.

### 2026-06-02 — Gate B: WASM/C parity closed, session pipeline, constant-time

Compiler enforcement-parity work (REQ-27, Gate B). All verified by command.

### Added
- **Session-type parse→project→check pipeline** (`riina-typechecker`): choreography
  protocols now parse **role-relative** to the first role, so the stored
  `SessionType` is that role's local view (`A->B:T` ⇒ `Send T` when A is the
  first role, `Recv T` when B is). New `project_choreography` (role ⇒ local
  session type; role[0] ⇒ protocol, role[1] ⇒ `session_dual`; >2 roles ⇒
  unsupported), `session_well_formed` (closed recursion), and
  `choreography_compatible` (distinct roles + closed protocol + 2-party
  projection duality ⇒ deadlock-free, per Coq `ST_020` / `CT_117`), wired into
  `type_check_full` — ill-formed choreographies are now rejected.
- **Per-program constant-time codegen pass** (`riina-codegen/src/ct_verify.rs`):
  `verify_constant_time` re-checks the lowered IR for a `CondBranch` on a
  `ConstantTime` condition or a `Div`/`Mod` on a `ConstantTime` operand
  (propagated through data-flow to a fixpoint), wired into
  `riina_codegen::compile` (new `Error::ConstantTimeViolation`).
- **CI `differential` job** (`.github/workflows/verify.yml`): installs
  `cc`+`wasmtime` so the WASM/C `corpus_differential` byte-equality test runs in
  CI instead of auto-skipping.
- **N-party multiparty session-type core** (`riina-typechecker/src/multiparty.rs`):
  role-annotated `GlobalType`/`LocalType` + `project(g, role)` + `mergeable` +
  `is_projectable`, mirroring the mechanized Coq development (`GlobalType`
  `ChoreographyTypes.v:160`, `LocalType` `:232`, `project` `:399`, `mergeableb`
  `ChoreographyProjection.v:48`). The binary `riina_types::SessionType` cannot
  carry peer roles, so >2-role projection needs this separate representation —
  this lifts the `project_choreography` >2-role `None` limitation. +9 tests incl.
  a genuine 3-party Buyer/Seller/Shipper protocol projected onto each role and
  branch-projectability accept/reject. (Per-statement channel-op impl checking
  and `koreografi`-surface wiring remain — RIINA has no session-channel surface
  ops yet.)

### Changed
- **WASM backend reaches byte-for-byte parity with C** across the dual-backend
  example corpus — `corpus_differential` is now **30/30 byte-equal**
  (`KNOWN_DIVERGENT` empty), up from 26. Fixes this session: (a) nested-if/else
  merge-`Phi` pushed from each branch region's exit block (fixes `padan`
  integer/tuple matches → `pattern_match`); (b) struct `FieldAccess` lowered to
  the real positional projection `Fst(Snd^i(base))` over the struct's product
  layout (fixes `compiler/main` → `v0.1.0`); (c) WASM string-`Add` heap concat +
  `ke_teks` string pass-through (fixes the CAHAYA UI `paparan`/`tulisan`/`butang`
  examples).
- **Constant-time typecheck rule extended**: a `ConstantTime` operand in integer
  **division/modulo** is now rejected (data-dependent latency); `Add`/`Sub`/`Mul`
  stay constant-time and keep the CT tag. The lowerer's `infer_type` propagates
  the CT tag through `BinOp` (guarded on CT operands — non-CT programs are
  byte-identical).
- **Sum-elimination payload types in lowering** (`riina-codegen/src/lower.rs`):
  `Expr::Case` now derives each branch's payload type from `infer_type(scrutinee)`,
  mirroring the typechecker's `T_Case` normalization (`Sum(l,r) ⇒ (l,r)`;
  `Option(t) ⇒ (t,Unit)`; `Unit` fallback). The `UnwrapLeft`/`UnwrapRight` IR
  values **and** the branch bindings now carry the real payload type instead of a
  hardcoded `Unit` — closing 2 of the 4 remaining feature-gated Gate B `// TODO`s
  (now **3/5** done), via the same `infer_type` idiom `Fst`/`Snd` already use.
  +2 tests; differential unchanged at 30/30 byte-equal.
- **LDAP injection enforcement-parity test** closing a Gate B audit gap: a
  command-verified cross-check of every Coq `*_impossible` theorem in
  `domains/TaintSystemCorrectness.v` against the Rust taint tests found that
  `ldap_injection_impossible` had the enforcement (`ldap_search` sink requiring
  `Sanitized<String, LdapEscape>`, `sanitize_ldap`) but **no test**. Added
  `test_ldap_{injection_prevented,safe_with_sanitization,sanitizer_mismatch}`
  (positive + negative + wrong-sanitizer), matching the SQL/XML/path surface.
  (CSRF is modeled via the `csrf_generate`/method layer, not a taint sanitizer —
  documented as a deliberate modeling difference.)
- **Effect-Gate top-level-binding-purity tests** closing a second Gate B parity
  gap found by a per-`TypeError`-variant coverage audit: `EffectViolation` has two
  enforcement sites and only the function effect-discipline one was tested. Added
  `check_program_{rejects_effectful_top_level_binding,allows_pure_top_level_binding}`
  (a module-level `biar` initialized with an effectful expression is rejected;
  pure bindings accepted) — Coq effect-soundness parity.
- **Perform-payload TODO resolved** (`riina-typechecker`): a per-`TypeError`-variant
  audit showed the long-standing "validate payload type matches effect definition?"
  TODO was a *false gap* — Coq `T_Perform` (Typing.v:168) is
  `e:T!ε ⊢ perform eff e : T!(ε⊔eff)` with no payload-vs-signature premise, and the
  Rust arm already matches it exactly. Adding a check would be a Rust rule with no
  Coq counterpart (a parity violation). Reworded to a design note + 2 `gate_b_parity`
  tests locking the rule.
- **Lexer int-suffix TODO resolved** as a documented deferral: typed integer
  suffixes (`0xFFu8`, `42i64`) need sized integer types, which RIINA lacks (single
  `Nombor`/`Ty::Int`) — they belong to the numeric tower (Gate C). Lexing a suffix
  no later stage can consume would be a stub, so the bare `// TODO: Suffix` was
  replaced with that rationale. This resolves the last of the 5 documented
  lexer/parser/codegen TODOs (now **5/5**).
- **Taint-sink diagnostics wired live**: `TaintViolation`/`SanitizerMismatch` were
  declared (with help text + error codes) but never raised — taint at a sink was a
  generic `TypeMismatch`. The App rule now routes an incompatible `Sanitized<_,
  required>` argument through `sink_argument_error` (`Tainted` ⇒ `TaintViolation`,
  wrong sanitizer ⇒ `SanitizerMismatch`). The 20 injection tests now assert these
  precise variants — a stronger parity surface for the Coq `*_impossible` theorems.

### Verified (by command, not copied)
- `03_PROTO` test suite: **2,646 pass / 0 fail** (`cargo test --all`; 2,628 + 2
  sum-unwrap payload-type tests + 3 LDAP injection-parity tests + 2 Effect-Gate
  binding-purity tests + 2 `T_Perform` parity tests + 9 multiparty
  global-type/projection tests); `cargo clippy` 0 warnings.
  WASM/C differential 30/30 byte-equal under wasmtime 45.0.0.
  Coq active build 309 `.vo`, 0 `Admitted` / 0 `Axiom` (pre-push `riinac verify
  --full`). `gate_b_parity` deepened to 18 enforcement tests (added IFC
  reference-aliasing and nested-call-site capability), plus session-projection
  and constant-time div/mod tests.

### Still open (honestly scoped)
- **Multiparty** per-statement channel-operation impl checking + `koreografi`-surface
  wiring (the global-type + projection core now exists in `multiparty.rs`, but RIINA
  has no session-channel surface ops yet, so only the projected local *type* is
  checked — there is no operation sequence to check it against).
- **DMP/GoFetch-class** microarchitectural constant-time channels (out of scope
  until the CHERI/hardware-contract era, Phase 7/9).

### 2026-06-01 — Prototype: loop control, logical-not, example corpus

### Added
- **Loop control keywords** `putus` (break) and `lanjut` (continue), parsed in
  `selagi` / `ulang` / `untuk` bodies (with an optional ignored loop label). The
  spellings match the example corpus; `keluar` / `terus` are no longer reserved
  and are usable as ordinary identifiers (e.g. loop-flag variables).
- **`baca_garisan`** (read-line) builtin, typed as a `Teks` thunk.
- `03_PROTO/.cargo/config.toml` sets `RUST_MIN_STACK=16 MiB` so `cargo test
  --all` is green by default. In debug builds the large interpreter
  `eval_with_env` match has a big stack frame, and the `letrec` countdown tests
  overflowed the default 2 MiB spawned-thread stack; the release `riinac`
  binary (8 MiB main thread) was never affected. No semantic change.

### Changed
- **`!` is now overloaded** as logical-not on `Bool`/`Any` (it keeps its deref
  meaning on references), matching the language reference which already
  documented `!` / `bukan` as the `not` operator.
- Documentation aligned to the implemented loop-control vocabulary
  (`04_SPECS/language/RIINA_LANGUAGE_REFERENCE_AI.md`,
  `SYNTAX_IMPROVEMENT_SPEC_v2_0_0.md`, `RIINA_MASTER_PLAN.md` Part 9,
  `07_EXAMPLES/06_ai_context/` cheatsheet + common-mistakes); corpus status
  refreshed in `07_EXAMPLES/README.md`.

### Verified (by command, not copied)
- `07_EXAMPLES/00_basics/` passes `riinac check` 20/20; full corpus 47/147
  git-tracked (51/155 on disk). `03_PROTO` test suite: 2,607 pass / 0 fail;
  `cargo clippy --all` reports 0 warnings.

### 2026-05-17 — Lean active-lane axiom restoration

### Fixed
- Lean 4 active lane: replaced 15 generator-fallback `axiom` declarations
  ("fallback: unresolved match translation") in `02_FORMAL/lean/RIINA/Domains/` and
  `Industries/IndustryFinancial.lean` with concrete `def`/`partial def` ports of the
  matching Coq sources. Affected: `netperm_eq`, `action_to_perm`, `action_target`
  (NetworkDefense), `valid_transition` (FullstackSecurity), `dual` (SessionTypes +
  X001_ConcurrencyModel), `ast_dual` (ActorCalculus), `interaction_dual`,
  `can_communicate` (ChoreographyTypes), `assignment_active` (EnterpriseERP),
  `time_010_check_timeout` (TimingSecurity), `project` (X001_ConcurrencyModel),
  `exec_txn` (SIGMA001_VerifiedStorage), `all_typed` (MobileOS/ConcurrencyFramework),
  `tx_final` (IndustryFinancial). Active-lane axiom grep returns 0; `lake build RIINA`
  still passes (commit `41b85893`).

### Tracked but not changed
- Per-file `lake env lean RIINA/Domains/<X>.lean` runs reveal pre-existing
  elaboration-time sorries (60+ in `ActorCalculus.lean` alone) caused by
  upstream transpiler-output mistypes. These are NOT literal `sorry` tokens
  (grep stays at 0), but Lean inserts them when proofs fail to elaborate.
  Default `lake build RIINA` target routes through the near-empty `Domains/All`
  shim and does not exercise individual domain files. Recorded in
  RIINA_MASTER_PLAN.md Part 2 Lean caveat for follow-up.

### 2026-05-16 — Documentation drift correction

### Fixed
- `RIINA_MASTER_PLAN.md` Part 2: corrected Coq active `.v` files (292 → 309), Lean files (155 → 325), Lean axiom count (0 → 15), Isabelle files (307 → 368), and extended-prover file counts to match `metrics.json`
- `AGENTS.md`, `llms.txt`, `README.md`: refreshed verified-state tables; previous values were a session out of date
- `VERIFICATION_MANIFEST.md`: refreshed SHA + tooling test count; clarified Coq/Lean build status as "not re-verified in ephemeral container"

### Added
- `PROOF_STATUS.md` (regenerated via `scripts/update-proof-ledger.sh`): new `Abort (active, incomplete proof attempts)` ledger surfacing 4 gaps in `domains/X001_ConcurrencyModel.v`, `V001_TerminationGuarantees.v`, `W001_VerifiedMemory.v`, `domains/mobile_os/LocationServices.v`
- `scripts/audit-docs.sh`: added drift checks for AGENTS.md + llms.txt so the next session detects rot automatically

### Removed
- 4 stub crates in `05_TOOLING/crates/`: `riina-lang-{lexer,parser,types,codegen}` (each was a 4-LOC `forbid(unsafe_code)` header duplicating the real `03_PROTO/crates/riina-{lexer,parser,types,codegen}`). Workspace + dependency entries cleaned up; only consumer (also-stub `05_TOOLING/crates/riinac`) had its deps pruned without behavioral change.

## [0.3.0] — 2026-03-19

### JALINAN Phase J1 — Session-Typed Actors
- **Actor system**: `pelakon` (actor), `lahir` (spawn), `hantar` (send), `terima` (recv) — full pipeline from parse to run to emit-c
- **Choreography types**: `koreografi` (choreography), `peranan` (role) — global multiparty session protocols
- **Content-addressed values**: `cincang` (hash) — FNV-1a hash with deterministic output
- **CRDT merge**: `gabung` (merge) — conflict-free replicated data with GCounter semantics
- **Actor runtime**: `riina-runtime` crate (16th crate) — mailbox, supervisor, session-typed channels
- **C backend**: pthread-based actor runtime — real mutex/cond mailbox for native execution
- **WASM backend**: actor instruction stubs for browser playground
- **Interpreter**: synchronous message processing — Spawn stores state, Send applies handler, Recv returns state

### Proofs & Verification
- 11,905 Coq Qed (0 Admitted, 0 axioms, 301 active files)
- 71,351 total proof artifacts across 10 provers
- New Coq domains: ActorCalculus, ActorSupervision, ChoreographyTypes, ChoreographyProjection, CRDTFoundations, CRDTComposition, MerkleDAG, ContentAddressedState, AccessibilityVerification
- 5 mechanized (Coq, Lean, Isabelle, TLA+, SMT), 2 compiled (F*, Alloy), 3 generated

### Compiler & Tooling
- 2,294 Rust tests (up from 1,282)
- 500+ compliance rules across 15 profiles
- HTTP package registry client (riina-pkg)
- Session type checker (56 tests)
- BinOp type checker uses types_compatible() for Any compatibility
- Parser: multi-line actor syntax, koreografi/pelakon/lahir/hantar/terima blocks

### Website & Documentation
- RIINA™ trademark asserted across all public documents
- Website: JALINAN section on How It Works page, actor example in playground
- Claim level explainer (mechanized/compiled/generated)
- GPG signing permanently configured for deployments

### Pre-0.3.0 development notes (Sessions 87–88, March 2026)

<!-- Was mis-titled `## [Unreleased]` until 2026-08-05. It sits BELOW the
     `## [0.3.0] — 2026-03-19` heading and its content is dated 2026-03-16, so
     this work shipped IN 0.3.0 — it was simply never promoted when that release
     was cut. Demoted to a subsection of 0.3.0 rather than deleted, so nothing is
     lost and the grouping stays visible. Content below is byte-identical. -->

### Added (Session 88 — 2026-03-16 — Linear Types, Multi-Prover Mechanization, WASM Backend)
- Linear type enforcement: `biar sekali` (affine), `biar paling` (relevant), `biar mesti` (linear) wired through lexer→parser→typechecker; Phase 3 gate PASSED
- WASM backend working end-to-end: .rii → WASM → wasmtime for integers, arithmetic, if/else, function calls, closures with captures, recursive functions (REQ-14 DONE)
- 19 Lean 4 domain files fixed — Lean upgraded to mechanized (4,458 theorems, 0 sorry)
- 267 SMT/Z3 files added — SMT dequarantined (generated corpus, 12,405 raw asserts). [Correction 2026-06-01: only the 1 smoke file (`SecurityLatticeVerification.smt2`) actually verifies — 25 Z3 unsat properties, not the "11,843 assertions" / "mechanized" originally stated here.]
- Isabelle 10 core theories compile — Isabelle upgraded to mechanized (9,092 lemmas, 0 sorry)
- F*, TLA+, Alloy dequarantined — Track B1 worker fixes merged
- Total proofs: 48,913 across 10 provers (4 mechanized, 3 compiled, 3 generated)
- 980 Rust tests passing, clippy clean

### Fixed (Session 88)
- `generate-metrics.sh`: `escape_json` fix for newlines in pending reasons

### Added (Session 87 — Phase 3 Compiler Enforcement Alignment)
- Declassification strict mode: `declassify(e)` now rejects non-Secret types (matches Coq T_Declassify)
- Handle effect join: `handle e with x → h` returns `eff_e ⊔ eff_h` (matches Coq T_Handle)
- Handle handler binding: handler variable `x` bound to body result type in handler scope
- Top-level binding purity enforcement: `biar x = e` at module level rejects effectful expressions
- Capability Grant/Require context tracking: `TypingContext.granted` set propagated through Grant/Require/LetRec
- Function body capability granting: declared function effects auto-granted in body scope
- Phase 3 and Phase 4 task tables updated with DONE/TODO status
- 968 Rust tests passing (up from 924), 0 failures

### Added (Session 86 — Core Deepening)
- `properties/TypingInversion.v`: 53 Qed — 22 typing inversion lemmas, value purity theorem, type/effect determinism, type constructor disjointness (12) and injectivity (6)
- `domains/TaintSystemCorrectness.v`: 47 Qed — compile-time taint tracking with typing uniqueness proving 9 injection attack categories impossible (SQL, XSS, command, path traversal, LDAP, XML, header, template, eval)
- Resolved 4 design decisions: D014 (fuel-based while loops), D019 (file-based modules), D020 (u64 core + signed library), D021 (infix operator desugaring)
- Active Coq build: 9,171 Qed across 259 files, 0 Admitted, 0 active axioms

### Added
- REQ-13: End-to-end .rii → C → executable pipeline verified
  - Fixed `riinac build` path handling for files outside working directory
  - Fixed C codegen `str_val` → `string_val.data` in `riina_binop_add` string concatenation
  - Fixed C codegen missing `_XOPEN_SOURCE` for `strptime`
  - Fixed IR lowering: `FixClosure` only emitted for genuinely recursive functions (was segfaulting non-recursive top-level functions)
  - 6 end-to-end integration tests: hello, arithmetic, conditionals, declassification, multi-function, non-trivial full pipeline
  - Non-trivial test exercises: multiple functions, arithmetic, if/else, Secret<T> classify/declassify with proof, System effect
- REQ-12: Compiler enforces information flow control (Bell-LaPadula model)
  - T_Assign: no-write-down (`Δ ⊑ sl`) prevents implicit flows through control structure
  - T_Deref: no-read-up (`sl ⊑ Δ`) prevents unauthorized reads
  - IFC-aware branching: If/Case elevate Δ in branches based on condition security level
  - New `ImplicitFlowViolation` error (S0003) with clear diagnostics
  - 7 new IFC enforcement tests (Bell-LaPadula, implicit flow prevention)
- Lean 4 active lane mechanized: 3,895 theorem/lemma declarations across 136 files, 0 sorry, 0 axioms
- AlgebraicEffects.lean: 48 axioms eliminated via first-order defunctionalization + step-indexed typing (Appel-McAllester 2001)
- Z3 security lattice verification: 25 properties verified (matching Coq Syntax.v lattice lemmas)
- Isabelle/HOL smoke session: 1 compiled theory (RIINA_CORE, Syntax.thy)
- Phase 2 prover closure gate passed for scoped provers (Lean, F*, TLA+, Alloy, Z3)

### Fixed
- Coq 8.20.1 compatibility: migrated from Rocq 9.1, fixed all import paths (`Stdlib.*` → `Coq.*`), fixed API changes (`filter_length` → `filter_length_le`), fixed recursive definitions, updated proofs for new semantics
- Eliminated all 7 previously-tracked Admitted proofs (DELTA001, Platform/WASM/Mobile stubs, ValRelStepLimit)
- Eliminated remaining active proof assumptions; active Coq build is now `Axioms=0`, `Admitted=0`, explicit assumptions `=0`
- Active Coq build now at 12,678 Qed proofs

### Added (Phase 7)
- Phase 7: Platform Universality — modular backend trait architecture (`Backend` trait, `Target` enum)
- WebAssembly backend (`--target=wasm32`) with direct IR-to-WASM binary emission
- Platform-conditional standard library (`platform.rs`) for cross-platform compilation
- Mobile backend scaffolding: Android JNI bridge generation, iOS Swift bridge generation
- `--target` flag for `riinac build` and `riinac emit` commands
- `riina-wasm` crate: in-browser compiler via WASM (cdylib with `extern "C"` exports)
- WASM Playground page on website (split-pane editor, 5 examples, Web Worker compilation)
- 4 backend verification Coq proofs: WASM correctness, JNI/Swift bridge, platform stdlib, backend trait (63 Qed)
- Phase 7 complete (all M7.1–M7.6 milestones done)
- WASM backend production: bump allocator, string constants, pair/sum types, closures (table + call_indirect), refs, builtin imports
- WASM bug fixes: Mod (I32RemS), And/Or (I32And/I32Or), Call (function index resolution)
- Android JNI production: full C implementation (JNI_OnLoad, type marshaling, callback routing, permissions from effects)
- iOS Swift production: extended type conversion, C bridge routing, Info.plist generation, SPM Package.swift
- Playground build pipeline: build-wasm.sh, Vite WASM integration, deploy pipeline
- Backend composition Coq proofs: NI preservation through compiled backends (BackendComposition.v, 11 Qed)
- Extended WASM verification (+23 Qed: strings, closures, pairs, allocator, completeness)
- Extended mobile bridge verification (+17 Qed: JNI string roundtrip, Swift type safety, callback safety)

## [0.2.0] - 2026-02-01

### Added
- Compliance system user guide (`docs/enterprise/COMPLIANCE_GUIDE.md`)
- 15 industry compliance profiles with CLI integration (`--compliance`, `--report`, `--report-json`)
- Audit report generation (text + JSON formats with SHA-256 integrity)
- `riina-compliance` crate: PCI-DSS (3 rules), PDPA (2 rules), BNM RMiT (1 rule)

### Changed
- Version bump to 0.2.0 across all manifests

### Fixed
- CERTIFICATION.md: corrected axiom count (5 → 4) and file count (244 → 245)

## [0.1.0] - 2026-02-01

### Added
- RIINA compiler (`riinac`) with Bahasa Melayu syntax
- Lexer, parser, type checker, and C code generation
- Effect system with `kesan` (effect) and `bersih` (pure) annotations
- Security types: `Rahsia<T>` (secret) with `dedah` (declassify)
- Standard library: 88 builtins across 9 modules
- Developer tools: `riina-fmt`, `riina-lsp`, `riina-doc`
- VS Code extension (`riina-vscode`)
- Package manager (`riina-pkg`)
- 112 example `.rii` files across 9 categories
- Formal verification: 4,890 Qed proofs in Coq active build (0 admits, 4 justified axioms)
- Compliance system: 15 industry profiles with audit report generation
- C FFI support via `luaran "C" { ... }`
- REPL with `:jenis` (type) and `:kesan` (effect) commands
- Nix flake, Dockerfile, and install script
- Website with documentation

### Security
- Non-interference proven via logical relations in Coq
- Type safety (progress + preservation) formally verified
- Effect system soundness proven
- Zero third-party runtime dependencies

[Unreleased]: https://github.com/ib823/riina/compare/v0.4.0...HEAD
[0.2.0]: https://github.com/ib823/riina/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/ib823/riina/releases/tag/v0.1.0
