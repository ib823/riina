# RIINA Research Domain AF: Verified Secure Updates

## Document Control

```
Track: AF (Alpha-Foxtrot)
Version: 1.0.0
Date: 2026-01-17
Classification: FOUNDATIONAL
Status: SPECIFICATION
Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE
```

---

## AF-01: The "Update" Problem & The RIINA Solution

### 1. The Existential Threat

Software updates are a prime attack vector:
- Malicious updates (SolarWinds, CCleaner)
- Rollback attacks reinstall vulnerable versions
- Partial updates leave inconsistent state
- Update servers can be compromised
- Man-in-the-middle on update channel
- Delayed updates extend vulnerability window

**Current state:** Updates are trusted without cryptographic guarantees.

### 2. The RIINA Solution: Verified Secure Updates

```
THEOREM update_safety:
  ∀ update U, system S:
    ApplyUpdate(S, U) = Success →
    Signed(U, vendor_key) ∧
    Version(U) > Version(S) ∧
    Integrity(U) ∧
    Atomic(apply(S, U))
```

### 3. Core Components

#### 3.1 Update Package

```
UpdatePackage ::= {
  metadata: UpdateMetadata,
  payload: EncryptedPayload,
  signatures: List<Signature>,
  dependencies: List<Dependency>,
  rollback_info: RollbackInfo
}

UpdateMetadata ::= {
  version: SemVer,
  requires_version: VersionRange,
  release_date: Timestamp,
  expiry_date: Option<Timestamp>,
  changelog: SignedChangelog,
  security_fixes: List<CVE>
}

RollbackInfo ::= {
  min_version: SemVer,  // Cannot rollback below this
  rollback_protected: Bool,
  anti_rollback_counter: Nat
}
```

#### 3.2 Update Verification

```
UpdateVerification ::= {
  signature_check: SignatureVerification,
  version_check: VersionVerification,
  integrity_check: IntegrityVerification,
  compatibility_check: CompatibilityVerification,
  rollback_check: RollbackVerification
}
```

### 4. Formal Properties

```coq
(* Updates are monotonic *)
Theorem update_monotonicity:
  forall s u s',
    apply_update s u = Some s' ->
    version s' > version s.

(* No rollback below minimum *)
Theorem rollback_protection:
  forall s u,
    version u < rollback_min s ->
    apply_update s u = RollbackPrevented.

(* Atomic update application *)
Theorem update_atomicity:
  forall s u,
    apply_update s u = Success ->
    system_consistent s' \/
    apply_update s u = Failure /\ s = s_original.

(* Update authenticity *)
Theorem update_authentic:
  forall u,
    apply_update _ u = Success ->
    exists key, In key trusted_keys /\ signed_by u key.
```

### 5. Implementation Requirements

```riina
fungsi verify_and_apply_update(
    current: SystemState,
    update: UpdatePackage,
    trusted_keys: Set<PublicKey>
) -> Keputusan<SystemState, UpdateError>
kesan [Crypto, FileSystem, System]
{
    // 1. Verify signatures (threshold: 2 of 3)
    biar valid_sigs = update.signatures
        .iter()
        .filter(|s| trusted_keys.contains(&s.key))
        .filter(|s| verify_signature(s))
        .count();

    kalau valid_sigs < 2 {
        pulang Err(UpdateError::InsufficientSignatures)
    }

    // 2. Verify version is newer (anti-rollback)
    kalau update.metadata.version <= current.version {
        pulang Err(UpdateError::VersionNotNewer)
    }

    // 3. Verify anti-rollback counter (TPM-backed)
    kalau update.rollback_info.anti_rollback_counter <= tpm_read_counter() {
        pulang Err(UpdateError::CounterRollback)
    }

    // 4. Verify compatibility
    kalau !current.version.satisfies(&update.metadata.requires_version) {
        pulang Err(UpdateError::IncompatibleVersion)
    }

    // 5. Verify integrity
    biar payload_hash = compute_hash(&update.payload);
    kalau payload_hash != update.metadata.expected_hash {
        pulang Err(UpdateError::IntegrityFailure)
    }

    // 6. Create backup (for atomic rollback)
    biar backup = create_backup(&current)?;

    // 7. Apply update atomically
    padan apply_update_atomic(&current, &update.payload) {
        Ok(new_state) => {
            // Increment TPM counter (prevents rollback)
            tpm_increment_counter()?;
            // Delete backup
            delete_backup(backup)?;
            Ok(new_state)
        },
        Err(e) => {
            // Restore from backup
            restore_backup(backup)?;
            Err(UpdateError::ApplyFailed(e))
        }
    }
}
```

### 6. Dependencies

| Dependency | Track | Required For |
|------------|-------|--------------|
| Cryptography | G | Signatures |
| Supply chain | AB | Package verification |
| Hardware | S | TPM counter |
| Storage | Σ | Atomic file operations |

### 7. Verification Milestones

| Milestone | Description | Status |
|-----------|-------------|--------|
| AF-M1 | Signature verification | ❌ |
| AF-M2 | Anti-rollback counter | ❌ |
| AF-M3 | Atomic application | ❌ |
| AF-M4 | Recovery on failure | ❌ |
| AF-M5 | Full update flow | ❌ |

---

*Track AF: Verified Secure Updates*
*Status: SPECIFICATION COMPLETE, PROOFS PENDING*
*Last updated: 2026-01-17*
