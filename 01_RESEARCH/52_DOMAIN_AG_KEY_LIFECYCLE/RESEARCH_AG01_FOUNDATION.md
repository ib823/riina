# RIINA Research Domain AG: Verified Key Lifecycle Management

## Document Control

```
Track: AG (Alpha-Golf)
Version: 1.0.0
Date: 2026-01-17
Classification: FOUNDATIONAL
Status: SPECIFICATION
Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | INFINITE TIMELINE
```

---

## AG-01: The "Key Management" Problem & The RIINA Solution

### 1. The Existential Threat

Keys are the foundation of all cryptographic security, yet:
- Keys generated with weak entropy
- Keys stored in plaintext
- Keys never rotated
- Key compromise undetected
- No secure key destruction
- Key escrow/recovery weak or absent

**Current state:** Key management is ad-hoc and error-prone.

### 2. The RIINA Solution: Verified Key Lifecycle

```
THEOREM key_lifecycle_secure:
  ∀ key K:
    Generated(K, verified_entropy) ∧
    Stored(K, HSM ∨ encrypted) ∧
    Used(K, authorized_operations_only) ∧
    Rotated(K, policy_schedule) ∧
    Destroyed(K, secure_zeroization)
```

### 3. Core Components

#### 3.1 Key Types

```
KeyType ::=
  | SymmetricKey of { algorithm: SymAlgo, size: KeySize }
  | AsymmetricKeyPair of { algorithm: AsymAlgo, public: PublicKey, private: PrivateKey }
  | DerivedKey of { parent: KeyId, derivation: KDF, context: Bytes }
  | WrappedKey of { wrapped: Bytes, wrapper: KeyId }

KeyState ::= Active | Suspended | Compromised | Expired | Destroyed

KeyMetadata ::= {
  id: KeyId,
  type: KeyType,
  state: KeyState,
  created: Timestamp,
  expires: Option<Timestamp>,
  rotation_policy: RotationPolicy,
  usage_policy: UsagePolicy,
  audit_log: AuditLogRef
}
```

#### 3.2 Key Storage

```
KeyStorage ::=
  | HSM of { slot: HSMSlot, extractable: Bool }
  | TPM of { handle: TPMHandle, policy: TPMPolicy }
  | EncryptedFile of { path: Path, kek: KeyId }
  | SecureEnclave of { identifier: EnclaveId }
  | SplitKey of { shares: List<KeyShare>, threshold: Nat }
```

#### 3.3 Key Operations

```
KeyOperation ::=
  | Generate of { type: KeyType, entropy_source: EntropySource }
  | Import of { key_material: EncryptedKeyMaterial }
  | Export of { format: KeyFormat, wrapping: Option<KeyId> }
  | Rotate of { new_key: KeyId, migration: MigrationPolicy }
  | Revoke of { reason: RevocationReason }
  | Destroy of { method: DestructionMethod }
```

### 4. Formal Properties

```coq
(* Keys are generated with sufficient entropy *)
Theorem key_entropy:
  forall k,
    generated k verified_rng ->
    entropy k >= min_entropy (key_type k).

(* Private keys never leave secure storage unencrypted *)
Theorem key_confinement:
  forall k op,
    is_private k ->
    operation k op ->
    ~(exported_plaintext k).

(* Destroyed keys are unrecoverable *)
Theorem key_destruction:
  forall k,
    destroyed k ->
    forall adversary, ~(recoverable adversary k).

(* Key rotation maintains security *)
Theorem key_rotation_secure:
  forall k_old k_new,
    rotate k_old k_new ->
    security_level k_new >= security_level k_old.
```

### 5. Implementation Requirements

```riina
struktur KeyManager {
    hsm: HSMConnection,
    policy: KeyPolicy,
    audit: AuditLog
}

fungsi generate_key(
    manager: &KeyManager,
    key_type: KeyType,
    policy: UsagePolicy
) -> Keputusan<KeyId, KeyError>
kesan [Crypto, HSM]
{
    // Generate in HSM (key material never exposed)
    biar key_id = manager.hsm.generate_key(key_type)?;

    // Set usage policy
    manager.hsm.set_policy(key_id, policy)?;

    // Log generation
    manager.audit.log(KeyEvent::Generated {
        key_id,
        key_type,
        timestamp: now()
    })?;

    Ok(key_id)
}

fungsi rotate_key(
    manager: &KeyManager,
    old_key: KeyId,
    migration: MigrationPolicy
) -> Keputusan<KeyId, KeyError>
kesan [Crypto, HSM]
{
    // Generate new key with same type
    biar key_type = manager.hsm.get_key_type(old_key)?;
    biar new_key = manager.hsm.generate_key(key_type)?;

    // Copy policy
    biar policy = manager.hsm.get_policy(old_key)?;
    manager.hsm.set_policy(new_key, policy)?;

    // Execute migration
    padan migration {
        MigrationPolicy::ReEncrypt(data_refs) => {
            untuk data_ref dalam data_refs {
                re_encrypt(manager, data_ref, old_key, new_key)?;
            }
        },
        MigrationPolicy::DualKey(duration) => {
            // Both keys active for transition period
            manager.hsm.set_state(old_key, KeyState::Suspended)?;
            schedule_destruction(old_key, duration)?;
        }
    }

    // Mark old key as rotated
    manager.audit.log(KeyEvent::Rotated {
        old_key,
        new_key,
        timestamp: now()
    })?;

    Ok(new_key)
}

fungsi destroy_key(
    manager: &KeyManager,
    key_id: KeyId,
    reason: DestructionReason
) -> Keputusan<(), KeyError>
kesan [Crypto, HSM]
{
    // Verify key can be destroyed
    biar state = manager.hsm.get_state(key_id)?;
    kalau state == KeyState::Active {
        pulang Err(KeyError::CannotDestroyActiveKey)
    }

    // Secure destruction in HSM
    manager.hsm.zeroize_key(key_id)?;

    // Log destruction
    manager.audit.log(KeyEvent::Destroyed {
        key_id,
        reason,
        timestamp: now()
    })?;

    Ok(())
}
```

### 6. Dependencies

| Dependency | Track | Required For |
|------------|-------|--------------|
| Cryptography | G | Key algorithms |
| Hardware | Φ | HSM/TPM |
| Audit | AE | Key event logging |
| Memory | W | Secure zeroization |

### 7. Verification Milestones

| Milestone | Description | Status |
|-----------|-------------|--------|
| AG-M1 | Key generation verified | ❌ |
| AG-M2 | Key storage verified | ❌ |
| AG-M3 | Key rotation verified | ❌ |
| AG-M4 | Key destruction verified | ❌ |
| AG-M5 | Full lifecycle verified | ❌ |

---

*Track AG: Verified Key Lifecycle Management*
*Status: SPECIFICATION COMPLETE, PROOFS PENDING*
*Last updated: 2026-01-17*
