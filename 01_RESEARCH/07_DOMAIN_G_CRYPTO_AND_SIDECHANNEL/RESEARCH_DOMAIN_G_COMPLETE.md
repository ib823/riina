# TERAS-LANG Research Domain G: Cryptographic Foundations

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-G-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | G-01 through G-10 |
| Domain | G: Cryptographic Foundations |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# G-01: Cryptographic Type Systems

## Executive Summary

Cryptographic type systems enforce correct usage of cryptographic primitives at compile time, preventing misuse such as key reuse, algorithm confusion, and improper modes.

## Key Concepts

### Typed Cryptographic APIs

```rust
// Key types prevent confusion
struct AesKey<const BITS: usize>;  // AES-128, AES-256
struct RsaPrivateKey<const BITS: usize>;
struct Ed25519PrivateKey;
struct X25519PrivateKey;

// Algorithm-specific operations
impl AesKey<256> {
    fn encrypt(&self, nonce: &Nonce, plaintext: &[u8]) -> Ciphertext;
    fn decrypt(&self, nonce: &Nonce, ciphertext: &Ciphertext) -> Result<Vec<u8>, DecryptError>;
}

// Type prevents: AES key used for RSA, wrong key size, etc.
```

### Nonce Tracking

```rust
// Linear nonce prevents reuse
struct Nonce(lin [u8; 12]);

fn encrypt(key: &AesKey, nonce: Nonce, data: &[u8]) -> Ciphertext {
    // nonce consumed, cannot be reused
}

// Type error: nonce used twice
let nonce = generate_nonce();
encrypt(&key, nonce, data1);
encrypt(&key, nonce, data2);  // ERROR: nonce already consumed
```

### Key Lifecycle

```rust
// Typestate for key lifecycle
struct Key<State> {
    material: SecureBox<[u8; 32]>,
    _state: PhantomData<State>,
}

struct Generated;
struct Active;
struct Compromised;
struct Destroyed;

impl Key<Generated> {
    fn activate(self) -> Key<Active> { ... }
}

impl Key<Active> {
    fn use_for_signing(&self) -> Signature { ... }
    fn compromise(self) -> Key<Compromised> { ... }
    fn destroy(self) -> Key<Destroyed> { ... }
}

impl Key<Compromised> {
    // Cannot use for signing!
    fn destroy(self) -> Key<Destroyed> { ... }
}
```

## TERAS Decision G-01

**IMPLEMENT** cryptographic type system:
1. Distinct types per algorithm/key size
2. Linear nonces for single-use
3. Typestate for key lifecycle
4. Compile-time algorithm correctness

### Architecture Decision ID: `TERAS-ARCH-G01-CRY-001`

---

# G-02: Post-Quantum Cryptography

## Algorithms

```
NIST PQC Standards (2024):
├── ML-KEM (Kyber): Key encapsulation
├── ML-DSA (Dilithium): Digital signatures
├── SLH-DSA (SPHINCS+): Hash-based signatures
└── (Future) FN-DSA (Falcon): Signatures

Hybrid Approach:
    Classical + PQC for transition period
    e.g., X25519 + ML-KEM-768
```

## TERAS PQC Types

```rust
// Post-quantum key types
struct MlKemPublicKey<const K: usize>;   // K=2,3,4 for 512,768,1024
struct MlKemPrivateKey<const K: usize>;
struct MlDsaPublicKey<const K: usize>;
struct MlDsaPrivateKey<const K: usize>;

// Hybrid types
struct HybridKemPublicKey {
    classical: X25519PublicKey,
    pqc: MlKemPublicKey<3>,
}

// Hybrid encapsulation
fn hybrid_encapsulate(pk: &HybridKemPublicKey) -> (HybridCiphertext, SharedSecret) {
    let (c1, ss1) = x25519_encapsulate(&pk.classical);
    let (c2, ss2) = ml_kem_encapsulate(&pk.pqc);
    let ss = kdf(ss1, ss2);  // Combine secrets
    (HybridCiphertext { c1, c2 }, ss)
}
```

## TERAS Decision G-02

**IMPLEMENT** PQC support:
1. ML-KEM for key exchange
2. ML-DSA for signatures
3. Hybrid mode for transition
4. Algorithm agility for upgrades

### Architecture Decision ID: `TERAS-ARCH-G02-PQC-001`

---

# G-03: Verified Cryptography

## Formal Verification Approaches

```
Verification Levels:

1. Specification Level
   - Mathematical correctness
   - Security proofs (provable security)

2. Implementation Level
   - Functional correctness
   - Side-channel resistance
   - Memory safety

3. Compilation Level
   - Preservation of properties
   - Optimization safety
```

## Verified Crypto Libraries

```
Verified Implementations:
├── HACL* (F*): AES, ChaCha20, Poly1305, Curve25519, SHA2/3
├── Jasmin: Assembly-level verification
├── Fiat-Crypto: Field arithmetic
├── AWS-LC: Partial verification
└── Vale: Verified assembly
```

## TERAS Verified Crypto Integration

```rust
// Import verified implementations
extern "hacl" {
    fn chacha20_poly1305_encrypt(
        key: &[u8; 32],
        nonce: &[u8; 12],
        aad: &[u8],
        plaintext: &[u8],
        ciphertext: &mut [u8],
        tag: &mut [u8; 16]
    );
}

// Wrap with TERAS types
pub fn encrypt_aead(
    key: &ChaCha20Poly1305Key,
    nonce: Nonce,  // Linear
    aad: &[u8],
    plaintext: &[u8]
) -> AuthenticatedCiphertext {
    let mut ct = vec![0u8; plaintext.len()];
    let mut tag = [0u8; 16];
    unsafe {
        chacha20_poly1305_encrypt(
            key.as_bytes(),
            nonce.as_bytes(),
            aad,
            plaintext,
            &mut ct,
            &mut tag
        );
    }
    AuthenticatedCiphertext { ciphertext: ct, tag }
}
```

## TERAS Decision G-03

**INTEGRATE** verified crypto:
1. Use HACL*/Jasmin implementations
2. Wrap with TERAS type system
3. Verify wrapper code
4. Maintain verification chain

### Architecture Decision ID: `TERAS-ARCH-G03-VER-001`

---

# G-04: Side-Channel Resistance

## Side-Channel Types

```
Side Channels:
├── Timing: Variable execution time
├── Cache: Memory access patterns
├── Power: Energy consumption
├── EM: Electromagnetic emanations
└── Fault: Induced errors
```

## Constant-Time Programming

```rust
// Constant-time trait
trait ConstantTime {
    fn ct_eq(&self, other: &Self) -> bool;
    fn ct_select(a: &Self, b: &Self, choice: bool) -> Self;
}

impl ConstantTime for [u8; 32] {
    fn ct_eq(&self, other: &Self) -> bool {
        let mut diff = 0u8;
        for i in 0..32 {
            diff |= self[i] ^ other[i];
        }
        // No early return!
        diff == 0
    }
    
    fn ct_select(a: &Self, b: &Self, choice: bool) -> Self {
        let mask = (choice as u8).wrapping_neg();
        let mut result = [0u8; 32];
        for i in 0..32 {
            result[i] = (a[i] & !mask) | (b[i] & mask);
        }
        result
    }
}
```

## Constant-Time Type Annotations

```rust
// Mark secret data
#[secret]
struct PrivateKey([u8; 32]);

// Compiler enforces constant-time for secret data
impl PrivateKey {
    #[constant_time]
    fn sign(&self, message: &[u8]) -> Signature {
        // Compiler rejects branches on self
        // Compiler rejects variable-time operations
    }
}

// Error examples
#[constant_time]
fn bad_compare(secret: &[u8], public: &[u8]) -> bool {
    secret == public  // ERROR: early-exit comparison on secret
}

#[constant_time]
fn bad_index(secret: &[u8], idx: usize) -> u8 {
    secret[idx]  // ERROR: variable-time memory access
}
```

## TERAS Decision G-04

**ENFORCE** constant-time:
1. Secret type annotations
2. Constant-time verification
3. Reject variable-time operations on secrets
4. Verified constant-time primitives

### Architecture Decision ID: `TERAS-ARCH-G04-CT-001`

---

# G-05: Key Management

## Key Hierarchy

```
TERAS Key Hierarchy:

Root Key (HSM-protected)
    │
    ├── Master Key Encryption Key (KEK)
    │       │
    │       ├── Data Encryption Keys (DEK)
    │       │       ├── File encryption
    │       │       ├── Database encryption
    │       │       └── Communication encryption
    │       │
    │       └── Key Wrapping Keys
    │
    ├── Master Signing Key
    │       │
    │       ├── Code Signing Key
    │       ├── Document Signing Key
    │       └── Certificate Signing Key
    │
    └── Master Agreement Key
            │
            ├── TLS Keys
            └── Key Exchange Keys
```

## Key Management Types

```rust
// Key purpose enforcement
trait KeyPurpose {}
struct Encryption;
struct Signing;
struct KeyWrapping;
struct KeyAgreement;

struct ManagedKey<P: KeyPurpose, A: Algorithm> {
    id: KeyId,
    material: Option<SecureBox<KeyMaterial>>,  // May be HSM-only
    metadata: KeyMetadata,
    _purpose: PhantomData<P>,
    _algorithm: PhantomData<A>,
}

// Type prevents misuse
impl<A: EncryptionAlgorithm> ManagedKey<Encryption, A> {
    fn encrypt(&self, data: &[u8]) -> EncryptedData { ... }
    fn decrypt(&self, data: &EncryptedData) -> Vec<u8> { ... }
    // Cannot sign!
}

impl<A: SigningAlgorithm> ManagedKey<Signing, A> {
    fn sign(&self, data: &[u8]) -> Signature { ... }
    // Cannot encrypt!
}
```

## HSM Integration

```rust
// HSM-backed keys
struct HsmKey<P: KeyPurpose> {
    handle: HsmHandle,
    _purpose: PhantomData<P>,
}

impl<P: KeyPurpose> HsmKey<P> {
    // Key material never leaves HSM
    fn operation(&self, input: &[u8]) -> Vec<u8> {
        hsm_call(self.handle, input)
    }
}

// Effect for HSM operations
effect Hsm {
    fn generate_key(params: KeyParams) -> HsmHandle;
    fn sign(handle: HsmHandle, data: &[u8]) -> Signature;
    fn decrypt(handle: HsmHandle, ciphertext: &[u8]) -> Vec<u8>;
}
```

## TERAS Decision G-05

**IMPLEMENT** key management:
1. Hierarchical key structure
2. Purpose-bound key types
3. HSM integration
4. Key lifecycle tracking

### Architecture Decision ID: `TERAS-ARCH-G05-KM-001`

---

# G-06: Secure Random Number Generation

## RNG Types

```rust
// CSPRNG trait
trait SecureRng {
    fn fill_bytes(&mut self, dest: &mut [u8]);
    fn next_u64(&mut self) -> u64;
}

// System RNG (OS-provided)
struct OsRng;

impl SecureRng for OsRng {
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        getrandom(dest).expect("OS RNG failed");
    }
}

// DRBG (deterministic)
struct HmacDrbg {
    key: [u8; 32],
    counter: [u8; 32],
    reseed_counter: u64,
}

impl SecureRng for HmacDrbg {
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        if self.reseed_counter > RESEED_INTERVAL {
            self.reseed();
        }
        // Generate output
    }
}
```

## RNG Effect

```rust
// Random as effect
effect Random {
    fn random_bytes(len: usize) -> Vec<u8>;
    fn random_u64() -> u64;
    fn random_range(min: u64, max: u64) -> u64;
}

// Handler with audit
handler secure_random_handler(rng: impl SecureRng) for Random {
    random_bytes(len) resume => {
        let mut bytes = vec![0u8; len];
        rng.fill_bytes(&mut bytes);
        Audit::log(RandomGeneration { len });
        resume(bytes)
    }
}
```

## TERAS Decision G-06

**IMPLEMENT** secure RNG:
1. OS-backed CSPRNG default
2. DRBG for deterministic testing
3. Random as effect for tracking
4. Audit all random generation

### Architecture Decision ID: `TERAS-ARCH-G06-RNG-001`

---

# G-07: Authenticated Encryption

## AEAD Constructions

```rust
// AEAD trait
trait Aead {
    const KEY_SIZE: usize;
    const NONCE_SIZE: usize;
    const TAG_SIZE: usize;
    
    fn encrypt(
        key: &[u8; Self::KEY_SIZE],
        nonce: &[u8; Self::NONCE_SIZE],
        aad: &[u8],
        plaintext: &[u8]
    ) -> (Vec<u8>, [u8; Self::TAG_SIZE]);
    
    fn decrypt(
        key: &[u8; Self::KEY_SIZE],
        nonce: &[u8; Self::NONCE_SIZE],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8; Self::TAG_SIZE]
    ) -> Result<Vec<u8>, AuthError>;
}

// Implementations
struct ChaCha20Poly1305;
struct Aes256Gcm;
struct Aes256GcmSiv;  // Nonce-misuse resistant
```

## Nonce Management

```rust
// Counter-based nonce (sequential)
struct CounterNonce {
    prefix: [u8; 4],  // Random per key
    counter: AtomicU64,
}

impl CounterNonce {
    fn next(&self) -> [u8; 12] {
        let c = self.counter.fetch_add(1, Ordering::SeqCst);
        let mut nonce = [0u8; 12];
        nonce[..4].copy_from_slice(&self.prefix);
        nonce[4..].copy_from_slice(&c.to_be_bytes());
        nonce
    }
}

// Random nonce (requires 256-bit nonces or SIV)
struct RandomNonce;

impl RandomNonce {
    fn generate() -> [u8; 24] {  // XChaCha20 uses 24-byte
        let mut nonce = [0u8; 24];
        OsRng.fill_bytes(&mut nonce);
        nonce
    }
}
```

## TERAS Decision G-07

**IMPLEMENT** AEAD:
1. ChaCha20-Poly1305 default
2. AES-GCM-SIV for nonce-misuse resistance
3. Counter-based nonce management
4. Linear nonce types

### Architecture Decision ID: `TERAS-ARCH-G07-AEAD-001`

---

# G-08: Digital Signatures

## Signature Schemes

```rust
// Signature trait
trait SignatureScheme {
    type PublicKey;
    type PrivateKey;
    type Signature;
    
    fn generate() -> (Self::PublicKey, Self::PrivateKey);
    fn sign(sk: &Self::PrivateKey, msg: &[u8]) -> Self::Signature;
    fn verify(pk: &Self::PublicKey, msg: &[u8], sig: &Self::Signature) -> bool;
}

// Implementations
struct Ed25519;
struct MlDsa65;      // Post-quantum
struct HybridSig;    // Ed25519 + ML-DSA

impl SignatureScheme for HybridSig {
    type PublicKey = (Ed25519PublicKey, MlDsa65PublicKey);
    type PrivateKey = (Ed25519PrivateKey, MlDsa65PrivateKey);
    type Signature = (Ed25519Signature, MlDsa65Signature);
    
    fn verify(pk: &Self::PublicKey, msg: &[u8], sig: &Self::Signature) -> bool {
        Ed25519::verify(&pk.0, msg, &sig.0) && MlDsa65::verify(&pk.1, msg, &sig.1)
    }
}
```

## Signature Effect

```rust
// Signing as capability-protected effect
effect Signing {
    fn sign(data: &[u8]) -> Signature;
    fn verify(pk: &PublicKey, data: &[u8], sig: &Signature) -> bool;
}

// Handler requires capability
handler signing_handler(key: SigningKey) for Signing 
    @ {Capability::CryptoSign}  // Coeffect requirement
{
    sign(data) resume => {
        let sig = key.sign(data);
        Audit::log(SigningOperation { key_id: key.id() });
        resume(sig)
    }
}
```

## TERAS Decision G-08

**IMPLEMENT** signatures:
1. Ed25519 for classical
2. ML-DSA for post-quantum
3. Hybrid for transition
4. Capability-protected signing

### Architecture Decision ID: `TERAS-ARCH-G08-SIG-001`

---

# G-09: Cryptographic Protocols

## Protocol Types

```rust
// Session types for protocols
type TlsClient = 
    Send<ClientHello> .
    Recv<ServerHello> .
    Recv<Certificate> .
    Recv<ServerHelloDone> .
    Send<ClientKeyExchange> .
    Send<ChangeCipherSpec> .
    Send<Finished> .
    Recv<ChangeCipherSpec> .
    Recv<Finished> .
    SecureChannel;

// Protocol state machine
enum TlsState {
    Initial,
    SentClientHello,
    ReceivedServerHello,
    // ...
    Established(SecureChannel),
}
```

## Verified Protocol Implementation

```rust
// State machine verified by types
struct TlsHandshake<S: TlsState> {
    state: S,
    transcript: Transcript,
}

impl TlsHandshake<Initial> {
    fn send_client_hello(self) -> (ClientHello, TlsHandshake<SentClientHello>) {
        // ...
    }
}

impl TlsHandshake<SentClientHello> {
    fn receive_server_hello(self, sh: ServerHello) -> TlsHandshake<ReceivedServerHello> {
        // ...
    }
}

// Cannot skip states - type system enforces
```

## TERAS Decision G-09

**IMPLEMENT** protocol types:
1. Session types for protocols
2. State machine enforcement
3. Transcript binding
4. Verified implementations

### Architecture Decision ID: `TERAS-ARCH-G09-PROTO-001`

---

# G-10: Cryptographic Agility

## Algorithm Registry

```rust
// Algorithm identifiers
#[derive(Clone, Copy)]
enum SymmetricAlgorithm {
    Aes128Gcm,
    Aes256Gcm,
    ChaCha20Poly1305,
    Aes256GcmSiv,
}

#[derive(Clone, Copy)]
enum AsymmetricAlgorithm {
    Rsa2048,
    Rsa4096,
    EcdsaP256,
    EcdsaP384,
    Ed25519,
    X25519,
    MlKem768,
    MlDsa65,
}

// Algorithm negotiation
struct AlgorithmSuite {
    symmetric: SymmetricAlgorithm,
    asymmetric: AsymmetricAlgorithm,
    hash: HashAlgorithm,
    kdf: KdfAlgorithm,
}

impl AlgorithmSuite {
    fn negotiate(offered: &[AlgorithmSuite], accepted: &[AlgorithmSuite]) -> Option<AlgorithmSuite> {
        // Find strongest mutually supported
    }
}
```

## Upgrade Path

```rust
// Version-tagged cryptographic data
struct VersionedCiphertext {
    version: u32,
    algorithm: SymmetricAlgorithm,
    ciphertext: Vec<u8>,
}

impl VersionedCiphertext {
    fn decrypt(&self, keys: &KeyStore) -> Result<Vec<u8>, CryptoError> {
        match self.algorithm {
            SymmetricAlgorithm::Aes128Gcm => {
                let key = keys.get_aes128_key(self.version)?;
                aes128gcm_decrypt(&key, &self.ciphertext)
            }
            // ... handle all algorithms
        }
    }
    
    fn upgrade(&self, keys: &KeyStore, new_algo: SymmetricAlgorithm) -> Result<Self, CryptoError> {
        let plaintext = self.decrypt(keys)?;
        let new_key = keys.get_current_key(new_algo)?;
        encrypt(new_algo, &new_key, &plaintext)
    }
}
```

## TERAS Decision G-10

**IMPLEMENT** crypto agility:
1. Algorithm registry
2. Version tagging
3. Negotiation support
4. Upgrade mechanisms

### Architecture Decision ID: `TERAS-ARCH-G10-AGIL-001`

---

# Domain G Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| G-01 | Crypto Types | TERAS-ARCH-G01-CRY-001 |
| G-02 | Post-Quantum | TERAS-ARCH-G02-PQC-001 |
| G-03 | Verified Crypto | TERAS-ARCH-G03-VER-001 |
| G-04 | Side-Channels | TERAS-ARCH-G04-CT-001 |
| G-05 | Key Management | TERAS-ARCH-G05-KM-001 |
| G-06 | RNG | TERAS-ARCH-G06-RNG-001 |
| G-07 | AEAD | TERAS-ARCH-G07-AEAD-001 |
| G-08 | Signatures | TERAS-ARCH-G08-SIG-001 |
| G-09 | Protocols | TERAS-ARCH-G09-PROTO-001 |
| G-10 | Agility | TERAS-ARCH-G10-AGIL-001 |

## Domain G: COMPLETE

---

*Research Track Output — Domain G: Cryptographic Foundations*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
