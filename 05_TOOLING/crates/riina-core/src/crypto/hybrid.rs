//! Hybrid Cryptographic Schemes
//!
//! This module implements hybrid cryptographic schemes that combine classical
//! and post-quantum primitives as required by Law 2.
//!
//! # Law 2: Cryptographic Non-Negotiables
//!
//! - ML-KEM-768 + X25519 hybrid key encapsulation
//! - ML-DSA-65 + Ed25519 hybrid signatures
//!
//! # Rationale for Hybrid Schemes
//!
//! 1. **Defense in Depth**: If either the classical or post-quantum scheme is broken,
//!    the hybrid scheme remains secure.
//!
//! 2. **Quantum Transition**: Organizations need to deploy PQ crypto before quantum
//!    computers arrive, but the algorithms are newer and less battle-tested.
//!
//! 3. **Regulatory Compliance**: Some regulations still require classical crypto,
//!    so hybrid schemes satisfy both requirements.
//!
//! # Hybrid Construction
//!
//! For key encapsulation:
//! ```text
//! shared_secret = KDF(x25519_secret || ml_kem_secret || context)
//! ```
//!
//! For signatures:
//! ```text
//! hybrid_signature = ed25519_signature || ml_dsa_signature
//! ```

use crate::crypto::ed25519::{
    Ed25519SigningKey, Ed25519VerifyingKey, 
    PUBLIC_KEY_SIZE as ED25519_PUBLIC_KEY_SIZE,
    SECRET_KEY_SIZE as ED25519_SECRET_KEY_SIZE,
    SIGNATURE_SIZE as ED25519_SIGNATURE_SIZE,
};
use crate::crypto::hkdf::HkdfSha256;
use crate::crypto::ml_dsa::{
    MlDsa65KeyPair, MlDsa65SigningKey, MlDsa65VerifyingKey,
    PUBLIC_KEY_SIZE as ML_DSA_PUBLIC_KEY_SIZE,
    SECRET_KEY_SIZE as ML_DSA_SECRET_KEY_SIZE,
    SIGNATURE_SIZE as ML_DSA_SIGNATURE_SIZE,
};
use crate::crypto::ml_kem::{
    MlKem768KeyPair, MlKem768EncapsulationKey, MlKem768DecapsulationKey,
    PUBLIC_KEY_SIZE as ML_KEM_PUBLIC_KEY_SIZE,
    SECRET_KEY_SIZE as ML_KEM_SECRET_KEY_SIZE,
    CIPHERTEXT_SIZE as ML_KEM_CIPHERTEXT_SIZE,
    SHARED_SECRET_SIZE as ML_KEM_SHARED_SECRET_SIZE,
};
use crate::crypto::x25519::{
    X25519KeyPair,
    PUBLIC_KEY_SIZE as X25519_PUBLIC_KEY_SIZE,
    PRIVATE_KEY_SIZE as X25519_PRIVATE_KEY_SIZE,
    SHARED_SECRET_SIZE as X25519_SHARED_SECRET_SIZE,
};
use crate::crypto::{CryptoError, CryptoResult};
use crate::zeroize::Zeroize;

// ============================================================================
// Hybrid Key Encapsulation (X25519 + ML-KEM-768)
// ============================================================================

/// Hybrid KEM public key size (X25519 + ML-KEM-768)
pub const HYBRID_KEM_PUBLIC_KEY_SIZE: usize = X25519_PUBLIC_KEY_SIZE + ML_KEM_PUBLIC_KEY_SIZE;
/// Hybrid KEM secret key size (X25519 + ML-KEM-768)
pub const HYBRID_KEM_SECRET_KEY_SIZE: usize = X25519_PRIVATE_KEY_SIZE + ML_KEM_SECRET_KEY_SIZE;
/// Hybrid KEM ciphertext size (X25519 ephemeral + ML-KEM ciphertext)
pub const HYBRID_KEM_CIPHERTEXT_SIZE: usize = X25519_PUBLIC_KEY_SIZE + ML_KEM_CIPHERTEXT_SIZE;
/// Hybrid KEM shared secret size
pub const HYBRID_KEM_SHARED_SECRET_SIZE: usize = 32;

/// Domain separation context for hybrid KEM
const HYBRID_KEM_CONTEXT: &[u8] = b"RIINA-HYBRID-KEM-X25519-ML-KEM-768-v1";

/// Hybrid key encapsulation combining X25519 and ML-KEM-768
pub struct HybridKem {
    /// X25519 key pair
    x25519: X25519KeyPair,
    /// ML-KEM-768 key pair
    ml_kem: MlKem768KeyPair,
}

impl HybridKem {
    /// Generate a new hybrid KEM key pair
    ///
    /// # Arguments
    /// * `random` - At least 128 bytes of cryptographically secure random data
    ///   (32 for X25519, 64 for ML-KEM, 32 for implicit rejection)
    ///
    /// # Errors
    /// Returns error if random data is insufficient or key generation fails.
    pub fn generate(random: &[u8]) -> CryptoResult<Self> {
        if random.len() < 128 {
            return Err(CryptoError::KeyGenerationFailed);
        }

        let x25519_random: [u8; 32] = random[..32]
            .try_into()
            .map_err(|_| CryptoError::KeyGenerationFailed)?;
        let ml_kem_random: [u8; 64] = random[32..96]
            .try_into()
            .map_err(|_| CryptoError::KeyGenerationFailed)?;

        let x25519 = X25519KeyPair::generate(&x25519_random);
        let ml_kem = MlKem768KeyPair::generate(&ml_kem_random)?;

        Ok(Self { x25519, ml_kem })
    }

    /// Get the combined public key
    ///
    /// Format: `x25519_public_key || ml_kem_encapsulation_key`
    #[must_use]
    pub fn public_key(&self) -> [u8; HYBRID_KEM_PUBLIC_KEY_SIZE] {
        let mut pk = [0u8; HYBRID_KEM_PUBLIC_KEY_SIZE];
        pk[..X25519_PUBLIC_KEY_SIZE].copy_from_slice(self.x25519.public_key());
        pk[X25519_PUBLIC_KEY_SIZE..].copy_from_slice(self.ml_kem.encapsulation_key().as_bytes());
        pk
    }

    /// Decapsulate a hybrid ciphertext
    ///
    /// # Arguments
    /// * `ciphertext` - The hybrid ciphertext to decapsulate
    ///
    /// # Returns
    /// The 32-byte combined shared secret
    ///
    /// # Errors
    /// Returns error if either decapsulation fails.
    pub fn decapsulate(
        &self,
        ciphertext: &[u8; HYBRID_KEM_CIPHERTEXT_SIZE],
    ) -> CryptoResult<[u8; HYBRID_KEM_SHARED_SECRET_SIZE]> {
        // Extract components
        let ephemeral_x25519: [u8; X25519_PUBLIC_KEY_SIZE] = ciphertext[..X25519_PUBLIC_KEY_SIZE]
            .try_into()
            .map_err(|_| CryptoError::DecapsulationFailed)?;
        let ml_kem_ct: [u8; ML_KEM_CIPHERTEXT_SIZE] = ciphertext[X25519_PUBLIC_KEY_SIZE..]
            .try_into()
            .map_err(|_| CryptoError::DecapsulationFailed)?;

        // Perform X25519 key agreement
        let x25519_ss = self.x25519.diffie_hellman(&ephemeral_x25519)?;

        // Perform ML-KEM decapsulation
        let ml_kem_ss = self.ml_kem.decapsulate(&ml_kem_ct)?;

        // Combine shared secrets using HKDF
        let mut combined_ikm = [0u8; X25519_SHARED_SECRET_SIZE + ML_KEM_SHARED_SECRET_SIZE];
        combined_ikm[..X25519_SHARED_SECRET_SIZE].copy_from_slice(&x25519_ss);
        combined_ikm[X25519_SHARED_SECRET_SIZE..].copy_from_slice(&ml_kem_ss);

        let shared_secret = HkdfSha256::derive_key(&[], &combined_ikm, HYBRID_KEM_CONTEXT);

        // Zeroize intermediate values
        combined_ikm.zeroize();

        Ok(shared_secret)
    }
}

/// Encapsulate to a hybrid public key
///
/// # Arguments
/// * `public_key` - The recipient's hybrid public key
/// * `random` - At least 64 bytes of random data
///
/// # Returns
/// A tuple of (ciphertext, shared_secret)
///
/// # Errors
/// Returns error if encapsulation fails.
pub fn hybrid_kem_encapsulate(
    public_key: &[u8; HYBRID_KEM_PUBLIC_KEY_SIZE],
    random: &[u8],
) -> CryptoResult<([u8; HYBRID_KEM_CIPHERTEXT_SIZE], [u8; HYBRID_KEM_SHARED_SECRET_SIZE])> {
    if random.len() < 64 {
        return Err(CryptoError::KeyGenerationFailed);
    }

    // Extract public key components
    let x25519_pk: [u8; X25519_PUBLIC_KEY_SIZE] = public_key[..X25519_PUBLIC_KEY_SIZE]
        .try_into()
        .map_err(|_| CryptoError::InvalidKeyLength)?;
    let ml_kem_ek: [u8; ML_KEM_PUBLIC_KEY_SIZE] = public_key[X25519_PUBLIC_KEY_SIZE..]
        .try_into()
        .map_err(|_| CryptoError::InvalidKeyLength)?;

    // Generate ephemeral X25519 key pair and perform key agreement
    let x25519_random: [u8; 32] = random[..32]
        .try_into()
        .map_err(|_| CryptoError::KeyGenerationFailed)?;
    let ephemeral = X25519KeyPair::generate(&x25519_random);
    let x25519_ss = ephemeral.diffie_hellman(&x25519_pk)?;

    // Perform ML-KEM encapsulation
    let ml_kem_ek = MlKem768EncapsulationKey::from_bytes(&ml_kem_ek)?;
    let ml_kem_random: [u8; 32] = random[32..64]
        .try_into()
        .map_err(|_| CryptoError::KeyGenerationFailed)?;
    let (ml_kem_ct, ml_kem_ss) = ml_kem_ek.encapsulate(&ml_kem_random)?;

    // Build ciphertext: ephemeral public key || ML-KEM ciphertext
    let mut ciphertext = [0u8; HYBRID_KEM_CIPHERTEXT_SIZE];
    ciphertext[..X25519_PUBLIC_KEY_SIZE].copy_from_slice(ephemeral.public_key());
    ciphertext[X25519_PUBLIC_KEY_SIZE..].copy_from_slice(&ml_kem_ct);

    // Combine shared secrets using HKDF
    let mut combined_ikm = [0u8; X25519_SHARED_SECRET_SIZE + ML_KEM_SHARED_SECRET_SIZE];
    combined_ikm[..X25519_SHARED_SECRET_SIZE].copy_from_slice(&x25519_ss);
    combined_ikm[X25519_SHARED_SECRET_SIZE..].copy_from_slice(&ml_kem_ss);

    let shared_secret = HkdfSha256::derive_key(&[], &combined_ikm, HYBRID_KEM_CONTEXT);

    // Zeroize intermediate values
    combined_ikm.zeroize();

    Ok((ciphertext, shared_secret))
}

// ============================================================================
// Hybrid Digital Signatures (Ed25519 + ML-DSA-65)
// ============================================================================

/// Hybrid signature public key size (Ed25519 + ML-DSA-65)
pub const HYBRID_SIG_PUBLIC_KEY_SIZE: usize = ED25519_PUBLIC_KEY_SIZE + ML_DSA_PUBLIC_KEY_SIZE;
/// Hybrid signature secret key size (Ed25519 + ML-DSA-65)
pub const HYBRID_SIG_SECRET_KEY_SIZE: usize = ED25519_SECRET_KEY_SIZE + ML_DSA_SECRET_KEY_SIZE;
/// Hybrid signature size (Ed25519 + ML-DSA-65)
pub const HYBRID_SIG_SIGNATURE_SIZE: usize = ED25519_SIGNATURE_SIZE + ML_DSA_SIGNATURE_SIZE;

/// Domain separation context for hybrid signatures
const HYBRID_SIG_CONTEXT: &[u8] = b"RIINA-HYBRID-SIG-Ed25519-ML-DSA-65-v1";

/// Hybrid signature signing key combining Ed25519 and ML-DSA-65
pub struct HybridSigningKey {
    /// Ed25519 signing key
    ed25519: Ed25519SigningKey,
    /// ML-DSA-65 key pair (needed for signing)
    ml_dsa: MlDsa65KeyPair,
}

impl HybridSigningKey {
    /// Generate a new hybrid signing key
    ///
    /// # Arguments
    /// * `random` - At least 64 bytes of cryptographically secure random data
    ///   (32 for Ed25519, 32 for ML-DSA)
    ///
    /// # Errors
    /// Returns error if random data is insufficient or key generation fails.
    pub fn generate(random: &[u8]) -> CryptoResult<Self> {
        if random.len() < 64 {
            return Err(CryptoError::KeyGenerationFailed);
        }

        let ed25519_seed: [u8; 32] = random[..32]
            .try_into()
            .map_err(|_| CryptoError::KeyGenerationFailed)?;
        let ml_dsa_random: [u8; 32] = random[32..64]
            .try_into()
            .map_err(|_| CryptoError::KeyGenerationFailed)?;

        let ed25519 = Ed25519SigningKey::from_seed(&ed25519_seed);
        let ml_dsa = MlDsa65KeyPair::generate(&ml_dsa_random)?;

        Ok(Self { ed25519, ml_dsa })
    }

    /// Get the combined public key
    ///
    /// Format: `ed25519_public_key || ml_dsa_verifying_key`
    #[must_use]
    pub fn public_key(&self) -> [u8; HYBRID_SIG_PUBLIC_KEY_SIZE] {
        let mut pk = [0u8; HYBRID_SIG_PUBLIC_KEY_SIZE];
        pk[..ED25519_PUBLIC_KEY_SIZE].copy_from_slice(self.ed25519.public_key_bytes());
        pk[ED25519_PUBLIC_KEY_SIZE..].copy_from_slice(self.ml_dsa.verifying_key().as_bytes());
        pk
    }

    /// Get the verification key
    #[must_use]
    pub fn verifying_key(&self) -> HybridVerifyingKey {
        HybridVerifyingKey {
            bytes: self.public_key(),
        }
    }

    /// Sign a message with both Ed25519 and ML-DSA-65
    ///
    /// The message is domain-separated before signing:
    /// `H(CONTEXT || len(message) || message)`
    ///
    /// # Arguments
    /// * `message` - The message to sign
    ///
    /// # Returns
    /// The hybrid signature: `ed25519_signature || ml_dsa_signature`
    ///
    /// # Errors
    /// Returns error if either signing operation fails.
    pub fn sign(&self, message: &[u8]) -> CryptoResult<[u8; HYBRID_SIG_SIGNATURE_SIZE]> {
        // Create domain-separated message
        let domain_sep_msg = create_domain_separated_message(message);

        // Sign with Ed25519
        let ed25519_sig = self.ed25519.sign(&domain_sep_msg);

        // Sign with ML-DSA-65
        let ml_dsa_sig = self.ml_dsa.sign(&domain_sep_msg)?;

        // Combine signatures
        let mut signature = [0u8; HYBRID_SIG_SIGNATURE_SIZE];
        signature[..ED25519_SIGNATURE_SIZE].copy_from_slice(&ed25519_sig);
        signature[ED25519_SIGNATURE_SIZE..].copy_from_slice(&ml_dsa_sig);

        Ok(signature)
    }
}

/// Hybrid signature verification key combining Ed25519 and ML-DSA-65
pub struct HybridVerifyingKey {
    /// Combined public key bytes
    bytes: [u8; HYBRID_SIG_PUBLIC_KEY_SIZE],
}

impl HybridVerifyingKey {
    /// Create from bytes
    ///
    /// # Errors
    /// Returns error if validation fails.
    pub fn from_bytes(bytes: &[u8; HYBRID_SIG_PUBLIC_KEY_SIZE]) -> CryptoResult<Self> {
        // TODO: Validate both public keys
        Ok(Self { bytes: *bytes })
    }

    /// Get the public key bytes
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; HYBRID_SIG_PUBLIC_KEY_SIZE] {
        &self.bytes
    }

    /// Verify a hybrid signature
    ///
    /// **Both** Ed25519 and ML-DSA-65 signatures must be valid.
    ///
    /// # Arguments
    /// * `message` - The message that was signed
    /// * `signature` - The hybrid signature to verify
    ///
    /// # Errors
    /// Returns `InvalidSignature` if either verification fails.
    pub fn verify(
        &self,
        message: &[u8],
        signature: &[u8; HYBRID_SIG_SIGNATURE_SIZE],
    ) -> CryptoResult<()> {
        // Extract public key components
        let ed25519_pk: [u8; ED25519_PUBLIC_KEY_SIZE] = self.bytes[..ED25519_PUBLIC_KEY_SIZE]
            .try_into()
            .map_err(|_| CryptoError::InvalidSignature)?;
        let ml_dsa_pk: [u8; ML_DSA_PUBLIC_KEY_SIZE] = self.bytes[ED25519_PUBLIC_KEY_SIZE..]
            .try_into()
            .map_err(|_| CryptoError::InvalidSignature)?;

        // Extract signature components
        let ed25519_sig: [u8; ED25519_SIGNATURE_SIZE] = signature[..ED25519_SIGNATURE_SIZE]
            .try_into()
            .map_err(|_| CryptoError::InvalidSignature)?;
        let ml_dsa_sig: [u8; ML_DSA_SIGNATURE_SIZE] = signature[ED25519_SIGNATURE_SIZE..]
            .try_into()
            .map_err(|_| CryptoError::InvalidSignature)?;

        // Create domain-separated message
        let domain_sep_msg = create_domain_separated_message(message);

        // Verify Ed25519 signature
        let ed25519_vk = Ed25519VerifyingKey::from_bytes(&ed25519_pk)?;
        ed25519_vk.verify(&domain_sep_msg, &ed25519_sig)?;

        // Verify ML-DSA-65 signature
        let ml_dsa_vk = MlDsa65VerifyingKey::from_bytes(&ml_dsa_pk)?;
        ml_dsa_vk.verify(&domain_sep_msg, &ml_dsa_sig)?;

        Ok(())
    }
}

/// Create a domain-separated message for hybrid signing
///
/// Format: `CONTEXT || len(message) as 8-byte BE || message`
fn create_domain_separated_message(message: &[u8]) -> Vec<u8> {
    let len_bytes = (message.len() as u64).to_be_bytes();
    let mut result = Vec::with_capacity(HYBRID_SIG_CONTEXT.len() + 8 + message.len());
    result.extend_from_slice(HYBRID_SIG_CONTEXT);
    result.extend_from_slice(&len_bytes);
    result.extend_from_slice(message);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hybrid_kem_sizes() {
        assert_eq!(HYBRID_KEM_PUBLIC_KEY_SIZE, 32 + 1184); // X25519 + ML-KEM-768
        assert_eq!(HYBRID_KEM_SECRET_KEY_SIZE, 32 + 2400);
        assert_eq!(HYBRID_KEM_CIPHERTEXT_SIZE, 32 + 1088);
        assert_eq!(HYBRID_KEM_SHARED_SECRET_SIZE, 32);
    }

    #[test]
    fn test_hybrid_sig_sizes() {
        assert_eq!(HYBRID_SIG_PUBLIC_KEY_SIZE, 32 + 1952); // Ed25519 + ML-DSA-65
        assert_eq!(HYBRID_SIG_SECRET_KEY_SIZE, 32 + 4032);
        assert_eq!(HYBRID_SIG_SIGNATURE_SIZE, 64 + 3309);
    }

    #[test]
    fn test_domain_separated_message() {
        let msg = b"test message";
        let result = create_domain_separated_message(msg);
        
        assert!(result.starts_with(HYBRID_SIG_CONTEXT));
        let len_start = HYBRID_SIG_CONTEXT.len();
        let len_bytes: [u8; 8] = result[len_start..len_start + 8]
            .try_into()
            .unwrap();
        assert_eq!(u64::from_be_bytes(len_bytes), msg.len() as u64);
        assert_eq!(&result[len_start + 8..], msg);
    }

    #[test]
    #[ignore = "Implementation pending - requires completed X25519/ML-KEM"]
    fn test_hybrid_kem_key_generation() {
        let random = [0x42u8; 128];
        let keypair = HybridKem::generate(&random);
        assert!(keypair.is_ok());
    }

    #[test]
    #[ignore = "Implementation pending - requires completed Ed25519/ML-DSA"]
    fn test_hybrid_sig_key_generation() {
        let random = [0x42u8; 64];
        let keypair = HybridSigningKey::generate(&random);
        assert!(keypair.is_ok());
    }

    #[test]
    #[ignore = "Implementation pending"]
    fn test_hybrid_kem_roundtrip() {
        let random = [0x42u8; 128];
        let keypair = HybridKem::generate(&random).unwrap();
        let pk = keypair.public_key();
        
        let enc_random = [0x24u8; 64];
        let (ct, ss1) = hybrid_kem_encapsulate(&pk, &enc_random).unwrap();
        
        let ss2 = keypair.decapsulate(&ct).unwrap();
        assert_eq!(ss1, ss2);
    }

    #[test]
    #[ignore = "Implementation pending"]
    fn test_hybrid_sig_roundtrip() {
        let random = [0x42u8; 64];
        let signing_key = HybridSigningKey::generate(&random).unwrap();
        let verifying_key = signing_key.verifying_key();
        
        let message = b"The quick brown fox jumps over the lazy dog";
        let signature = signing_key.sign(message).unwrap();
        
        assert!(verifying_key.verify(message, &signature).is_ok());
    }

    #[test]
    #[ignore = "Implementation pending"]
    fn test_hybrid_sig_wrong_message() {
        let random = [0x42u8; 64];
        let signing_key = HybridSigningKey::generate(&random).unwrap();
        let verifying_key = signing_key.verifying_key();
        
        let message = b"Original message";
        let signature = signing_key.sign(message).unwrap();
        
        let wrong_message = b"Wrong message";
        assert!(verifying_key.verify(wrong_message, &signature).is_err());
    }
}
