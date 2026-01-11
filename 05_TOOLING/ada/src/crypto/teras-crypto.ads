-- ═══════════════════════════════════════════════════════════════════════════════
-- TERAS CRYPTO PACKAGE
-- Track F/E Deliverable: Ada/SPARK Crypto Core
-- ═══════════════════════════════════════════════════════════════════════════════
--
-- SPARK Status: PLATINUM
-- Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
--
-- Parent package for all TERAS cryptographic primitives.
-- Child packages:
--   - Teras.Crypto.AES    : AES-256 block cipher
--   - Teras.Crypto.SHA3   : SHA3-256 and SHAKE
--   - Teras.Crypto.ML_KEM : ML-KEM-1024 (post-quantum KEM)
--   - Teras.Crypto.ML_DSA : ML-DSA-65 (post-quantum signatures)

pragma SPARK_Mode (On);

package Teras.Crypto
   with Pure,
        SPARK_Mode => On
is

   --  All cryptographic operations must be constant-time.
   --  This is enforced through:
   --  1. No secret-dependent branches
   --  2. No secret-dependent memory accesses
   --  3. SPARK flow analysis for data dependencies

   --  Error codes for cryptographic operations
   type Crypto_Result is (
      Success,           --  Operation completed successfully
      Invalid_Key,       --  Key is malformed or wrong size
      Invalid_Input,     --  Input data is malformed
      Invalid_Tag,       --  Authentication tag verification failed
      Buffer_Too_Small,  --  Output buffer insufficient
      Verification_Failed --  Signature or proof verification failed
   );

   --  Predicate for success
   function Is_Success (R : Crypto_Result) return Boolean is (R = Success);

end Teras.Crypto;
