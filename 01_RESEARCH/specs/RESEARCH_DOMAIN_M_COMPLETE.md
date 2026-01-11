# TERAS-LANG Research Domain M: Testing and Quality Assurance

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-M-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | M-01 through M-10 |
| Domain | M: Testing and Quality Assurance |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# M-01: Testing Foundations

## Executive Summary

Testing in security-critical systems must go beyond functional correctness to verify security properties, handle adversarial inputs, and validate cryptographic implementations. TERAS-LANG requires a comprehensive testing framework integrated with the type system.

## Testing Pyramid

```
                    /\
                   /  \
                  / E2E\           End-to-End Tests
                 /______\          (Full system)
                /        \
               /Integration\       Integration Tests
              /______________\     (Component interaction)
             /                \
            /    Unit Tests    \   Unit Tests
           /____________________\  (Individual functions)
          /                      \
         /    Property Tests      \ Property-Based Tests
        /__________________________\ (Invariants)
       /                            \
      /      Type System Checks      \ Static Verification
     /________________________________\ (Compile-time)
```

## Security Testing Categories

```
1. Functional Security
   - Authentication flows
   - Authorization checks
   - Access control

2. Cryptographic
   - Algorithm correctness
   - Key management
   - Side-channel resistance

3. Input Validation
   - Boundary conditions
   - Malformed inputs
   - Injection attempts

4. Concurrency
   - Race conditions
   - Deadlocks
   - Timing attacks

5. Resource
   - Memory leaks
   - Resource exhaustion
   - DoS resistance
```

## TERAS Testing Philosophy

```
1. Type System as First Line
   - Many properties verified at compile time
   - Reduces runtime test burden

2. Property-Based Testing
   - Verify invariants hold for all inputs
   - Generate adversarial inputs

3. Mutation Testing
   - Ensure tests catch real bugs
   - Verify test quality

4. Coverage Requirements
   - Code coverage
   - Branch coverage
   - Security property coverage
```

## TERAS Decision M-01

**IMPLEMENT** testing framework:
1. Integrated with type system
2. Property-based testing
3. Security-focused assertions
4. Comprehensive coverage

### Architecture Decision ID: `TERAS-ARCH-M01-TEST-001`

---

# M-02: Unit Testing

## Test Definition

```rust
// Basic test
#[test]
fn test_addition() {
    assert_eq!(2 + 2, 4);
}

// Test with setup
#[test]
fn test_encryption() {
    let key = AesKey::generate();
    let plaintext = b"Hello, World!";
    
    let ciphertext = encrypt(&key, plaintext);
    let decrypted = decrypt(&key, &ciphertext).unwrap();
    
    assert_eq!(plaintext, decrypted.as_slice());
}

// Expected panic
#[test]
#[should_panic(expected = "division by zero")]
fn test_divide_by_zero() {
    divide(1, 0);
}

// Result-returning test
#[test]
fn test_file_read() -> Result<(), Error> {
    let content = read_file("test.txt")?;
    assert!(!content.is_empty());
    Ok(())
}
```

## Test Organization

```rust
// Module tests
mod encryption {
    #[cfg(test)]
    mod tests {
        use super::*;
        
        #[test]
        fn test_aes_roundtrip() { ... }
        
        #[test]
        fn test_aes_wrong_key() { ... }
    }
}

// Test fixtures
struct TestContext {
    key: AesKey,
    temp_dir: TempDir,
}

impl TestContext {
    fn new() -> Self {
        TestContext {
            key: AesKey::generate(),
            temp_dir: TempDir::new().unwrap(),
        }
    }
}

impl Drop for TestContext {
    fn drop(&mut self) {
        // Cleanup
    }
}

#[test]
fn test_with_context() {
    let ctx = TestContext::new();
    // Use ctx...
}
```

## Security Unit Tests

```rust
// Test authentication
#[test]
fn test_auth_valid_credentials() {
    let user = create_test_user("alice", "password123");
    let result = authenticate("alice", "password123");
    assert!(result.is_ok());
}

#[test]
fn test_auth_invalid_password() {
    let user = create_test_user("alice", "password123");
    let result = authenticate("alice", "wrongpassword");
    assert!(matches!(result, Err(AuthError::InvalidCredentials)));
}

#[test]
fn test_auth_timing() {
    // Verify constant-time comparison
    let start1 = Instant::now();
    authenticate("alice", "password123");
    let duration1 = start1.elapsed();
    
    let start2 = Instant::now();
    authenticate("alice", "x");  // Very short password
    let duration2 = start2.elapsed();
    
    // Should be approximately equal (within tolerance)
    let diff = (duration1.as_nanos() as i64 - duration2.as_nanos() as i64).abs();
    assert!(diff < 1_000_000, "Timing difference too large: {}ns", diff);
}
```

## TERAS Decision M-02

**IMPLEMENT** unit testing:
1. #[test] attribute
2. Assertions library
3. Test fixtures
4. Security-specific tests

### Architecture Decision ID: `TERAS-ARCH-M02-UNIT-001`

---

# M-03: Property-Based Testing

## QuickCheck Style

```rust
use proptest::prelude::*;

// Property: encryption is reversible
proptest! {
    #[test]
    fn encryption_roundtrip(
        key in any::<[u8; 32]>(),
        plaintext in any::<Vec<u8>>(),
    ) {
        let key = AesKey::from_bytes(&key);
        let nonce = generate_nonce();
        
        let ciphertext = encrypt(&key, &nonce, &plaintext);
        let decrypted = decrypt(&key, &nonce, &ciphertext).unwrap();
        
        prop_assert_eq!(plaintext, decrypted);
    }
}

// Property: hash is deterministic
proptest! {
    #[test]
    fn hash_deterministic(data in any::<Vec<u8>>()) {
        let hash1 = sha256(&data);
        let hash2 = sha256(&data);
        prop_assert_eq!(hash1, hash2);
    }
}

// Property: signatures verify
proptest! {
    #[test]
    fn signature_verifies(
        seed in any::<[u8; 32]>(),
        message in any::<Vec<u8>>(),
    ) {
        let (pk, sk) = generate_keypair_from_seed(&seed);
        let sig = sign(&sk, &message);
        prop_assert!(verify(&pk, &message, &sig));
    }
}
```

## Custom Generators

```rust
// Generate valid email
fn email_strategy() -> impl Strategy<Value = String> {
    (
        "[a-z]{1,10}",
        "[a-z]{1,10}",
        prop_oneof!["com", "org", "net"],
    ).prop_map(|(user, domain, tld)| format!("{}@{}.{}", user, domain, tld))
}

// Generate valid IP address
fn ipv4_strategy() -> impl Strategy<Value = IpAddr> {
    (0u8..=255, 0u8..=255, 0u8..=255, 0u8..=255)
        .prop_map(|(a, b, c, d)| IpAddr::V4(Ipv4Addr::new(a, b, c, d)))
}

// Generate adversarial input
fn malicious_string_strategy() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("'; DROP TABLE users; --".to_string()),
        Just("<script>alert('xss')</script>".to_string()),
        Just("../../../etc/passwd".to_string()),
        Just("\0\0\0".to_string()),
        Just("A".repeat(10000)),
    ]
}

proptest! {
    #[test]
    fn sanitize_handles_malicious(input in malicious_string_strategy()) {
        let sanitized = sanitize(&input);
        prop_assert!(!sanitized.contains("DROP TABLE"));
        prop_assert!(!sanitized.contains("<script>"));
        prop_assert!(!sanitized.contains("../"));
    }
}
```

## Security Properties

```rust
// Property: authorization is consistent
proptest! {
    #[test]
    fn authz_consistent(
        user in user_strategy(),
        resource in resource_strategy(),
        action in action_strategy(),
    ) {
        let result1 = check_authorization(&user, &resource, &action);
        let result2 = check_authorization(&user, &resource, &action);
        prop_assert_eq!(result1, result2);
    }
}

// Property: no information leakage via error messages
proptest! {
    #[test]
    fn error_no_leakage(input in any::<String>()) {
        let result = process_input(&input);
        if let Err(e) = result {
            let message = e.to_string();
            prop_assert!(!message.contains(&input), 
                "Error message contains user input");
        }
    }
}

// Property: rate limiting works
proptest! {
    #[test]
    fn rate_limit_enforced(
        requests in 1usize..1000,
        limit in 10usize..100,
    ) {
        let limiter = RateLimiter::new(limit);
        let mut allowed = 0;
        
        for _ in 0..requests {
            if limiter.check() {
                allowed += 1;
            }
        }
        
        prop_assert!(allowed <= limit);
    }
}
```

## TERAS Decision M-03

**IMPLEMENT** property testing:
1. Proptest integration
2. Custom generators
3. Security property tests
4. Shrinking for minimal counterexamples

### Architecture Decision ID: `TERAS-ARCH-M03-PROP-001`

---

# M-04: Fuzzing

## Fuzzing Framework

```rust
// Cargo-fuzz / libFuzzer integration
#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    // Fuzz target: parser
    let _ = parse_message(data);
});

// Structured fuzzing with arbitrary
use arbitrary::Arbitrary;

#[derive(Arbitrary, Debug)]
struct FuzzInput {
    header: Header,
    body: Vec<u8>,
    flags: u32,
}

fuzz_target!(|input: FuzzInput| {
    let _ = process_request(input.header, &input.body, input.flags);
});
```

## Coverage-Guided Fuzzing

```rust
// AFL-style fuzzing
// Compile with: cargo afl build
// Run with: cargo afl fuzz -i seeds -o findings target/debug/fuzz_target

fn main() {
    afl::fuzz!(|data: &[u8]| {
        let _ = parse_certificate(data);
    });
}

// Seed corpus
// seeds/
//   valid_cert.der
//   self_signed.der
//   expired.der
```

## Security Fuzzing

```rust
// Fuzz cryptographic parsing
fuzz_target!(|data: &[u8]| {
    // Should never panic
    let _ = parse_public_key(data);
    let _ = parse_signature(data);
    let _ = parse_certificate(data);
});

// Fuzz with sanitizers
// RUSTFLAGS="-Z sanitizer=address" cargo fuzz run fuzz_target
// RUSTFLAGS="-Z sanitizer=memory" cargo fuzz run fuzz_target

// Differential fuzzing
fuzz_target!(|data: &[u8]| {
    let result1 = our_parser(data);
    let result2 = reference_parser(data);
    
    match (result1, result2) {
        (Ok(a), Ok(b)) => assert_eq!(a, b),
        (Err(_), Err(_)) => {}  // Both error is fine
        _ => panic!("Parser disagreement on input: {:?}", data),
    }
});
```

## TERAS Fuzzing Targets

```rust
// GAPURA: HTTP parsing
fuzz_target!(|data: &[u8]| {
    let _ = parse_http_request(data);
});

// ZIRAH: File format parsing
fuzz_target!(|data: &[u8]| {
    let _ = parse_pe_header(data);
    let _ = parse_elf_header(data);
    let _ = parse_macho_header(data);
});

// BENTENG: Document parsing
fuzz_target!(|data: &[u8]| {
    let _ = parse_mykad_mrz(data);
    let _ = parse_passport_mrz(data);
});

// SANDI: Certificate parsing
fuzz_target!(|data: &[u8]| {
    let _ = parse_x509_certificate(data);
    let _ = parse_pkcs7_signature(data);
});
```

## TERAS Decision M-04

**IMPLEMENT** fuzzing:
1. libFuzzer integration
2. Coverage-guided
3. Structured fuzzing
4. Differential fuzzing

### Architecture Decision ID: `TERAS-ARCH-M04-FUZZ-001`

---

# M-05: Integration Testing

## Component Integration

```rust
// tests/integration/auth_test.rs
use teras::auth::*;
use teras::database::*;
use teras::audit::*;

#[test]
fn test_full_auth_flow() {
    // Setup
    let db = TestDatabase::new();
    let audit = TestAuditLog::new();
    let auth = AuthService::new(&db, &audit);
    
    // Create user
    let user = auth.create_user("alice", "password123").unwrap();
    
    // Login
    let session = auth.login("alice", "password123").unwrap();
    assert!(session.is_valid());
    
    // Verify audit
    let events = audit.get_events();
    assert!(events.iter().any(|e| matches!(e, AuditEvent::UserCreated { .. })));
    assert!(events.iter().any(|e| matches!(e, AuditEvent::LoginSuccess { .. })));
    
    // Logout
    auth.logout(&session).unwrap();
    assert!(!session.is_valid());
}

#[test]
fn test_auth_with_mfa() {
    let db = TestDatabase::new();
    let mfa = TestMfaProvider::new();
    let auth = AuthService::new(&db).with_mfa(&mfa);
    
    // Create user with MFA
    let user = auth.create_user("bob", "password123").unwrap();
    auth.enable_mfa(&user, MfaType::Totp).unwrap();
    
    // Login requires MFA
    let result = auth.login("bob", "password123");
    assert!(matches!(result, Err(AuthError::MfaRequired)));
    
    // Login with MFA
    let code = mfa.generate_code(&user);
    let session = auth.login_with_mfa("bob", "password123", &code).unwrap();
    assert!(session.is_valid());
}
```

## API Integration

```rust
#[tokio::test]
async fn test_api_authentication() {
    let app = TestApp::spawn().await;
    
    // Register
    let response = app.post("/api/register")
        .json(&json!({
            "username": "alice",
            "email": "alice@example.com",
            "password": "SecurePass123!"
        }))
        .send()
        .await;
    assert_eq!(response.status(), 201);
    
    // Login
    let response = app.post("/api/login")
        .json(&json!({
            "username": "alice",
            "password": "SecurePass123!"
        }))
        .send()
        .await;
    assert_eq!(response.status(), 200);
    
    let token: TokenResponse = response.json().await;
    
    // Access protected resource
    let response = app.get("/api/profile")
        .bearer_auth(&token.access_token)
        .send()
        .await;
    assert_eq!(response.status(), 200);
}
```

## Security Integration Tests

```rust
#[test]
fn test_authorization_chain() {
    let system = TestSystem::new();
    
    // Create hierarchy
    let admin = system.create_user("admin", Role::Admin);
    let manager = system.create_user("manager", Role::Manager);
    let user = system.create_user("user", Role::User);
    
    let resource = system.create_resource("secret_doc", Classification::Secret);
    
    // Test access
    assert!(system.can_access(&admin, &resource, Action::Read));
    assert!(system.can_access(&admin, &resource, Action::Write));
    
    assert!(system.can_access(&manager, &resource, Action::Read));
    assert!(!system.can_access(&manager, &resource, Action::Write));
    
    assert!(!system.can_access(&user, &resource, Action::Read));
    assert!(!system.can_access(&user, &resource, Action::Write));
}

#[test]
fn test_audit_trail_integrity() {
    let system = TestSystem::new();
    
    // Perform operations
    system.authenticate("alice", "password");
    system.access_resource("doc1");
    system.modify_resource("doc1", "new content");
    
    // Verify audit trail
    let audit_log = system.get_audit_log();
    
    // Verify chain integrity
    for i in 1..audit_log.len() {
        let prev_hash = audit_log[i - 1].hash();
        assert_eq!(audit_log[i].prev_hash, prev_hash);
    }
    
    // Verify no tampering
    assert!(audit_log.verify_integrity());
}
```

## TERAS Decision M-05

**IMPLEMENT** integration testing:
1. Component integration
2. API testing
3. Security flow tests
4. Audit verification

### Architecture Decision ID: `TERAS-ARCH-M05-INT-001`

---

# M-06: Mutation Testing

## Mutation Testing Concepts

```
Mutation Testing:
    1. Inject small bugs (mutations) into code
    2. Run test suite
    3. Check if tests detect mutations
    
Mutation Operators:
    - Arithmetic: + â†’ -, * â†’ /
    - Relational: < â†’ <=, == â†’ !=
    - Logical: && â†’ ||, ! removed
    - Statement: delete statement
    - Return: change return value
    
Mutation Score = Killed Mutations / Total Mutations
```

## Mutation Examples

```rust
// Original code
fn check_age(age: u32) -> bool {
    age >= 18
}

// Mutations:
fn check_age_mut1(age: u32) -> bool {
    age > 18  // >= â†’ >
}

fn check_age_mut2(age: u32) -> bool {
    age >= 17  // 18 â†’ 17
}

fn check_age_mut3(age: u32) -> bool {
    age <= 18  // >= â†’ <=
}

// Test that kills all mutations
#[test]
fn test_check_age() {
    assert!(!check_age(17));  // Kills mut1, mut2
    assert!(check_age(18));   // Kills mut3
    assert!(check_age(19));   // Sanity check
}
```

## Security Mutation Testing

```rust
// Security-critical mutations
// Original
fn verify_signature(pk: &PublicKey, msg: &[u8], sig: &Signature) -> bool {
    let computed = compute_signature(pk, msg);
    constant_time_compare(&computed, sig)
}

// Security mutations to detect:
// 1. Remove verification entirely
fn verify_signature_mut1(...) -> bool {
    true  // Always succeeds!
}

// 2. Use non-constant-time compare
fn verify_signature_mut2(...) -> bool {
    computed == sig  // Timing attack!
}

// 3. Wrong computation
fn verify_signature_mut3(...) -> bool {
    constant_time_compare(&[0; 64], sig)  // Wrong data!
}

// Tests must catch ALL of these
#[test]
fn test_verify_signature_valid() {
    let (pk, sk) = generate_keypair();
    let msg = b"test message";
    let sig = sign(&sk, msg);
    assert!(verify_signature(&pk, msg, &sig));
}

#[test]
fn test_verify_signature_invalid() {
    let (pk, _) = generate_keypair();
    let msg = b"test message";
    let bad_sig = Signature::from_bytes(&[0; 64]);
    assert!(!verify_signature(&pk, msg, &bad_sig));  // Catches mut1, mut3
}

#[test]
fn test_verify_signature_wrong_message() {
    let (pk, sk) = generate_keypair();
    let msg = b"test message";
    let sig = sign(&sk, msg);
    assert!(!verify_signature(&pk, b"other message", &sig));
}
```

## TERAS Mutation Requirements

```rust
// Security-critical functions require 100% mutation score
#[mutation_coverage(100)]
fn authenticate(username: &str, password: &str) -> Result<Session, AuthError> {
    // ...
}

// Cryptographic functions
#[mutation_coverage(100)]
fn encrypt(key: &Key, data: &[u8]) -> Vec<u8> {
    // ...
}

// Access control
#[mutation_coverage(100)]
fn check_permission(user: &User, resource: &Resource, action: Action) -> bool {
    // ...
}
```

## TERAS Decision M-06

**IMPLEMENT** mutation testing:
1. Standard mutation operators
2. Security-specific mutations
3. Coverage requirements
4. CI integration

### Architecture Decision ID: `TERAS-ARCH-M06-MUT-001`

---

# M-07: Performance Testing

## Benchmarking

```rust
use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};

fn bench_encryption(c: &mut Criterion) {
    let key = AesKey::generate();
    let nonce = generate_nonce();
    
    let mut group = c.benchmark_group("AES-256-GCM");
    
    for size in [64, 256, 1024, 4096, 16384].iter() {
        let data = vec![0u8; *size];
        
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, _| {
                b.iter(|| encrypt(&key, &nonce, &data));
            },
        );
    }
    
    group.finish();
}

fn bench_hash(c: &mut Criterion) {
    let mut group = c.benchmark_group("SHA-256");
    
    for size in [64, 256, 1024, 4096].iter() {
        let data = vec![0u8; *size];
        
        group.throughput(Throughput::Bytes(*size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            &data,
            |b, data| {
                b.iter(|| sha256(data));
            },
        );
    }
    
    group.finish();
}

criterion_group!(benches, bench_encryption, bench_hash);
criterion_main!(benches);
```

## Load Testing

```rust
#[tokio::test]
async fn load_test_api() {
    let app = TestApp::spawn().await;
    let client = reqwest::Client::new();
    
    let start = Instant::now();
    let mut handles = vec![];
    
    // 1000 concurrent requests
    for _ in 0..1000 {
        let client = client.clone();
        let url = app.url("/api/health");
        
        handles.push(tokio::spawn(async move {
            client.get(&url).send().await
        }));
    }
    
    let mut success = 0;
    let mut failure = 0;
    
    for handle in handles {
        match handle.await.unwrap() {
            Ok(resp) if resp.status().is_success() => success += 1,
            _ => failure += 1,
        }
    }
    
    let duration = start.elapsed();
    let rps = 1000.0 / duration.as_secs_f64();
    
    println!("Requests per second: {:.2}", rps);
    println!("Success: {}, Failure: {}", success, failure);
    
    assert!(success >= 990, "Too many failures");
    assert!(rps >= 100.0, "RPS too low");
}
```

## Security Performance

```rust
// Constant-time verification
#[test]
fn test_constant_time_compare() {
    let secret = [0u8; 32];
    
    // Measure time for matching comparison
    let matching = [0u8; 32];
    let start = Instant::now();
    for _ in 0..10000 {
        constant_time_compare(&secret, &matching);
    }
    let match_time = start.elapsed();
    
    // Measure time for non-matching (early difference)
    let mut non_matching = [0u8; 32];
    non_matching[0] = 1;
    let start = Instant::now();
    for _ in 0..10000 {
        constant_time_compare(&secret, &non_matching);
    }
    let non_match_time = start.elapsed();
    
    // Times should be within 5%
    let ratio = match_time.as_nanos() as f64 / non_match_time.as_nanos() as f64;
    assert!((0.95..=1.05).contains(&ratio), 
        "Timing variance too high: {}", ratio);
}
```

## TERAS Decision M-07

**IMPLEMENT** performance testing:
1. Criterion benchmarks
2. Load testing
3. Constant-time verification
4. Performance regression CI

### Architecture Decision ID: `TERAS-ARCH-M07-PERF-001`

---

# M-08: Security Testing

## Penetration Testing Support

```rust
// Test harness for security testing
pub struct SecurityTestHarness {
    app: TestApp,
    attacker: AttackerContext,
}

impl SecurityTestHarness {
    // SQL Injection tests
    pub fn test_sql_injection(&self, endpoint: &str, param: &str) -> Vec<Finding> {
        let payloads = [
            "' OR '1'='1",
            "'; DROP TABLE users; --",
            "1; SELECT * FROM users",
            "' UNION SELECT password FROM users --",
        ];
        
        let mut findings = vec![];
        for payload in &payloads {
            let response = self.app.get(endpoint)
                .query(&[(param, payload)])
                .send();
            
            if self.indicates_sqli(&response) {
                findings.push(Finding::SqlInjection {
                    endpoint: endpoint.to_string(),
                    payload: payload.to_string(),
                });
            }
        }
        findings
    }
    
    // XSS tests
    pub fn test_xss(&self, endpoint: &str, param: &str) -> Vec<Finding> {
        let payloads = [
            "<script>alert('xss')</script>",
            "<img src=x onerror=alert('xss')>",
            "javascript:alert('xss')",
        ];
        
        let mut findings = vec![];
        for payload in &payloads {
            let response = self.app.post(endpoint)
                .form(&[(param, payload)])
                .send();
            
            if response.text().contains(payload) {
                findings.push(Finding::Xss {
                    endpoint: endpoint.to_string(),
                    payload: payload.to_string(),
                });
            }
        }
        findings
    }
}
```

## Authentication Testing

```rust
#[test]
fn test_brute_force_protection() {
    let app = TestApp::spawn();
    
    // Attempt many failed logins
    for i in 0..20 {
        let result = app.login("alice", &format!("wrong{}", i));
        
        if i >= 5 {
            // Should be rate limited after 5 attempts
            assert!(matches!(result, Err(AuthError::RateLimited)));
        }
    }
}

#[test]
fn test_session_fixation() {
    let app = TestApp::spawn();
    
    // Get initial session
    let initial_session = app.get_session();
    
    // Login
    app.login("alice", "password123").unwrap();
    
    // Session should change after login
    let post_login_session = app.get_session();
    assert_ne!(initial_session, post_login_session, 
        "Session fixation vulnerability: session not regenerated");
}

#[test]
fn test_password_in_logs() {
    let app = TestApp::spawn();
    
    // Attempt login
    app.login("alice", "SuperSecretPassword123!").unwrap();
    
    // Check logs don't contain password
    let logs = app.get_logs();
    assert!(!logs.contains("SuperSecretPassword123!"),
        "Password appears in logs!");
}
```

## Cryptographic Testing

```rust
// Known Answer Tests (KAT)
#[test]
fn test_aes_kat() {
    // NIST test vectors
    let key = hex!("000102030405060708090a0b0c0d0e0f");
    let plaintext = hex!("00112233445566778899aabbccddeeff");
    let expected = hex!("69c4e0d86a7b0430d8cdb78070b4c55a");
    
    let result = aes_encrypt(&key, &plaintext);
    assert_eq!(result, expected);
}

// Monte Carlo Tests
#[test]
fn test_aes_monte_carlo() {
    let mut key = [0u8; 16];
    let mut pt = [0u8; 16];
    
    for _ in 0..100 {
        let ct = aes_encrypt(&key, &pt);
        pt = ct;
        for i in 0..16 {
            key[i] ^= ct[i];
        }
    }
    
    // Verify against known result
    let expected = hex!("..."); // Known result after 100 iterations
    assert_eq!(pt, expected);
}
```

## TERAS Decision M-08

**IMPLEMENT** security testing:
1. Penetration test harness
2. Authentication tests
3. Cryptographic KATs
4. Vulnerability scanning

### Architecture Decision ID: `TERAS-ARCH-M08-SEC-001`

---

# M-09: Test Coverage

## Coverage Metrics

```rust
// Code coverage
// Run with: cargo tarpaulin --out Html

// Branch coverage
#[test]
fn test_all_branches() {
    // Test true branch
    assert!(check_condition(true));
    
    // Test false branch
    assert!(!check_condition(false));
}

// Coverage requirements
#[coverage(min = 90)]
mod critical_module {
    // Must have 90%+ coverage
}

#[coverage(min = 100)]
mod security_module {
    // Must have 100% coverage
}
```

## Security Property Coverage

```rust
// Define security properties
enum SecurityProperty {
    Authentication,
    Authorization,
    Confidentiality,
    Integrity,
    Availability,
    NonRepudiation,
}

// Track which properties are tested
#[derive(Default)]
struct SecurityCoverage {
    properties: HashSet<SecurityProperty>,
}

impl SecurityCoverage {
    fn mark_tested(&mut self, prop: SecurityProperty) {
        self.properties.insert(prop);
    }
    
    fn verify_complete(&self) {
        let required = [
            SecurityProperty::Authentication,
            SecurityProperty::Authorization,
            SecurityProperty::Confidentiality,
            SecurityProperty::Integrity,
        ];
        
        for prop in &required {
            assert!(self.properties.contains(prop),
                "Missing test coverage for {:?}", prop);
        }
    }
}

#[test]
fn test_security_coverage() {
    let mut coverage = SecurityCoverage::default();
    
    // Test authentication
    test_authentication();
    coverage.mark_tested(SecurityProperty::Authentication);
    
    // Test authorization
    test_authorization();
    coverage.mark_tested(SecurityProperty::Authorization);
    
    // ... more tests
    
    coverage.verify_complete();
}
```

## Coverage Reports

```rust
// Generate coverage report
// cargo tarpaulin --out Html --output-dir coverage

// CI integration
// .github/workflows/coverage.yml
/*
- name: Run coverage
  run: cargo tarpaulin --out Xml
  
- name: Upload coverage
  uses: codecov/codecov-action@v3
  
- name: Check coverage threshold
  run: |
    COVERAGE=$(cargo tarpaulin --out Json | jq '.coverage')
    if (( $(echo "$COVERAGE < 80" | bc -l) )); then
      echo "Coverage below threshold: $COVERAGE%"
      exit 1
    fi
*/
```

## TERAS Decision M-09

**IMPLEMENT** coverage:
1. Line/branch coverage
2. Security property coverage
3. Coverage thresholds
4. CI enforcement

### Architecture Decision ID: `TERAS-ARCH-M09-COV-001`

---

# M-10: Testing in TERAS Products

## MENARA Testing

```rust
// Mobile security testing
mod menara_tests {
    #[test]
    fn test_app_scan() {
        let app = TestApp::malicious_sample();
        let result = scan_app(&app);
        assert_eq!(result.threat_level, ThreatLevel::High);
        assert!(result.indicators.contains(&Indicator::MaliciousCode));
    }
    
    #[test]
    fn test_network_interception_detection() {
        let mock_network = MockNetwork::with_mitm();
        let detector = NetworkMonitor::new(&mock_network);
        
        let threats = detector.detect_threats();
        assert!(threats.iter().any(|t| matches!(t, Threat::MitmAttack)));
    }
    
    #[test]
    fn test_permission_analysis() {
        let manifest = AndroidManifest::from_file("test_data/suspicious_manifest.xml");
        let analysis = analyze_permissions(&manifest);
        
        assert!(analysis.has_dangerous_combination());
        assert!(analysis.risks.contains(&Risk::SmsInterception));
    }
}
```

## GAPURA Testing

```rust
// WAF testing
mod gapura_tests {
    #[test]
    fn test_sql_injection_detection() {
        let waf = Gapura::new(default_rules());
        
        let malicious_requests = [
            "SELECT * FROM users",
            "1' OR '1'='1",
            "'; DROP TABLE users; --",
        ];
        
        for payload in &malicious_requests {
            let request = Request::get("/api/search").query("q", payload);
            let decision = waf.check(&request);
            assert!(matches!(decision, Decision::Block(_)));
        }
    }
    
    #[test]
    fn test_rate_limiting() {
        let waf = Gapura::new(RateLimit::new(100, Duration::from_secs(60)));
        let client_ip = "192.168.1.1".parse().unwrap();
        
        for i in 0..150 {
            let request = Request::get("/api/resource").from_ip(client_ip);
            let decision = waf.check(&request);
            
            if i < 100 {
                assert!(matches!(decision, Decision::Allow));
            } else {
                assert!(matches!(decision, Decision::RateLimit));
            }
        }
    }
}
```

## ZIRAH Testing

```rust
// EDR testing
mod zirah_tests {
    #[test]
    fn test_malware_detection() {
        let scanner = ZirahScanner::new();
        
        let samples = [
            ("eicar.com", ThreatType::TestFile),
            ("wannacry.exe", ThreatType::Ransomware),
            ("mimikatz.exe", ThreatType::HackTool),
        ];
        
        for (file, expected_type) in &samples {
            let result = scanner.scan_file(&format!("test_samples/{}", file));
            assert!(result.is_threat);
            assert_eq!(result.threat_type, *expected_type);
        }
    }
    
    #[test]
    fn test_behavioral_detection() {
        let monitor = BehaviorMonitor::new();
        
        // Simulate ransomware behavior
        let process = MockProcess::new();
        process.rapid_file_encryption(100);
        
        let alerts = monitor.check(&process);
        assert!(alerts.iter().any(|a| matches!(a, Alert::RansomwareBehavior)));
    }
}
```

## BENTENG Testing

```rust
// eKYC testing
mod benteng_tests {
    #[test]
    fn test_face_matching() {
        let verifier = FaceVerifier::new();
        
        // Same person
        let selfie = load_image("test_data/alice_selfie.jpg");
        let document = load_image("test_data/alice_mykad.jpg");
        let result = verifier.compare(&selfie, &document);
        assert!(result.match_score > 0.9);
        
        // Different person
        let bob_selfie = load_image("test_data/bob_selfie.jpg");
        let result = verifier.compare(&bob_selfie, &document);
        assert!(result.match_score < 0.5);
    }
    
    #[test]
    fn test_liveness_detection() {
        let detector = LivenessDetector::new();
        
        // Real video
        let real_video = load_video("test_data/real_liveness.mp4");
        assert!(detector.check(&real_video).is_live);
        
        // Printed photo attack
        let photo_attack = load_video("test_data/photo_attack.mp4");
        assert!(!detector.check(&photo_attack).is_live);
    }
    
    #[test]
    fn test_document_ocr() {
        let ocr = DocumentOcr::new();
        
        let mykad = load_image("test_data/sample_mykad.jpg");
        let result = ocr.extract(&mykad);
        
        assert_eq!(result.ic_number, "880101-14-5555");
        assert_eq!(result.name, "AHMAD BIN ABDULLAH");
    }
}
```

## SANDI Testing

```rust
// Digital signature testing
mod sandi_tests {
    #[test]
    fn test_signature_creation() {
        let key_pair = generate_keypair();
        let document = b"Important contract content";
        
        let signature = sign(&key_pair.private, document);
        assert!(verify(&key_pair.public, document, &signature));
    }
    
    #[test]
    fn test_timestamp_verification() {
        let tsa = TestTsaServer::new();
        let signature = create_timestamped_signature(&tsa);
        
        let verification = verify_timestamp(&signature);
        assert!(verification.is_valid);
        assert!(verification.timestamp.is_some());
    }
    
    #[test]
    fn test_certificate_chain() {
        let chain = CertificateChain::from_file("test_data/chain.pem");
        let verification = chain.verify();
        
        assert!(verification.is_valid);
        assert_eq!(verification.chain_length, 3);
    }
}
```

## TERAS Decision M-10

**IMPLEMENT** product testing:
1. Product-specific test suites
2. Sample-based testing
3. Integration with CI
4. Security test automation

### Architecture Decision ID: `TERAS-ARCH-M10-PROD-001`

---

# Domain M Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| M-01 | Foundations | TERAS-ARCH-M01-TEST-001 |
| M-02 | Unit Testing | TERAS-ARCH-M02-UNIT-001 |
| M-03 | Property Testing | TERAS-ARCH-M03-PROP-001 |
| M-04 | Fuzzing | TERAS-ARCH-M04-FUZZ-001 |
| M-05 | Integration | TERAS-ARCH-M05-INT-001 |
| M-06 | Mutation | TERAS-ARCH-M06-MUT-001 |
| M-07 | Performance | TERAS-ARCH-M07-PERF-001 |
| M-08 | Security | TERAS-ARCH-M08-SEC-001 |
| M-09 | Coverage | TERAS-ARCH-M09-COV-001 |
| M-10 | Products | TERAS-ARCH-M10-PROD-001 |

## Domain M: COMPLETE

---

*Research Track Output â€” Domain M: Testing and Quality Assurance*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
