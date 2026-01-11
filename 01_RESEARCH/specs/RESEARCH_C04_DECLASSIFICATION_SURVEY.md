# TERAS-LANG Research Survey C-04: Declassification and Endorsement

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-C04-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | C-04 |
| Domain | C: Information Flow Control |
| Author | Claude (Anthropic) |
| Classification | TERAS Internal |
| Status | Complete |

---

## Executive Summary

Strict noninterference is too restrictive for practical systems. Declassification (releasing confidential information) and endorsement (trusting untrusted data) provide controlled relaxation. This survey covers policies, mechanisms, and safety properties for intentional information release in TERAS.

---

## Part 1: The Need for Relaxation

### 1.1 Strict Noninterference Limitations

```
Problems with strict noninterference:

1. Password checking
   hash(input) == stored_hash  
   // Result reveals something about password!

2. Statistical queries
   count(salary > 100000)
   // Reveals aggregate info about salaries

3. Access control decisions
   if authorized(user) then show(data)
   // Decision reveals authorization status

4. Encryption
   encrypt(secret, key)
   // Ciphertext derived from secret

All useful systems "leak" something intentionally.
```

### 1.2 Controlled Release

```
Declassification: Intentional confidentiality relaxation
    Secret â†’ Public (under policy)

Endorsement: Intentional integrity upgrade
    Untrusted â†’ Trusted (under policy)

Key insight: Not all leaks are bad
             Must distinguish intentional from accidental
```

---

## Part 2: Declassification Dimensions

### 2.1 The Four Dimensions (Sabelfeld & Sands)

```
What: What information is released?
Who:  Who can release it?
When: Under what conditions?
Where: At what program points?

Each dimension has associated policies and mechanisms.
```

### 2.2 What: Information Released

```
Mechanisms:

1. Selective declassification
   declassify(secret, {salary_range})
   // Release only the range, not exact value

2. Aggregate declassification
   declassify(avg(salaries))
   // Release aggregate, not individuals

3. Sanitized declassification
   declassify(hash(password))
   // Release derived value

4. Partial declassification
   declassify(first_name)
   // Release subset of record
```

### 2.3 Who: Authority

```
Principal-based control:

1. Owner-based (DLM)
   if acts_for(current, data.owner) then
       declassify(data)
   // Only owner can release

2. Role-based
   if current.has_role(DataSteward) then
       declassify(data)
   // Specific role required

3. Capability-based
   fn release(cap: DeclassifyCap, data) {
       // Capability token authorizes
       declassify(data)
   }
```

### 2.4 When: Conditions

```
Condition-based declassification:

1. Temporal
   if time > embargo_date then
       declassify(data)
   // Release after embargo

2. Aggregation threshold
   if count(contributors) >= k then
       declassify(aggregate)
   // k-anonymity style

3. User consent
   if user.consented(data_use) then
       declassify(user_data)
   // Consent-based

4. Approval workflow
   if approved_by(manager) && approved_by(security) then
       declassify(data)
```

### 2.5 Where: Program Points

```
Location-based policies:

1. Trusted code blocks
   trusted {
       // Declassification allowed here
       declassify(secret)
   }

2. Designated functions
   #[allows_declassify]
   fn password_check(input, stored) -> bool {
       hash(input) == stored
   }

3. Module boundaries
   // Only security_module can declassify
   mod security_module {
       pub fn release(x) { declassify(x) }
   }
```

---

## Part 3: Robust Declassification

### 3.1 Attacker Model

```
Threat: Attacker controls low-integrity code

Attack scenario:
    fn attacker_code() {
        // Can we trick system into declassifying?
        let what = attacker_chosen()
        declassify(what)  // Attack!
    }

Defense: Robust declassification
    - Only high-integrity code can declassify
    - Attacker cannot influence what is released
```

### 3.2 Robustness Definition

```
Robust Declassification (Zdancewic & Myers):

A system has robust declassification if:
    - Changes to low-integrity inputs
    - Cannot affect what is declassified

Formally:
    âˆ€ lowâ‚, lowâ‚‚:
        declassified(P(high, lowâ‚)) = declassified(P(high, lowâ‚‚))
```

### 3.3 Achieving Robustness

```
Implementation requirements:

1. Declassification requires high integrity
   fn declassify<L>(x: T @ (L, High)) -> T @ (Lower, High)
                           ^^^^^^^^^
                           Must be trusted

2. What is declassified independent of low
   fn robust_password_check(
       input: String @ (_, Low),   // Untrusted
       hash: Hash @ (Secret, High) // Trusted
   ) -> bool @ (_, High) {
       // Compare fixed number of bytes (constant time)
       constant_time_compare(hash(input), hash)
   }
```

---

## Part 4: Endorsement

### 4.1 Integrity Upgrade

```
Endorsement: Marking untrusted data as trusted

input: String @ Untrusted
validated = validate(input)
trusted_input: String @ Trusted = endorse(validated)
                                  ^^^^^^^
                                  Integrity upgrade

Requirements:
    - Validation must precede endorsement
    - Validation must be thorough
    - Trusted code performs endorsement
```

### 4.2 Validation Patterns

```
Common validation endorsement patterns:

1. Input sanitization
   fn sanitize_html(input: String @ Untrusted) -> String @ Trusted {
       let cleaned = remove_scripts(input)
       endorse(cleaned)
   }

2. Type parsing
   fn parse_int(input: String @ Untrusted) -> Option<i32 @ Trusted> {
       match input.parse::<i32>() {
           Ok(n) if n >= 0 && n <= 1000 => Some(endorse(n)),
           _ => None
       }
   }

3. Authentication
   fn authenticate(creds: Credentials @ Untrusted) -> Option<User @ Trusted> {
       if verify_password(creds.password, stored_hash) {
           Some(endorse(User::from(creds.username)))
       } else {
           None
       }
   }
```

### 4.3 Robust Endorsement

```
Dual of robust declassification:

Changes to high-confidentiality data cannot affect
what low-confidentiality code endorses.

Prevents:
    - Covert channel attacks on integrity
    - Confused deputy via endorsement
```

---

## Part 5: Downgrading Policies

### 5.1 Policy Language

```
Expressing declassification policies:

policy PasswordCheck {
    allows: declassify(password_correct)  // bool only
    when: authentication_context
    who: auth_service
}

policy StatisticalQuery {
    allows: declassify(aggregate(data))
    when: query.is_aggregate && result.noise >= Îµ
    who: analytics_service
}

policy EmbargoRelease {
    allows: declassify(document)
    when: current_time > document.embargo_date
    who: document.owner
}
```

### 5.2 Policy Enforcement

```
Static enforcement:
    - Type checker verifies policy
    - Reject programs violating policy
    - Sound but conservative

Dynamic enforcement:
    - Runtime policy checks
    - More flexible
    - Overhead cost

Hybrid:
    - Static for structure
    - Dynamic for conditions
```

### 5.3 Policy Composition

```
Combining policies:

policy Combined = PasswordCheck && UserConsent

// Requires BOTH policies to allow declassification

policy Alternative = StatQuery || AdminOverride

// Either policy sufficient
```

---

## Part 6: TERAS Declassification Design

### 6.1 Declassification Syntax

```rust
// Explicit declassification with policy
#[policy(PasswordCheck)]
fn check_password(input: &str @ Untrusted, stored: Hash @ Secret) 
    -> bool @ Public 
{
    let hash = secure_hash(input);
    declassify!(
        constant_time_eq(&hash, &stored),
        from: Secret,
        to: Public,
        policy: PasswordCheck,
        justification: "Password verification result"
    )
}
```

### 6.2 Authority System

```rust
// Authority trait
trait DeclassifyAuthority<From: Label, To: Label> {
    fn can_declassify(&self) -> bool;
}

// Principal-based authority
impl DeclassifyAuthority<Secret, Public> for Principal {
    fn can_declassify(&self) -> bool {
        self.has_role(Role::SecurityOfficer) ||
        self.has_capability(Capability::Declassify)
    }
}

// Effect for declassification
effect Declassify<From, To> {
    fn declassify<T>(value: T @ From) -> T @ To
        where CurrentPrincipal: DeclassifyAuthority<From, To>;
}
```

### 6.3 Endorsement Syntax

```rust
// Endorsement after validation
fn validate_and_endorse(input: String @ Untrusted) -> Result<String @ Trusted, Error> {
    // Validate
    let validated = validate_input(&input)?;
    
    // Endorse
    endorse!(
        validated,
        from: Untrusted,
        to: Trusted,
        validation: "input_sanitization",
        justification: "HTML sanitized, length checked"
    )
}
```

### 6.4 Audit Integration

```rust
// All declassification is audited
fn declassify_impl<T, From, To>(
    value: T @ From,
    policy: Policy,
    justification: &str
) -> T @ To 
where
    From: Label, To: Label,
    CurrentPrincipal: DeclassifyAuthority<From, To>
{
    // Audit the declassification
    Audit::log(AuditEvent::Declassification {
        from: From::name(),
        to: To::name(),
        principal: current_principal(),
        policy: policy.name(),
        justification: justification.to_string(),
        timestamp: monotonic_time(),
        location: caller_location(),
    });
    
    // Perform declassification
    unsafe { transmute_label(value) }
}
```

---

## Part 7: Product Applications

### 7.1 BENTENG (eKYC)

```rust
// Verification result declassification
#[policy(VerificationComplete)]
fn verify_identity(
    face: FaceTemplate @ TopSecret,
    document: DocumentData @ Secret
) -> VerificationResult @ Internal {
    let match_score = face_match(face, document.photo);
    let doc_valid = verify_document(document);
    
    declassify!(
        VerificationResult {
            verified: match_score > THRESHOLD && doc_valid,
            confidence: confidence_bucket(match_score), // Bucketed, not exact
        },
        from: Secret,
        to: Internal,
        policy: VerificationComplete
    )
}
```

### 7.2 GAPURA (WAF)

```rust
// Request endorsement after validation
fn process_request(req: Request @ Untrusted) -> Response {
    // Validate and endorse
    let validated = validate_request(req)?;
    let safe_req: Request @ Trusted = endorse!(validated, Validated);
    
    // Process with trusted request
    backend.handle(safe_req)
}
```

---

## Part 8: Bibliography

1. Sabelfeld, A., Sands, D. (2009). "Declassification: Dimensions and Principles"
2. Zdancewic, S., Myers, A.C. (2001). "Robust Declassification"
3. Chong, S., Myers, A.C. (2004). "Security Policies for Downgrading"
4. Askarov, A., Sabelfeld, A. (2007). "Gradual Release"
5. Li, P., Zdancewic, S. (2006). "Downgrading Policies and Relaxed Noninterference"

---

*Research Track Output â€” Domain C: Information Flow Control*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
