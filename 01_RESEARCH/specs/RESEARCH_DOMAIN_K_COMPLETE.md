# TERAS-LANG Research Domain K: Metaprogramming and Macros

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-K-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | K-01 through K-10 |
| Domain | K: Metaprogramming and Macros |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# K-01: Metaprogramming Foundations

## Executive Summary

Metaprogramming enables code that writes or manipulates code, reducing boilerplate and enabling DSLs. For security systems, metaprogramming must be controlled to prevent injection attacks and maintain auditability.

## Metaprogramming Approaches

```
1. Text-Based Macros (C preprocessor)
   - Simple string substitution
   - Unhygienic (name clashes)
   - No type awareness
   
2. Syntactic Macros (Rust, Lisp)
   - Operate on AST
   - Hygienic expansion
   - Type-aware possible

3. Compile-Time Execution (Zig, D)
   - Full language at compile time
   - Powerful but complex
   - Can generate code

4. Reflection (Java, C#)
   - Runtime introspection
   - Modify behavior dynamically
   - Performance overhead

5. Template Metaprogramming (C++, Rust generics)
   - Type-level computation
   - Zero runtime overhead
   - Complex error messages
```

## Security Considerations

```
Metaprogramming Risks:

1. Code Injection
   - Untrusted input in macros
   - Generated SQL/commands
   
2. Hidden Behavior
   - Macro obscures intent
   - Audit difficulty

3. Build Tampering
   - Malicious proc macros
   - Supply chain attacks

4. Information Leakage
   - Compile-time secrets
   - Debug output

TERAS Mitigations:
- Hygienic macros only
- No runtime code generation
- Macro expansion audit
- Sandboxed proc macros
```

## TERAS Decision K-01

**IMPLEMENT** metaprogramming:
1. Hygienic macros only
2. No runtime code generation
3. Audit macro expansion
4. Sandboxed procedural macros

### Architecture Decision ID: `TERAS-ARCH-K01-META-001`

---

# K-02: Declarative Macros

## Macro by Example

```rust
// Simple macro
macro_rules! vec {
    () => { Vec::new() };
    ($($elem:expr),+ $(,)?) => {
        {
            let mut v = Vec::new();
            $(v.push($elem);)+
            v
        }
    };
}

// Usage
let v = vec![1, 2, 3];

// Expands to:
let v = {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    v.push(3);
    v
};
```

## Pattern Matching

```rust
// Fragment types
macro_rules! match_demo {
    // Expression
    (expr: $e:expr) => { println!("expr: {}", $e) };
    
    // Identifier
    (ident: $i:ident) => { let $i = 42; };
    
    // Type
    (ty: $t:ty) => { let x: $t = Default::default(); };
    
    // Pattern
    (pat: $p:pat) => { match x { $p => {} } };
    
    // Statement
    (stmt: $s:stmt) => { $s };
    
    // Token tree
    (tt: $t:tt) => { $t };
    
    // Literal
    (lit: $l:literal) => { $l };
    
    // Block
    (block: $b:block) => { $b };
    
    // Path
    (path: $p:path) => { use $p; };
}
```

## Repetition Patterns

```rust
// Zero or more: $(...)*
// One or more: $(...)+
// Optional: $(...)?

macro_rules! tuple_from {
    ($($t:ty),*) => {
        impl<$($t),*> From<($($t),*)> for MyStruct {
            fn from(tuple: ($($t),*)) -> Self {
                let ($($t),*) = tuple;
                // ...
            }
        }
    };
}

// Nested repetition
macro_rules! nested {
    ($($outer:ident: $($inner:expr),*);*) => {
        $(
            let $outer = vec![$($inner),*];
        )*
    };
}
```

## TERAS Security Macros

```rust
// Audit logging macro
macro_rules! audit {
    ($event_type:ident { $($field:ident: $value:expr),* $(,)? }) => {
        {
            let event = $crate::audit::AuditEvent::$event_type {
                timestamp: $crate::time::now(),
                correlation_id: $crate::context::correlation_id(),
                $($field: $value),*
            };
            $crate::audit::log(event);
        }
    };
}

// Usage
audit!(AuthAttempt {
    username: &user.name,
    success: false,
    ip: &client_ip,
});

// Secure assert macro
macro_rules! security_assert {
    ($cond:expr, $msg:expr) => {
        if !$cond {
            $crate::audit::log_security_violation($msg);
            panic!("Security assertion failed: {}", $msg);
        }
    };
}
```

## TERAS Decision K-02

**IMPLEMENT** declarative macros:
1. macro_rules! syntax
2. Hygienic expansion
3. Fragment types
4. Repetition patterns

### Architecture Decision ID: `TERAS-ARCH-K02-DECL-001`

---

# K-03: Procedural Macros

## Proc Macro Types

```rust
// Function-like: custom_macro!(...)
#[proc_macro]
pub fn custom_macro(input: TokenStream) -> TokenStream {
    // Process tokens
    input
}

// Derive macro: #[derive(MyTrait)]
#[proc_macro_derive(MyTrait)]
pub fn derive_my_trait(input: TokenStream) -> TokenStream {
    // Generate trait implementation
}

// Attribute macro: #[my_attribute]
#[proc_macro_attribute]
pub fn my_attribute(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Transform item
    item
}
```

## Token Manipulation

```rust
use proc_macro2::{TokenStream, TokenTree};
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(Serialize)]
pub fn derive_serialize(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    let name = &input.ident;
    let generics = &input.generics;
    
    let expanded = quote! {
        impl #generics Serialize for #name #generics {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                // Generated implementation
            }
        }
    };
    
    expanded.into()
}
```

## TERAS Security Proc Macros

```rust
// Capability requirement macro
#[proc_macro_attribute]
pub fn requires_capability(attr: TokenStream, item: TokenStream) -> TokenStream {
    let cap = parse_macro_input!(attr as Ident);
    let func = parse_macro_input!(item as ItemFn);
    
    let name = &func.sig.ident;
    let inputs = &func.sig.inputs;
    let output = &func.sig.output;
    let body = &func.block;
    
    let expanded = quote! {
        fn #name(#inputs) #output {
            if !$crate::capability::has_capability::<#cap>() {
                panic!("Missing capability: {}", stringify!(#cap));
            }
            $crate::audit::log_capability_use::<#cap>(stringify!(#name));
            #body
        }
    };
    
    expanded.into()
}

// Usage
#[requires_capability(CryptoSign)]
fn sign_document(doc: &Document) -> Signature {
    // ...
}

// Automatic validation derive
#[proc_macro_derive(Validate, attributes(validate))]
pub fn derive_validate(input: TokenStream) -> TokenStream {
    // Generate validation code from field attributes
}
```

## TERAS Decision K-03

**IMPLEMENT** proc macros:
1. Three macro types
2. Token stream API
3. Sandboxed execution
4. Security-focused macros

### Architecture Decision ID: `TERAS-ARCH-K03-PROC-001`

---

# K-04: Macro Hygiene

## Hygiene Principles

```
Hygiene: Macros don't accidentally capture or conflict with names

Unhygienic Example (C):
    #define SWAP(a, b) { int temp = a; a = b; b = temp; }
    int temp = 1, x = 2;
    SWAP(temp, x);  // Bug: captures 'temp'

Hygienic Expansion:
    - Each macro expansion has its own scope
    - Names from macro don't clash with call site
    - Names from call site don't leak into macro
```

## Rust Hygiene Model

```rust
macro_rules! make_var {
    ($name:ident) => {
        let x = 42;  // Macro's 'x' - different from caller's
        let $name = x;  // $name is from caller's scope
    };
}

fn example() {
    let x = 10;
    make_var!(y);
    // x is still 10 (macro's x is separate)
    // y is 42
}
```

## Breaking Hygiene (When Needed)

```rust
// $crate for referring to defining crate
macro_rules! use_my_type {
    () => {
        $crate::types::MyType::new()
    };
}

// Identifier interpolation
macro_rules! make_fn {
    ($name:ident) => {
        fn $name() {}  // Uses caller's identifier
    };
}

// Span manipulation in proc macros
fn set_span(tokens: TokenStream, span: Span) -> TokenStream {
    tokens.into_iter()
        .map(|mut tt| { tt.set_span(span); tt })
        .collect()
}
```

## TERAS Hygiene Requirements

```rust
// All TERAS macros must be hygienic
// Audit trail for any hygiene breaks

macro_rules! teras_macro {
    ($user_code:expr) => {
        {
            // Macro-internal names use __teras prefix
            let __teras_result = $user_code;
            __teras_result
        }
    };
}

// Proc macros must document hygiene breaks
#[proc_macro_attribute]
#[hygiene(breaks = ["injected_field"])]
pub fn add_audit_field(attr: TokenStream, item: TokenStream) -> TokenStream {
    // Intentionally adds a field named 'audit_context'
    // Documented as hygiene break
}
```

## TERAS Decision K-04

**IMPLEMENT** hygiene:
1. Default hygienic
2. $crate for paths
3. Document hygiene breaks
4. Audit hygiene violations

### Architecture Decision ID: `TERAS-ARCH-K04-HYG-001`

---

# K-05: Compile-Time Computation

## Const Functions

```rust
// Compile-time evaluation
const fn factorial(n: u64) -> u64 {
    match n {
        0 | 1 => 1,
        _ => n * factorial(n - 1),
    }
}

const FACT_10: u64 = factorial(10);  // Computed at compile time

// Const generics
struct Buffer<const N: usize> {
    data: [u8; N],
}

impl<const N: usize> Buffer<N> {
    const fn new() -> Self {
        Buffer { data: [0; N] }
    }
    
    const fn capacity(&self) -> usize {
        N
    }
}
```

## Compile-Time Assertions

```rust
// Static assert
macro_rules! static_assert {
    ($cond:expr) => {
        const _: () = assert!($cond);
    };
    ($cond:expr, $msg:expr) => {
        const _: () = assert!($cond, $msg);
    };
}

// Usage
static_assert!(std::mem::size_of::<u64>() == 8);
static_assert!(KEY_SIZE >= 16, "Key size must be at least 16 bytes");

// Type-level assertions
trait AssertEq<T> {}
impl<T> AssertEq<T> for T {}

fn assert_same_type<T, U>() where T: AssertEq<U> {}
```

## TERAS Compile-Time Security

```rust
// Compile-time security checks
const fn verify_key_size<const N: usize>() {
    assert!(N == 16 || N == 24 || N == 32, "Invalid AES key size");
}

struct AesKey<const N: usize> {
    key: [u8; N],
}

impl<const N: usize> AesKey<N> {
    const fn new(key: [u8; N]) -> Self {
        verify_key_size::<N>();
        AesKey { key }
    }
}

// Compile-time capability check
const fn requires_capability(cap: &str) -> bool {
    // Check against compile-time capability manifest
    matches!(cap, "CryptoAll" | "AuditRead")
}

// Security label computation
const fn label_join(a: u8, b: u8) -> u8 {
    // Compute least upper bound
    if a > b { a } else { b }
}
```

## TERAS Decision K-05

**IMPLEMENT** const computation:
1. Const functions
2. Const generics
3. Static assertions
4. Compile-time security checks

### Architecture Decision ID: `TERAS-ARCH-K05-CONST-001`

---

# K-06: Derive Macros

## Standard Derives

```rust
// Debug: Debugging format
#[derive(Debug)]
struct Point { x: i32, y: i32 }
// Generates: impl Debug for Point { fn fmt(&self, f: &mut Formatter) -> fmt::Result { ... } }

// Clone: Cloning
#[derive(Clone)]
struct Data { values: Vec<u8> }
// Generates: impl Clone for Data { fn clone(&self) -> Self { ... } }

// Copy: Bit-wise copy
#[derive(Copy, Clone)]
struct Coord { x: i32, y: i32 }

// PartialEq, Eq: Equality
#[derive(PartialEq, Eq)]
struct Id(u64);

// Hash: Hashing
#[derive(Hash)]
struct Key { id: u64, name: String }

// Default: Default value
#[derive(Default)]
struct Config { timeout: u64, retries: u32 }
```

## Custom Derives

```rust
// Define custom derive
#[proc_macro_derive(Serialize)]
pub fn derive_serialize(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    let name = &input.ident;
    let fields = match &input.data {
        Data::Struct(data) => &data.fields,
        _ => panic!("Serialize only works on structs"),
    };
    
    let field_serializers = fields.iter().map(|f| {
        let name = &f.ident;
        quote! {
            state.serialize_field(stringify!(#name), &self.#name)?;
        }
    });
    
    let expanded = quote! {
        impl Serialize for #name {
            fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                let mut state = serializer.serialize_struct(stringify!(#name), #field_count)?;
                #(#field_serializers)*
                state.end()
            }
        }
    };
    
    expanded.into()
}
```

## TERAS Security Derives

```rust
// Derive for secure zeroing
#[proc_macro_derive(SecureZeroize)]
pub fn derive_secure_zeroize(input: TokenStream) -> TokenStream {
    // Generate Drop that zeroizes memory
}

// Usage
#[derive(SecureZeroize)]
struct PrivateKey {
    material: [u8; 32],
}

// Derive for audit serialization
#[proc_macro_derive(AuditSerialize)]
pub fn derive_audit_serialize(input: TokenStream) -> TokenStream {
    // Generate audit-safe serialization (redact sensitive fields)
}

// Usage
#[derive(AuditSerialize)]
struct LoginAttempt {
    username: String,
    #[audit(redact)]
    password: String,
    ip_address: IpAddr,
}

// Derive for validation
#[proc_macro_derive(Validate, attributes(validate))]
pub fn derive_validate(input: TokenStream) -> TokenStream {
    // Generate validation from field attributes
}

// Usage
#[derive(Validate)]
struct UserInput {
    #[validate(min_length = 3, max_length = 50)]
    username: String,
    #[validate(email)]
    email: String,
    #[validate(min_length = 8)]
    password: String,
}
```

## TERAS Decision K-06

**IMPLEMENT** derives:
1. Standard derives
2. Custom derive API
3. Security derives
4. Attribute helpers

### Architecture Decision ID: `TERAS-ARCH-K06-DER-001`

---

# K-07: Domain-Specific Languages (DSLs)

## Embedded DSLs

```rust
// Query DSL
let query = sql! {
    SELECT id, name, email
    FROM users
    WHERE active = true
    AND created_at > @since
};

// The macro parses SQL syntax and generates type-safe code
macro_rules! sql {
    (SELECT $($fields:ident),+ FROM $table:ident WHERE $($cond:tt)+) => {
        Query::new(stringify!($table))
            $(.field(stringify!($fields)))+
            .where_clause(parse_conditions!($($cond)+))
    };
}

// HTML DSL
let page = html! {
    <html>
        <head><title>{title}</title></head>
        <body>
            <h1>{heading}</h1>
            <p class="content">{content}</p>
        </body>
    </html>
};
```

## TERAS Security DSLs

```rust
// Security policy DSL
let policy = security_policy! {
    resource "documents/*" {
        allow read if principal.has_capability(DocumentRead);
        allow write if principal.has_capability(DocumentWrite)
                    && principal.clearance >= Secret;
        deny all if resource.classification > principal.clearance;
    }
    
    resource "crypto/keys/*" {
        allow read if principal.has_capability(CryptoRead)
                   && principal.clearance == TopSecret;
        deny write;  // Keys are immutable
    }
};

// Firewall rules DSL (GAPURA)
let rules = waf_rules! {
    rule "sql_injection" {
        detect sql_injection_pattern in [body, query_params];
        action block;
        severity critical;
    }
    
    rule "rate_limit" {
        condition requests_per_minute > 100;
        action throttle(rate: 10/minute);
        severity medium;
    }
};

// Threat signatures DSL (ZIRAH)
let signatures = threat_signatures! {
    signature "ransomware_pattern" {
        file_extension in [".encrypted", ".locked"];
        entropy > 7.5;
        strings contains ["bitcoin", "ransom", "decrypt"];
        action quarantine;
    }
};
```

## DSL Implementation

```rust
// Parser for custom DSL
#[proc_macro]
pub fn security_policy(input: TokenStream) -> TokenStream {
    let policy = parse_policy(input);
    
    // Validate policy
    validate_policy(&policy)?;
    
    // Generate enforcement code
    let rules = policy.rules.iter().map(|rule| {
        let resource = &rule.resource;
        let checks = generate_checks(&rule.conditions);
        let action = generate_action(&rule.action);
        
        quote! {
            if request.resource.matches(#resource) {
                #checks
                #action
            }
        }
    });
    
    quote! {
        fn enforce_policy(request: &Request, principal: &Principal) -> PolicyDecision {
            #(#rules)*
            PolicyDecision::Deny  // Default deny
        }
    }.into()
}
```

## TERAS Decision K-07

**IMPLEMENT** DSLs:
1. Security policy DSL
2. WAF rules DSL
3. Threat signature DSL
4. Query builder DSL

### Architecture Decision ID: `TERAS-ARCH-K07-DSL-001`

---

# K-08: Attribute Macros

## Attribute Syntax

```rust
// Simple attribute
#[inline]
fn fast_path() {}

// Attribute with arguments
#[repr(C)]
struct CCompatible { ... }

// Attribute with key-value
#[derive(Debug)]
#[serde(rename_all = "camelCase")]
struct ApiResponse { ... }

// Inner attribute
#![allow(dead_code)]
```

## Custom Attributes

```rust
// Logging attribute
#[proc_macro_attribute]
pub fn log_calls(attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);
    let name = &func.sig.ident;
    let block = &func.block;
    
    quote! {
        fn #name(#inputs) #output {
            log::info!("Entering {}", stringify!(#name));
            let __result = { #block };
            log::info!("Exiting {}", stringify!(#name));
            __result
        }
    }.into()
}

// Usage
#[log_calls]
fn important_operation() {
    // ...
}
```

## TERAS Security Attributes

```rust
// Capability requirement
#[requires_capability(CryptoSign)]
fn sign_data(data: &[u8]) -> Signature { ... }

// Clearance requirement
#[requires_clearance(Secret)]
fn access_classified(doc: &Document) -> &[u8] { ... }

// Audit all calls
#[audited(level = Full)]
fn sensitive_operation() { ... }

// No-panic guarantee
#[no_panic]
fn safe_parse(s: &str) -> Option<i32> { ... }

// Constant-time requirement
#[constant_time]
fn compare_secrets(a: &[u8], b: &[u8]) -> bool { ... }

// Implementation
#[proc_macro_attribute]
pub fn requires_clearance(attr: TokenStream, item: TokenStream) -> TokenStream {
    let clearance = parse_macro_input!(attr as Ident);
    let func = parse_macro_input!(item as ItemFn);
    
    let name = &func.sig.ident;
    let vis = &func.vis;
    let sig = &func.sig;
    let block = &func.block;
    
    quote! {
        #vis #sig {
            if !$crate::security::check_clearance::<#clearance>() {
                panic!("Insufficient clearance for {}", stringify!(#name));
            }
            $crate::audit::log($crate::audit::ClearanceCheck {
                function: stringify!(#name),
                required: stringify!(#clearance),
                granted: true,
            });
            #block
        }
    }.into()
}
```

## TERAS Decision K-08

**IMPLEMENT** attributes:
1. Security attributes
2. Audit attributes
3. Performance attributes
4. Compile-time checks

### Architecture Decision ID: `TERAS-ARCH-K08-ATTR-001`

---

# K-09: Macro Debugging and Testing

## Macro Expansion

```rust
// cargo expand to see expansion
// Original:
#[derive(Debug)]
struct Point { x: i32, y: i32 }

// Expanded:
struct Point { x: i32, y: i32 }
impl ::core::fmt::Debug for Point {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        ::core::fmt::Formatter::debug_struct(f, "Point")
            .field("x", &self.x)
            .field("y", &self.y)
            .finish()
    }
}
```

## Testing Macros

```rust
// Test macro expansion
#[test]
fn test_vec_macro() {
    let v = vec![1, 2, 3];
    assert_eq!(v, [1, 2, 3]);
}

// Test procedural macros
#[test]
fn test_derive_serialize() {
    #[derive(Serialize)]
    struct Test { value: i32 }
    
    let t = Test { value: 42 };
    let json = t.serialize_json();
    assert_eq!(json, r#"{"value":42}"#);
}

// Compile-fail tests
// tests/compile-fail/missing_capability.rs
#[requires_capability(CryptoSign)]
fn needs_cap() {}

fn main() {
    needs_cap();  //~ ERROR: Missing capability
}

// Expansion tests
#[test]
fn test_expansion() {
    let input = quote! {
        struct Test { value: i32 }
    };
    
    let output = derive_serialize(input);
    
    let expected = quote! {
        impl Serialize for Test {
            // ...
        }
    };
    
    assert_eq!(output.to_string(), expected.to_string());
}
```

## TERAS Macro Auditing

```rust
// Macro expansion audit
#[proc_macro_attribute]
pub fn audit_expansion(attr: TokenStream, item: TokenStream) -> TokenStream {
    let expanded = process_macro(item.clone());
    
    // Log expansion for audit
    log::debug!("Macro expansion audit:");
    log::debug!("  Input: {}", item);
    log::debug!("  Output: {}", expanded);
    
    expanded
}

// Security review of macro output
fn review_expansion(expansion: &TokenStream) -> Result<(), SecurityError> {
    let tokens: Vec<_> = expansion.clone().into_iter().collect();
    
    // Check for suspicious patterns
    for token in &tokens {
        if let TokenTree::Ident(ident) = token {
            if BANNED_IDENTS.contains(&ident.to_string()) {
                return Err(SecurityError::BannedIdentifier(ident.to_string()));
            }
        }
    }
    
    Ok(())
}
```

## TERAS Decision K-09

**IMPLEMENT** macro testing:
1. Expansion viewing
2. Unit tests
3. Compile-fail tests
4. Security audit

### Architecture Decision ID: `TERAS-ARCH-K09-TEST-001`

---

# K-10: Metaprogramming in TERAS Products

## MENARA Macros

```rust
// Threat detection rule macro
threat_rule! {
    name: "malicious_app",
    severity: High,
    indicators: [
        permission("SEND_SMS") && permission("READ_CONTACTS"),
        signature_missing,
        obfuscated_code,
    ],
    action: Alert,
}

// Expands to threat detection logic with audit

// Permission check macro
check_permissions! {
    required: [CAMERA, LOCATION],
    optional: [CONTACTS],
    on_denied: notify_user,
}
```

## GAPURA Macros

```rust
// WAF rule definition
waf_rule! {
    id: "SQLI-001",
    name: "SQL Injection Detection",
    phase: Request,
    match_pattern: r"(?i)(union|select|insert|delete|update|drop)",
    targets: [QueryParams, Body, Headers],
    action: Block { status: 403 },
    log: true,
}

// Rate limit macro
rate_limit! {
    key: client_ip,
    limit: 100 per minute,
    burst: 10,
    action: Throttle { delay: 1000ms },
}
```

## ZIRAH Macros

```rust
// Signature definition
malware_signature! {
    id: "RANSOM-001",
    family: "LockBit",
    patterns: [
        bytes: [0x4D, 0x5A, 0x90],
        strings: ["Your files have been encrypted"],
        entropy: > 7.8,
    ],
    severity: Critical,
}

// Behavioral rule
behavior_rule! {
    name: "rapid_file_encryption",
    condition: file_modifications > 100 per second,
    file_types: [doc, pdf, xls],
    action: Quarantine,
}
```

## BENTENG Macros

```rust
// Document field extraction
ocr_template! {
    document: MyKad,
    fields: {
        name: region(x: 100, y: 50, w: 300, h: 30),
        ic_number: region(x: 100, y: 90, w: 200, h: 25),
        address: region(x: 100, y: 150, w: 300, h: 100),
    },
    validations: {
        ic_number: regex(r"^\d{6}-\d{2}-\d{4}$"),
    },
}

// Liveness check
liveness_challenge! {
    steps: [
        turn_head(direction: Left, angle: 30),
        blink(times: 2),
        smile,
    ],
    timeout: 30s,
    anti_spoof: enabled,
}
```

## SANDI Macros

```rust
// Signature format
signature_format! {
    standard: PAdES,
    level: B-LT,
    hash: SHA256,
    timestamp: required,
    certificate_chain: embedded,
}

// Certificate policy
cert_policy! {
    key_usage: [DigitalSignature, NonRepudiation],
    extended_key_usage: [DocumentSigning],
    validity: 2 years,
    revocation_check: OCSP,
}
```

## TERAS Decision K-10

**IMPLEMENT** product macros:
1. Product-specific DSLs
2. Rule definition macros
3. Configuration macros
4. Security policy macros

### Architecture Decision ID: `TERAS-ARCH-K10-PROD-001`

---

# Domain K Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| K-01 | Foundations | TERAS-ARCH-K01-META-001 |
| K-02 | Declarative | TERAS-ARCH-K02-DECL-001 |
| K-03 | Procedural | TERAS-ARCH-K03-PROC-001 |
| K-04 | Hygiene | TERAS-ARCH-K04-HYG-001 |
| K-05 | Const | TERAS-ARCH-K05-CONST-001 |
| K-06 | Derives | TERAS-ARCH-K06-DER-001 |
| K-07 | DSLs | TERAS-ARCH-K07-DSL-001 |
| K-08 | Attributes | TERAS-ARCH-K08-ATTR-001 |
| K-09 | Testing | TERAS-ARCH-K09-TEST-001 |
| K-10 | Products | TERAS-ARCH-K10-PROD-001 |

## Domain K: COMPLETE

---

*Research Track Output â€” Domain K: Metaprogramming and Macros*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
