# RESEARCH_A15_STAGED_TYPES_DECISION.md

## TERAS Research Track â€” Domain A: Type Theory
### Session A-15: Staged Types â€” Architecture Decision Record

**Version:** 1.0.0
**Date:** 2026-01-03
**Classification:** Architecture Decision
**Status:** APPROVED
**Decision ID:** TERAS-LANG-A15-001

---

# EXECUTIVE SUMMARY

**DECISION:** ADOPT MetaOCaml-style typed multi-stage programming as the core staging model for TERAS-LANG, with compile-time evaluation (comptime) for constant computation, integrated with linear types (A-04), effects (A-11), and capabilities (A-14) for zero-overhead code specialization with full type safety.

**RATIONALE:** Typed MSP provides the strongest guarantees for code generation in security-critical contexts, ensuring generated code is well-typed and scope-safe while enabling powerful compile-time specialization for cryptographic algorithms, protocol implementations, and security rule compilation.

---

# PART I: DECISION CONTEXT

## 1.1 Problem Statement

TERAS-LANG requires staging mechanisms that:
- Enable zero-overhead specialization of security-critical code
- Guarantee well-typed code generation
- Prevent scope extrusion and variable capture attacks
- Integrate with linear types, effects, and capabilities
- Support both compile-time and multi-stage computation

## 1.2 Decision Drivers

| Driver | Weight | Description |
|--------|--------|-------------|
| D38 | Critical | Performance via compile-time specialization |
| Type Safety | Critical | Generated code must be well-typed |
| Scope Safety | High | No variable escape/capture vulnerabilities |
| Integration | High | Coherence with A-04, A-11, A-14 |
| Practicality | Medium | Usable by security engineers |

## 1.3 Candidates Evaluated

| Candidate | Source | Core Approach |
|-----------|--------|---------------|
| Typed MSP | MetaOCaml | Environment classifiers, n-stage |
| Typed Quotes | Scala 3 | Type-indexed quotation |
| Compile-time | Zig | comptime evaluation |
| Template-based | Template Haskell | Q monad, splices |
| Token-based | Rust proc_macro | Token stream transform |

---

# PART II: DECISION SPECIFICATION

## 2.1 Core Decision: Typed Multi-Stage Programming

### 2.1.1 Code Type Definition

```
Staged Type Syntax:

code[Ï„]          -- code producing value of type Ï„
code[Ï„ ! E]      -- code with effect E when run
lin code[Ï„]      -- linear code (must run exactly once)
code[Ï„] at Ï     -- code in region Ï

Type Formation:
  Ï„ : Type
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  code[Ï„] : Type

Kinding:
  code : Type â†’ Type
```

### 2.1.2 Staging Primitives

```
Staging Operations:

Bracket (quote):
  .< e >.           -- delay computation, create code
  
  Typing:
    Î“ âŠ¢ e : Ï„
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ .<e>. : code[Ï„]

Escape (splice):
  .~ e              -- execute code within bracket
  
  Typing:
    Î“â‚€ âŠ¢ e : code[Ï„]   (in bracket context Î“â‚)
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“â‚€ âŠ— Î“â‚ âŠ¢ .~e : Ï„

Run (execute):
  run e             -- execute generated code
  
  Typing:
    Î“ âŠ¢ e : code[Ï„]
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ run e : Ï„
```

### 2.1.3 Environment Classifiers (Scope Safety)

```
Environment Classifier System:

Stage Levels:
  n âˆˆ â„•           -- stage level (0 = current, 1 = next, ...)

Classifier Annotations:
  Î“â¿              -- context at stage n
  Ï„â¿              -- type at stage n

Cross-Stage Rules:
  Î“â¿ âŠ¢ e : Ï„
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (stage raise)
  Î“â¿âºÂ¹ âŠ¢ .<e>. : code[Ï„]â¿âºÂ¹

  Î“â¿ âŠ¢ e : code[Ï„]â¿    (in context Î“â¿âºÂ¹)
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (stage lower)
  Î“â¿ âŠ— Î“â¿âºÂ¹ âŠ¢ .~e : Ï„â¿âºÂ¹

Scope Safety Theorem:
  Well-typed staged code cannot reference variables
  from wrong stages (no scope extrusion).
```

## 2.2 Compile-Time Evaluation (comptime)

### 2.2.1 Comptime Expressions

```
Compile-Time Computation:

comptime Keyword:
  comptime { e }    -- evaluate e at compile time
  
  Typing:
    Î“ âŠ¢ e : Ï„    e is comptime-evaluable
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ comptime { e } : Ï„

Comptime-Evaluable:
  - Literals and constants
  - Pure functions on comptime values
  - Type-level computations
  - No I/O or non-determinism

Examples:
  comptime { 1 + 2 }              -- 3
  comptime { factorial(10) }      -- 3628800
  comptime { generate_table() }   -- compile-time table
```

### 2.2.2 Comptime Functions

```
Compile-Time Function Parameters:

fn power<comptime N: u32>(x: f64) -> f64 {
    comptime {
        if N == 0 { return 1.0; }
    }
    let mut result = x;
    inline for _ in 1..N {
        result = result * x;
    }
    result
}

// Expands at compile time:
power<4>(x)  â†’  x * x * x * x

Typing:
  comptime N: Ï„   -- compile-time parameter
  Guaranteed evaluated before runtime
```

### 2.2.3 Comptime vs Staged Types

```
Distinction:

comptime:
  - Single stage: compile vs run
  - No code generation
  - Values computed at compile time
  - Result embedded as constant

code[Ï„]:
  - Multi-stage: arbitrary stages
  - Generates code values
  - Code can be manipulated
  - Run executes generated code

Use Cases:
  comptime -- lookup tables, constants, type-level
  code[Ï„] -- specialization, DSL compilation, metaprogramming
```

## 2.3 Integration Specifications

### 2.3.1 Integration with Linear Types (A-04)

```
Linear Staged Types:

Linearity Modes for Code:
  lin code[Ï„]     -- code must be run exactly once
  aff code[Ï„]     -- code may be run at most once
  unr code[Ï„]     -- code may be run multiple times (default)

Linear Results:
  code[lin Ï„]     -- code produces linear value
  
Combined:
  lin code[lin Ï„] -- linear code producing linear value

Typing Rules:
  Î“ âŠ¢ e : lin code[Ï„]    e used exactly once
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  Î“ âŠ¢ run e : Ï„

Example:
  fn make_transaction() -> lin code[lin Transaction] {
      .<begin_transaction()>.
  }
  // Code must be run exactly once
  // Resulting transaction must be used linearly
```

### 2.3.2 Integration with Effects (A-11)

```
Staged Effects:

Effect in Generated Code:
  code[Ï„ ! E]     -- running code has effect E
  
  Typing:
    Î“ âŠ¢ e : Ï„ ! E
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ .<e>. : code[Ï„ ! E]
    
    Î“ âŠ¢ e : code[Ï„ ! E]
    â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
    Î“ âŠ¢ run e : Ï„ ! E

Effect During Staging:
  (code[Ï„]) ! F   -- constructing code has effect F
  
  Example:
    fn build_code(config: &Config) -> code[Data] ! IO {
        let settings = config.read()?;  // IO during staging
        .<process(~settings)>.           // embed in code
    }

Handler Pattern:
  handle { run generated_code }
  with SecurityHandler { ... }
```

### 2.3.3 Integration with Capabilities (A-14)

```
Staged Capabilities:

Code Producing Capability:
  code[cap<R, P>]   -- generated code produces capability
  
  Example:
    fn compile_opener(path: Path) -> code[cap<File, Read>] {
        .<open_file(~path)>.
    }
    
    let opener = compile_opener("/etc/config");
    let file_cap = run opener;  // capability created at runtime

Capability During Staging:
  fn compile_with_cap<R, P>(c: &cap<R, P>) -> code[Data] 
      where P >= Read 
  {
      let config = c.read();     // use capability during staging
      .<constant(~config)>.      // embed result in code
  }

POLA for Staging:
  - Staging-time capabilities separate from runtime
  - Generated code should receive capabilities at runtime
  - Don't embed capabilities in generated code
```

### 2.3.4 Integration with Regions (A-12)

```
Region-Scoped Staging:

Code in Region:
  code[Ï„] at Ï    -- code value lives in region Ï
  
  letregion Ï in
      let c : code[Data] at Ï = .<compute()>.
      let result = run c
  end  // code deallocated with region

Cross-Stage Region Safety:
  .<letregion Ï in
      let x : Data at Ï = allocate()
      .~(f .<x>.)   // ERROR: x would escape region
    end>.
    
  -- Type system prevents region escape through staging

Region Effects in Code:
  code[Ï„ ! Alloc<Ï>]   -- code allocates in region Ï
```

---

# PART III: TYPE SYSTEM SPECIFICATION

## 3.1 Staged Type Formation

```
Staged Type Grammar:

CodeType ::= code[Ï„]
           | code[Ï„ ! E]
           | lin CodeType
           | aff CodeType
           | CodeType at Ï

Well-Formedness:
  Ï„ : Type
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  code[Ï„] : Type

  Ï„ : Type    E : Effect
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  code[Ï„ ! E] : Type
```

## 3.2 Complete Typing Rules

```
Staging Typing Rules:

-- Bracket (code creation)
Î“â¿ âŠ¢ e : Ï„
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“â¿âºÂ¹ âŠ¢ .<e>. : code[Ï„]

-- Escape (splice)
Î“â¿ âŠ¢ e : code[Ï„]
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (in bracket at level n+1)
Î“â¿ âŠ— Î“â¿âºÂ¹ âŠ¢ .~e : Ï„

-- Run
Î“ âŠ¢ e : code[Ï„]
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ run e : Ï„

-- Run with effects
Î“ âŠ¢ e : code[Ï„ ! E]
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ run e : Ï„ ! E

-- Linear code
Î“ âŠ¢ e : lin code[Ï„]    e used exactly once
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
Î“ âŠ¢ run e : Ï„

-- Cross-stage persistence (lift)
Î“â¿ âŠ¢ v : Ï„    Ï„ is CSP-able
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€  (in bracket at n+1)
Î“â¿ âŠ— Î“â¿âºÂ¹ âŠ¢ ~v : Ï„
```

## 3.3 Soundness Properties

```
Staged Type Safety Theorems:

THEOREM (Stage Preservation):
  If Î“ âŠ¢ e : code[Ï„] then run e : Ï„ is well-typed.
  (Generated code preserves types)

THEOREM (Scope Safety):
  If Î“â¿ âŠ¢ .<e>. : code[Ï„] then e does not reference
  variables from stage n+1 except via escape.
  (No scope extrusion)

THEOREM (No Capture):
  Variables bound in quoted code cannot capture
  dynamically scoped bindings.
  (Hygienic code generation)

THEOREM (Linear Staging):
  If c : lin code[Ï„], then c is run exactly once.
  (Linear code discipline preserved)

THEOREM (Effect Safety):
  If e : code[Ï„ ! E], then run e : Ï„ ! E.
  (Effects correctly tracked through staging)
```

---

# PART IV: TERAS PRODUCT APPLICATIONS

## 4.1 MENARA (Mobile Security)

```
Staged Authentication:

-- Compile authentication challenge handlers
compile_challenge_handler :: ChallengeType -> code[Challenge -> Response]
compile_challenge_handler PIN_Challenge =
    let validator = build_pin_validator() in
    .<fn challenge -> validator.validate(challenge)>.
compile_challenge_handler Biometric_Challenge =
    let matcher = load_biometric_model() in
    .<fn challenge -> matcher.verify(challenge)>.

-- Session token generation specialization
compile_token_generator :: TokenPolicy -> code[Session -> Token ! Crypto]
compile_token_generator policy =
    let key = policy.signing_key in
    let ttl = policy.token_ttl in
    .<fn session -> 
        let claims = session.to_claims() in
        sign(claims, ~key).with_expiry(~ttl)
    >.

-- Model loaded at compile time, execution at runtime
```

## 4.2 GAPURA (Web Application Firewall)

```
Staged Rule Compilation:

-- Compile WAF rules to specialized checkers
compile_rules :: [WAFRule] -> code[Request -> FilterResult]
compile_rules rules =
    let compiled = rules.map(compile_single_rule) in
    .<fn req ->
        for rule_code in ~compiled:
            match run rule_code with req:
                Block reason -> return Block reason
                Allow -> continue
        Allow
    >.

compile_single_rule :: WAFRule -> code[Request -> FilterResult]
compile_single_rule (SQLInjection patterns) =
    let regex = compile_regex(patterns) in
    .<fn req -> 
        if regex_match(~regex, req.params) then Block "SQLi"
        else Allow
    >.
compile_single_rule (XSSFilter patterns) =
    let sanitizer = build_sanitizer(patterns) in
    .<fn req ->
        if ~sanitizer.detect(req.body) then Block "XSS"
        else Allow
    >.

-- Regex compilation at staging time, matching at runtime
```

## 4.3 ZIRAH (Endpoint Detection & Response)

```
Staged Detection Compilation:

-- Compile detection signatures to optimized matchers
compile_signature :: Signature -> code[Process -> MatchResult]
compile_signature (BytePattern bytes mask) =
    let matcher = build_byte_matcher(bytes, mask) in
    .<fn proc ->
        let memory = proc.read_memory() in
        ~matcher.scan(memory)
    >.

compile_signature (BehaviorPattern events) =
    let automaton = compile_to_dfa(events) in
    .<fn proc ->
        let event_stream = proc.events() in
        ~automaton.match_stream(event_stream)
    >.

-- Compile detection rules into efficient scanner
compile_detection_engine :: [Signature] -> code[ScanEngine]
compile_detection_engine sigs =
    let matchers = sigs.map(compile_signature) in
    .<ScanEngine::new(~matchers)>.

-- DFA construction at compile time, execution at runtime
```

## 4.4 BENTENG (eKYC/Identity)

```
Staged Verification Pipelines:

-- Compile document verification for specific types
compile_verifier :: DocumentType -> code[Image -> VerifyResult ! Biometric]
compile_verifier Passport =
    let mrz_decoder = build_mrz_decoder() in
    let face_extractor = load_face_model() in
    .<fn image ->
        let mrz = ~mrz_decoder.extract(image) in
        let face = ~face_extractor.extract(image) in
        verify_passport(mrz, face)
    >.

compile_verifier NationalID region =
    let template = load_template(region) in
    let ocr = build_ocr(region.script) in
    .<fn image ->
        let fields = ~ocr.extract(image, ~template) in
        verify_national_id(fields)
    >.

-- Model loading at compile time, inference at runtime
```

## 4.5 SANDI (Digital Signatures)

```
Staged Cryptographic Operations:

-- Specialize signing algorithm
compile_signer :: SignatureAlgorithm -> code[Key -> Message -> Signature ! Crypto]
compile_signer RSA_PSS =
    let hasher = build_sha256() in
    let padder = build_pss_padding() in
    .<fn key msg ->
        let hash = ~hasher.hash(msg) in
        let padded = ~padder.pad(hash) in
        rsa_sign(key, padded)
    >.

compile_signer ECDSA curve =
    let params = load_curve_params(curve) in
    .<fn key msg ->
        ecdsa_sign(~params, key, msg)
    >.

-- Compile-time algorithm selection, runtime signing
-- Curve parameters embedded as constants

compile_verifier :: SignatureAlgorithm -> code[PublicKey -> Message -> Signature -> Bool]
compile_verifier alg = ... // analogous
```

---

# PART V: IMPLEMENTATION ROADMAP

## 5.1 Phase Structure

| Phase | Duration | Deliverables |
|-------|----------|--------------|
| Phase 1 | Weeks 1-4 | Core code types and staging primitives |
| Phase 2 | Weeks 5-8 | Environment classifiers and scope safety |
| Phase 3 | Weeks 9-12 | Comptime evaluation |
| Phase 4 | Weeks 13-16 | Integration with A-04, A-11, A-14 |
| Phase 5 | Weeks 17-20 | Code generation backend |
| Phase 6 | Weeks 21-24 | TERAS product staged APIs |

## 5.2 Phase 1: Core Staging

```
Week 1-2: Code Type
  - code[Ï„] type constructor
  - Basic bracket/escape/run
  - Type preservation

Week 3-4: Staging Semantics
  - Operational semantics
  - Substitution for staging
  - Initial code generation
```

## 5.3 Phase 2: Scope Safety

```
Week 5-6: Environment Classifiers
  - Stage level tracking
  - Variable scope analysis
  - Cross-stage variable handling

Week 7-8: Safety Proofs
  - Scope extrusion prevention
  - Hygiene guarantees
  - Formal verification
```

## 5.4 Phase 3: Comptime

```
Week 9-10: Comptime Evaluation
  - comptime keyword
  - Compile-time evaluator
  - Constant embedding

Week 11-12: Comptime Functions
  - comptime parameters
  - Inline expansion
  - Dead code elimination
```

## 5.5 Phase 4: Integration

```
Week 13-14: Linear/Effect Integration
  - lin code[Ï„] types
  - code[Ï„ ! E] effect tracking
  - Handler interaction

Week 15-16: Capability Integration
  - code[cap<R,P>] patterns
  - Staging-time vs runtime caps
  - POLA for staged code
```

---

# PART VI: RISK ANALYSIS

## 6.1 Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Compile time explosion | Medium | High | Memoization, limits |
| Code size blowup | Medium | Medium | CSE, sharing |
| Debugging complexity | High | Medium | Source maps, debugging tools |
| Integration complexity | Medium | High | Incremental integration |

## 6.2 Mitigation Strategies

```
Risk Mitigation:

1. Compile Time Explosion
   - Memoize staged computations
   - Limit staging depth
   - Incremental recompilation

2. Code Size Blowup
   - Common subexpression elimination
   - Code sharing for similar specializations
   - Configurable inlining limits

3. Debugging Complexity
   - Source maps for generated code
   - Stage-aware debugging
   - Error messages show staging context

4. Integration Complexity
   - Start with simple staging
   - Add features incrementally
   - Comprehensive test suite
```

---

# PART VII: DECISION RECORD

## 7.1 Decision Statement

**ADOPTED:** MetaOCaml-style typed multi-stage programming with the following components:

1. **Core Staging:** code[Ï„] types with bracket/escape/run
   - Full type safety via environment classifiers
   - Scope safety preventing variable capture
   - N-stage support for complex metaprogramming

2. **Compile-Time:** comptime for constant evaluation
   - comptime blocks and parameters
   - Compile-time function evaluation
   - Type-level computation

3. **Integration:** Full coherence with prior decisions
   - A-04: lin code[Ï„] for linear staging
   - A-11: code[Ï„ ! E] for effectful code
   - A-14: Staged capability authority

## 7.2 Alternatives Rejected

| Alternative | Reason for Rejection |
|-------------|---------------------|
| Template Haskell-style | Partial type safety, Q monad complexity |
| Rust proc_macro-style | No type safety, token-based |
| Pure comptime | Insufficient for runtime code gen |
| Untyped quotation | Security risk, no type guarantees |

## 7.3 Consequences

**Positive:**
- Generated code guaranteed well-typed
- Scope safety prevents capture attacks
- Zero runtime overhead for specialization
- Powerful compile-time computation
- Natural integration with type system

**Negative:**
- Compile time may increase significantly
- Learning curve for staging concepts
- Debugging staged code requires tooling

**Neutral:**
- Requires code generation backend
- Some restrictions on what can be staged

## 7.4 Compliance

| Requirement | Compliance | Notes |
|-------------|------------|-------|
| D38 (Performance) | âœ“ Full | Specialization enables optimization |
| Type Safety | âœ“ Full | Environment classifiers |
| Integration | âœ“ Full | Linear, effects, capabilities |
| Security | âœ“ Full | Scope safety, hygiene |

## 7.5 Approval

```
Decision: APPROVED
Date: 2026-01-03
Authority: TERAS-LANG Architecture Board (Simulated)
Review Cycle: 6 months

Alignment Score: 9.1/10

Scoring Breakdown:
  Type Safety:            25/25
  Integration:            18/20
  Security:               18/20
  Performance:            13/15
  Usability:               7/10
  Expressiveness:         10/10
  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
  Total:                  91/100
```

---

# APPENDIX A: STAGING PATTERNS

## A.1 Power Function (Classic Example)

```
-- Staged power function
power : comptime n : Nat -> f64 -> f64
power 0 x = 1.0
power n x = x * power (n - 1) x

-- Usage: power<4> generates x * x * x * x

-- Staged version with code type
power_staged : Nat -> code[f64 -> f64]
power_staged 0 = .<fn x -> 1.0>.
power_staged n = 
    let rec = power_staged (n - 1) in
    .<fn x -> x * (.~rec) x>.

-- run (power_staged 4) generates optimized code
```

## A.2 DSL Compilation Pattern

```
-- Example: simple expression DSL
datatype Expr =
    | Lit(i32)
    | Add(Expr, Expr)
    | Mul(Expr, Expr)
    | Var(String)

-- Compile DSL to code
compile_expr : Expr -> code[Env -> i32]
compile_expr (Lit n) = .<fn _ -> ~n>.
compile_expr (Add a b) = 
    let ca = compile_expr a in
    let cb = compile_expr b in
    .<fn env -> (.~ca) env + (.~cb) env>.
compile_expr (Mul a b) =
    let ca = compile_expr a in
    let cb = compile_expr b in
    .<fn env -> (.~ca) env * (.~cb) env>.
compile_expr (Var name) =
    .<fn env -> env.lookup(~name)>.
```

## A.3 Type-Safe Printf Pattern

```
-- Format string compilation
datatype Format =
    | FLit(String)
    | FInt
    | FString
    | FSeq(Format, Format)

-- Compile format to typed function
compile_format : Format -> Type Ã— code[... -> String]
compile_format FLit(s) = (Unit, .<fn () -> ~s>.)
compile_format FInt = (i32, .<fn n -> to_string(n)>.)
compile_format FString = (String, .<fn s -> s>.)
compile_format FSeq(a, b) =
    let (ta, ca) = compile_format a in
    let (tb, cb) = compile_format b in
    ((ta, tb), .<fn (x, y) -> (.~ca) x ++ (.~cb) y>.)
```

---

# APPENDIX B: FORMAL SEMANTICS SKETCH

## B.1 Staged Judgment Forms

```
Judgment Forms:

Î“â¿ âŠ¢ e : Ï„        -- e has type Ï„ at stage n
Î“ âŠ¢ e â‡“ v         -- e evaluates to v
âŸ¦eâŸ§ = code        -- code generation
```

## B.2 Operational Semantics (excerpt)

```
Small-Step Staging Semantics:

-- Bracket is value
.<v>. is a value

-- Escape substitution
.<... .~e ...>. â†’ .<... v ...>.  when e â‡“ .<v>.

-- Run execution
run .<e>. â†’ e

-- CSP (cross-stage persistence)
.<... ~v ...>. â†’ .<... v ...>.  when v is CSP-able
```

---

**END OF DECISION DOCUMENT**

**Session A-15 Complete**
**Next Session:** A-16 (Sized Types)
