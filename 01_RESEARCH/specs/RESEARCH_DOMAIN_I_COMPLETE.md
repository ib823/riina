# TERAS-LANG Research Domain I: Error Handling and Exceptions

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-I-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | I-01 through I-10 |
| Domain | I: Error Handling and Exceptions |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# I-01: Error Handling Foundations

## Executive Summary

Error handling in security-critical systems must be explicit, recoverable, and auditable. Silent failures, unhandled exceptions, and ambiguous error states create security vulnerabilities. TERAS-LANG requires a principled approach that makes errors visible and forces proper handling.

## Error Handling Paradigms

```
Exception-Based (Java, Python, C++):
    try {
        riskyOperation();
    } catch (Exception e) {
        handle(e);
    }
    
    Problems:
    - Invisible control flow
    - Easy to ignore
    - Performance overhead
    - Exception safety is hard

Result-Based (Rust, Haskell, OCaml):
    match riskyOperation() {
        Ok(value) => use(value),
        Err(e) => handle(e),
    }
    
    Benefits:
    - Explicit in types
    - Cannot ignore (easily)
    - Zero-cost abstractions
    - Composable

Effect-Based (Koka, TERAS):
    fn riskyOperation() -> T ! Error {
        // Error as effect
    }
    
    Benefits:
    - Unified with other effects
    - Resumable handlers
    - Effect polymorphism
    - Fine-grained control
```

## Security Implications

```
Error Handling Vulnerabilities:

1. Information Disclosure
   - Stack traces expose internals
   - Error messages reveal structure
   - Timing differences leak info

2. Denial of Service
   - Uncaught exceptions crash system
   - Resource leaks on error paths
   - Infinite retry loops

3. Authentication Bypass
   - Fail-open patterns
   - Exception swallowing
   - Default-allow on error

4. Injection Attacks
   - Error messages with user input
   - Exception chaining with tainted data
```

## TERAS Error Design Principles

```
1. Explicit: Errors visible in function signatures
2. Exhaustive: All errors must be handled
3. Recoverable: Support graceful degradation
4. Auditable: Error events logged
5. Secure: No information leakage
6. Composable: Error handling composes
```

## TERAS Decision I-01

**IMPLEMENT** error handling:
1. Result-based as primary
2. Effect-based for advanced
3. No silent failures
4. Mandatory error handling

### Architecture Decision ID: `TERAS-ARCH-I01-ERR-001`

---

# I-02: Result Type

## Core Result Type

```rust
enum Result<T, E> {
    Ok(T),
    Err(E),
}

impl<T, E> Result<T, E> {
    // Query
    fn is_ok(&self) -> bool;
    fn is_err(&self) -> bool;
    
    // Extract
    fn unwrap(self) -> T;  // Panics on Err
    fn unwrap_or(self, default: T) -> T;
    fn unwrap_or_else<F: FnOnce(E) -> T>(self, f: F) -> T;
    fn expect(self, msg: &str) -> T;  // Panics with message
    
    // Transform
    fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Result<U, E>;
    fn map_err<F, O: FnOnce(E) -> F>(self, f: O) -> Result<T, F>;
    fn and_then<U, F: FnOnce(T) -> Result<U, E>>(self, f: F) -> Result<U, E>;
    fn or_else<F, O: FnOnce(E) -> Result<T, F>>(self, f: O) -> Result<T, F>;
    
    // Convert
    fn ok(self) -> Option<T>;
    fn err(self) -> Option<E>;
}
```

## Early Return with `?`

```rust
// The ? operator for early return
fn process_file(path: &Path) -> Result<Data, FileError> {
    let file = File::open(path)?;  // Returns Err if failed
    let content = file.read_to_string()?;
    let data = parse(&content)?;
    Ok(data)
}

// Desugars to:
fn process_file(path: &Path) -> Result<Data, FileError> {
    let file = match File::open(path) {
        Ok(f) => f,
        Err(e) => return Err(e.into()),
    };
    // ...
}
```

## Error Conversion

```rust
// From trait for error conversion
trait From<T> {
    fn from(t: T) -> Self;
}

// Automatic conversion with ?
impl From<IoError> for FileError {
    fn from(e: IoError) -> Self {
        FileError::Io(e)
    }
}

impl From<ParseError> for FileError {
    fn from(e: ParseError) -> Self {
        FileError::Parse(e)
    }
}

// Now ? converts automatically
fn process(path: &Path) -> Result<Data, FileError> {
    let content = std::fs::read_to_string(path)?;  // IoError -> FileError
    let data: Data = serde_json::from_str(&content)?;  // ParseError -> FileError
    Ok(data)
}
```

## TERAS Security Extensions

```rust
// Result with security label
struct LabeledResult<T, E, L: Label> {
    inner: Result<T, E>,
    _label: PhantomData<L>,
}

impl<T, E, L: Label> LabeledResult<T, E, L> {
    fn unwrap(self) -> T
    where
        L: FlowsTo<CurrentPC>  // Can only unwrap if PC allows
    {
        self.inner.unwrap()
    }
}

// Secure error - no information leakage
trait SecureError: Error {
    fn public_message(&self) -> &str;  // Safe to show user
    fn internal_details(&self) -> &str;  // Log only
}

impl SecureError for AuthError {
    fn public_message(&self) -> &str {
        "Authentication failed"  // Generic
    }
    
    fn internal_details(&self) -> &str {
        match self {
            AuthError::InvalidUser(u) => &format!("User {} not found", u),
            AuthError::WrongPassword(u) => &format!("Wrong password for {}", u),
            // Internal details for logging
        }
    }
}
```

## TERAS Decision I-02

**IMPLEMENT** Result type:
1. Standard Result<T, E>
2. `?` operator for early return
3. From trait for conversion
4. Security-aware variants

### Architecture Decision ID: `TERAS-ARCH-I02-RES-001`

---

# I-03: Error Types and Hierarchies

## Error Trait

```rust
trait Error: Debug + Display {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        None
    }
    
    fn backtrace(&self) -> Option<&Backtrace> {
        None
    }
}

// Display for user-facing message
impl Display for MyError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "operation failed: {}", self.reason)
    }
}

// Debug for developer details
impl Debug for MyError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("MyError")
            .field("reason", &self.reason)
            .field("code", &self.code)
            .finish()
    }
}
```

## Error Hierarchies

```rust
// Domain-specific error hierarchy
enum TerasError {
    // Cryptographic errors
    Crypto(CryptoError),
    
    // Authentication errors
    Auth(AuthError),
    
    // Authorization errors
    Authz(AuthzError),
    
    // I/O errors
    Io(IoError),
    
    // Validation errors
    Validation(ValidationError),
}

enum CryptoError {
    KeyGeneration { algorithm: Algorithm, reason: String },
    Encryption { algorithm: Algorithm, reason: String },
    Decryption { algorithm: Algorithm, reason: String },
    Signature { algorithm: Algorithm, reason: String },
    Verification { algorithm: Algorithm, reason: String },
    InvalidKey { expected: KeyType, found: KeyType },
}

enum AuthError {
    InvalidCredentials,
    SessionExpired { expired_at: DateTime },
    AccountLocked { until: Option<DateTime> },
    MfaRequired,
    MfaFailed,
}

enum AuthzError {
    InsufficientPermissions { required: Permission, had: Vec<Permission> },
    CapabilityRevoked { capability: CapabilityId },
    ClearanceInsufficient { required: Clearance, had: Clearance },
}
```

## Structured Errors

```rust
// Error with structured context
struct StructuredError {
    kind: ErrorKind,
    message: String,
    context: ErrorContext,
    source: Option<Box<dyn Error>>,
    backtrace: Option<Backtrace>,
}

struct ErrorContext {
    operation: &'static str,
    location: Location,
    timestamp: DateTime,
    correlation_id: CorrelationId,
    attributes: HashMap<String, Value>,
}

// Builder pattern
impl StructuredError {
    fn new(kind: ErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
            context: ErrorContext::capture(),
            source: None,
            backtrace: Backtrace::capture(),
        }
    }
    
    fn with_source(mut self, source: impl Error + 'static) -> Self {
        self.source = Some(Box::new(source));
        self
    }
    
    fn with_attribute(mut self, key: &str, value: impl Into<Value>) -> Self {
        self.context.attributes.insert(key.to_string(), value.into());
        self
    }
}
```

## TERAS Decision I-03

**IMPLEMENT** error types:
1. Error trait with source chain
2. Domain-specific hierarchies
3. Structured error context
4. Security-safe Display

### Architecture Decision ID: `TERAS-ARCH-I03-TYP-001`

---

# I-04: Error Effects

## Error as Effect

```rust
// Error as algebraic effect
effect Error<E> {
    fn raise(e: E) -> !;
}

// Function that may fail
fn divide(x: i32, y: i32) -> i32 ! Error<DivError> {
    if y == 0 {
        do Error::raise(DivError::DivByZero)
    } else {
        x / y
    }
}

// Handler converts to Result
handler result_handler<E> for Error<E> {
    return(x) => Ok(x),
    raise(e) => Err(e),
}

// Usage
let result: Result<i32, DivError> = 
    handle[result_handler] {
        divide(10, 2)
    };
```

## Resumable Errors

```rust
// Effect with resumption
effect TryParse {
    fn parse_error(input: &str, expected: &str) -> Value;
}

fn parse_int(s: &str) -> i32 ! TryParse {
    match s.parse::<i32>() {
        Ok(n) => n,
        Err(_) => do TryParse::parse_error(s, "integer"),
    }
}

// Handler that provides default
handler with_default<T: Default> for TryParse {
    parse_error(_, _) resume => resume(T::default()),
}

// Handler that prompts user
handler interactive for TryParse {
    parse_error(input, expected) resume => {
        println!("Could not parse '{}' as {}", input, expected);
        let corrected = prompt_user("Enter correct value: ");
        resume(corrected)
    }
}
```

## Multiple Error Effects

```rust
// Function with multiple error types
fn complex_operation(
    path: &Path,
    key: &Key
) -> Data ! Error<IoError> + Error<CryptoError> + Error<ParseError> {
    let encrypted = read_file(path)?;  // IoError
    let decrypted = decrypt(key, &encrypted)?;  // CryptoError
    let parsed = parse(&decrypted)?;  // ParseError
    parsed
}

// Handle each independently
handler io_handler for Error<IoError> { ... }
handler crypto_handler for Error<CryptoError> { ... }
handler parse_handler for Error<ParseError> { ... }

let result = 
    handle[io_handler] {
        handle[crypto_handler] {
            handle[parse_handler] {
                complex_operation(path, key)
            }
        }
    };
```

## TERAS Decision I-04

**IMPLEMENT** error effects:
1. Error as algebraic effect
2. Resumable error handlers
3. Multiple error types
4. Effect polymorphism

### Architecture Decision ID: `TERAS-ARCH-I04-EFF-001`

---

# I-05: Panic and Abort

## Panic vs Error

```
Error (Recoverable):
    - Expected failure modes
    - Handled by caller
    - Part of API contract
    - e.g., file not found, invalid input

Panic (Unrecoverable):
    - Programming bugs
    - Violated invariants
    - Corrupted state
    - e.g., index out of bounds, assertion failure
```

## Panic Mechanics

```rust
// Panic function
fn panic(msg: &str) -> ! {
    // 1. Set panic flag
    // 2. Begin unwinding OR abort
    // 3. Run destructors (if unwinding)
    // 4. Terminate thread
}

// Panic macro with formatting
macro_rules! panic {
    () => { panic("explicit panic") };
    ($msg:expr) => { panic($msg) };
    ($fmt:expr, $($arg:tt)*) => { 
        panic(&format!($fmt, $($arg)*)) 
    };
}

// Assert macros
macro_rules! assert {
    ($cond:expr) => {
        if !$cond { panic!("assertion failed: {}", stringify!($cond)) }
    };
}

macro_rules! debug_assert {
    ($cond:expr) => {
        #[cfg(debug_assertions)]
        assert!($cond)
    };
}
```

## Unwinding vs Abort

```rust
// Unwinding: Run destructors, catchable
#[panic_handler = "unwind"]
fn panicking_function() {
    let guard = MutexGuard::new(&mutex);
    panic!("something wrong");
    // guard.drop() still runs
}

// Abort: Immediate termination
#[panic_handler = "abort"]
fn panicking_function() {
    panic!("something wrong");
    // Process terminates immediately
}

// Catch unwind (for isolation)
fn catch_panic<F, R>(f: F) -> Result<R, Box<dyn Any>>
where
    F: FnOnce() -> R + UnwindSafe,
{
    std::panic::catch_unwind(f)
}
```

## TERAS Panic Policy

```rust
// Security-critical code should not panic
#[no_panic]
fn crypto_operation(key: &Key, data: &[u8]) -> Result<Vec<u8>, CryptoError> {
    // Compiler error if panic possible
}

// Panic audit in security modules
#[audit_panic]
mod sensitive {
    // All panics logged with context
}

// Graceful degradation
fn handle_request(req: Request) -> Response {
    match catch_unwind(|| process(req)) {
        Ok(resp) => resp,
        Err(panic) => {
            Audit::log(PanicCaught { info: &panic });
            Response::internal_error()  // Don't expose details
        }
    }
}
```

## TERAS Decision I-05

**IMPLEMENT** panic handling:
1. Abort as default for security
2. Unwind for plugin isolation
3. #[no_panic] attribute
4. Panic audit logging

### Architecture Decision ID: `TERAS-ARCH-I05-PAN-001`

---

# I-06: Error Context and Chaining

## Error Context

```rust
// Context trait for wrapping errors
trait Context<T, E> {
    fn context<C>(self, context: C) -> Result<T, ContextError<C, E>>
    where
        C: Display;
    
    fn with_context<C, F>(self, f: F) -> Result<T, ContextError<C, E>>
    where
        C: Display,
        F: FnOnce() -> C;
}

impl<T, E: Error> Context<T, E> for Result<T, E> {
    fn context<C>(self, context: C) -> Result<T, ContextError<C, E>>
    where
        C: Display,
    {
        self.map_err(|e| ContextError { context, source: e })
    }
    
    fn with_context<C, F>(self, f: F) -> Result<T, ContextError<C, E>>
    where
        C: Display,
        F: FnOnce() -> C,
    {
        self.map_err(|e| ContextError { context: f(), source: e })
    }
}

// Usage
fn load_config(path: &Path) -> Result<Config, Error> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read config from {:?}", path))?;
    
    let config: Config = toml::from_str(&content)
        .context("Failed to parse config as TOML")?;
    
    Ok(config)
}
```

## Error Chain

```rust
// Walk error chain
fn print_error_chain(error: &dyn Error) {
    eprintln!("Error: {}", error);
    
    let mut source = error.source();
    while let Some(cause) = source {
        eprintln!("Caused by: {}", cause);
        source = cause.source();
    }
}

// Find specific error in chain
fn find_error<E: Error + 'static>(error: &dyn Error) -> Option<&E> {
    let mut current: Option<&dyn Error> = Some(error);
    while let Some(e) = current {
        if let Some(specific) = e.downcast_ref::<E>() {
            return Some(specific);
        }
        current = e.source();
    }
    None
}

// Example output:
// Error: Failed to load user data
// Caused by: Failed to read config from "/etc/app/config.toml"
// Caused by: Permission denied (os error 13)
```

## Backtrace

```rust
// Capture backtrace at error creation
struct ErrorWithBacktrace<E> {
    error: E,
    backtrace: Backtrace,
}

impl<E> ErrorWithBacktrace<E> {
    fn new(error: E) -> Self {
        Self {
            error,
            backtrace: Backtrace::capture(),
        }
    }
}

// TERAS: Secure backtrace (no sensitive data)
struct SecureBacktrace {
    frames: Vec<SecureFrame>,
}

struct SecureFrame {
    function: String,  // Sanitized function name
    module: String,
    // No file paths, line numbers in release
}

impl SecureBacktrace {
    fn capture() -> Self {
        let bt = Backtrace::capture();
        Self {
            frames: bt.frames().iter()
                .map(|f| SecureFrame::sanitize(f))
                .collect()
        }
    }
}
```

## TERAS Decision I-06

**IMPLEMENT** error context:
1. Context wrapping
2. Error chain traversal
3. Secure backtraces
4. No sensitive data in errors

### Architecture Decision ID: `TERAS-ARCH-I06-CTX-001`

---

# I-07: Error Handling Patterns

## Railway-Oriented Programming

```rust
// Chain operations, short-circuit on error
fn process_order(order_id: OrderId) -> Result<Receipt, OrderError> {
    get_order(order_id)
        .and_then(validate_order)
        .and_then(calculate_total)
        .and_then(process_payment)
        .and_then(generate_receipt)
}

// With context at each step
fn process_order(order_id: OrderId) -> Result<Receipt, Error> {
    let order = get_order(order_id)
        .context("Failed to retrieve order")?;
    
    let validated = validate_order(order)
        .context("Order validation failed")?;
    
    let total = calculate_total(&validated)
        .context("Failed to calculate total")?;
    
    let payment = process_payment(&validated, total)
        .context("Payment processing failed")?;
    
    generate_receipt(&validated, &payment)
        .context("Failed to generate receipt")
}
```

## Fallback Chains

```rust
// Try multiple strategies
fn load_config() -> Result<Config, Error> {
    load_from_env()
        .or_else(|_| load_from_file("/etc/app/config.toml"))
        .or_else(|_| load_from_file("./config.toml"))
        .or_else(|_| Ok(Config::default()))
}

// With logging
fn load_config() -> Config {
    load_from_env()
        .inspect_err(|e| log::debug!("Env config failed: {}", e))
        .or_else(|_| load_from_file("/etc/app/config.toml"))
        .inspect_err(|e| log::debug!("System config failed: {}", e))
        .or_else(|_| load_from_file("./config.toml"))
        .inspect_err(|e| log::debug!("Local config failed: {}", e))
        .unwrap_or_else(|_| {
            log::info!("Using default config");
            Config::default()
        })
}
```

## Retry Pattern

```rust
// Retry with backoff
async fn retry<T, E, F, Fut>(
    operation: F,
    config: RetryConfig,
) -> Result<T, E>
where
    F: Fn() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: Error,
{
    let mut attempts = 0;
    let mut delay = config.initial_delay;
    
    loop {
        match operation().await {
            Ok(value) => return Ok(value),
            Err(e) if attempts < config.max_attempts && e.is_retryable() => {
                attempts += 1;
                Audit::log(RetryAttempt { attempt: attempts, error: &e });
                tokio::time::sleep(delay).await;
                delay = min(delay * 2, config.max_delay);  // Exponential backoff
            }
            Err(e) => return Err(e),
        }
    }
}

// Usage
let result = retry(
    || fetch_data(&url),
    RetryConfig {
        max_attempts: 3,
        initial_delay: Duration::from_millis(100),
        max_delay: Duration::from_secs(5),
    },
).await;
```

## Circuit Breaker

```rust
// Circuit breaker for external services
struct CircuitBreaker {
    state: AtomicState,
    failure_count: AtomicUsize,
    last_failure: AtomicInstant,
    config: CircuitConfig,
}

enum State { Closed, Open, HalfOpen }

impl CircuitBreaker {
    async fn call<T, E, F, Fut>(&self, operation: F) -> Result<T, CircuitError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        match self.state.load() {
            State::Open => {
                if self.should_try_reset() {
                    self.state.store(State::HalfOpen);
                } else {
                    return Err(CircuitError::Open);
                }
            }
            State::Closed | State::HalfOpen => {}
        }
        
        match operation().await {
            Ok(value) => {
                self.on_success();
                Ok(value)
            }
            Err(e) => {
                self.on_failure();
                Err(CircuitError::Inner(e))
            }
        }
    }
    
    fn on_failure(&self) {
        let failures = self.failure_count.fetch_add(1, Ordering::SeqCst) + 1;
        if failures >= self.config.threshold {
            self.state.store(State::Open);
            self.last_failure.store(Instant::now());
            Audit::log(CircuitOpened { failures });
        }
    }
}
```

## TERAS Decision I-07

**IMPLEMENT** patterns:
1. Railway-oriented chains
2. Fallback strategies
3. Retry with backoff
4. Circuit breaker

### Architecture Decision ID: `TERAS-ARCH-I07-PAT-001`

---

# I-08: Validation Errors

## Validation Framework

```rust
// Validation error collection
struct ValidationErrors {
    errors: Vec<ValidationError>,
}

struct ValidationError {
    field: String,
    message: String,
    code: ErrorCode,
}

// Validate and collect all errors
trait Validate {
    fn validate(&self) -> Result<(), ValidationErrors>;
}

impl Validate for UserInput {
    fn validate(&self) -> Result<(), ValidationErrors> {
        let mut errors = ValidationErrors::new();
        
        if self.username.is_empty() {
            errors.add("username", "Username is required", ErrorCode::Required);
        } else if self.username.len() < 3 {
            errors.add("username", "Username must be at least 3 characters", ErrorCode::TooShort);
        }
        
        if !is_valid_email(&self.email) {
            errors.add("email", "Invalid email format", ErrorCode::InvalidFormat);
        }
        
        if self.password.len() < 8 {
            errors.add("password", "Password must be at least 8 characters", ErrorCode::TooShort);
        }
        
        errors.into_result()
    }
}
```

## Typed Validation

```rust
// Validated wrapper type
struct Validated<T> {
    value: T,
}

impl<T: Validate> Validated<T> {
    fn new(value: T) -> Result<Self, ValidationErrors> {
        value.validate()?;
        Ok(Validated { value })
    }
    
    fn into_inner(self) -> T {
        self.value
    }
}

// Newtype for validated data
struct ValidatedEmail(String);

impl ValidatedEmail {
    fn new(s: &str) -> Result<Self, ValidationError> {
        if is_valid_email(s) {
            Ok(ValidatedEmail(s.to_string()))
        } else {
            Err(ValidationError::invalid_format("email"))
        }
    }
}

// Functions accept only validated input
fn send_email(to: ValidatedEmail, subject: &str, body: &str) -> Result<(), EmailError> {
    // to is guaranteed valid
}
```

## Security Validation

```rust
// Sanitization as validation
struct SanitizedHtml(String);

impl SanitizedHtml {
    fn new(raw: &str) -> Self {
        let sanitized = ammonia::clean(raw);
        SanitizedHtml(sanitized)
    }
}

// Taint tracking
struct TaintedInput<T> {
    value: T,
    source: InputSource,
}

struct TrustedInput<T> {
    value: T,
}

impl<T: Sanitize> TaintedInput<T> {
    fn sanitize(self) -> TrustedInput<T> {
        TrustedInput {
            value: self.value.sanitize()
        }
    }
}

// Database query only accepts trusted
fn query(sql: TrustedInput<SqlQuery>) -> Result<Rows, DbError> {
    // sql is guaranteed sanitized
}
```

## TERAS Decision I-08

**IMPLEMENT** validation:
1. Collect all errors
2. Validated wrapper types
3. Sanitization framework
4. Taint tracking integration

### Architecture Decision ID: `TERAS-ARCH-I08-VAL-001`

---

# I-09: Error Logging and Audit

## Structured Error Logging

```rust
// Error logging with structure
fn log_error(error: &dyn Error, context: &ErrorContext) {
    let log_entry = ErrorLogEntry {
        timestamp: Utc::now(),
        level: Level::Error,
        message: error.to_string(),
        error_type: type_name_of(error),
        correlation_id: context.correlation_id,
        operation: context.operation,
        attributes: context.attributes.clone(),
        source_chain: collect_source_chain(error),
        backtrace: if cfg!(debug) { 
            Some(error.backtrace()) 
        } else { 
            None 
        },
    };
    
    Logger::log(log_entry);
}

// Sensitive data filtering
fn sanitize_error_for_log(error: &dyn Error) -> String {
    let msg = error.to_string();
    SENSITIVE_PATTERNS.iter()
        .fold(msg, |s, pattern| pattern.replace_all(&s, "[REDACTED]"))
}
```

## Security Audit Trail

```rust
// Security-relevant errors must be audited
trait SecurityError: Error {
    fn audit_event(&self) -> SecurityAuditEvent;
}

enum SecurityAuditEvent {
    AuthenticationFailure {
        username: String,  // Not password!
        ip_address: IpAddr,
        reason: AuthFailureReason,
    },
    AuthorizationDenied {
        principal: Principal,
        resource: ResourceId,
        action: Action,
    },
    CryptoFailure {
        operation: CryptoOperation,
        algorithm: Algorithm,
        // Not key material!
    },
    IntegrityViolation {
        resource: ResourceId,
        expected: Hash,
        found: Hash,
    },
}

// Automatic audit on security errors
impl<T, E: SecurityError> Result<T, E> {
    fn audit_on_err(self) -> Self {
        if let Err(ref e) = self {
            Audit::log(e.audit_event());
        }
        self
    }
}
```

## Error Metrics

```rust
// Error rate tracking
struct ErrorMetrics {
    counters: DashMap<ErrorKind, AtomicU64>,
    histograms: DashMap<ErrorKind, Histogram>,
}

impl ErrorMetrics {
    fn record(&self, error: &dyn Error, duration: Duration) {
        let kind = classify_error(error);
        self.counters
            .entry(kind)
            .or_insert_with(|| AtomicU64::new(0))
            .fetch_add(1, Ordering::Relaxed);
        
        self.histograms
            .entry(kind)
            .or_insert_with(Histogram::new)
            .record(duration);
    }
    
    fn error_rate(&self, kind: ErrorKind, window: Duration) -> f64 {
        // Calculate error rate over time window
    }
}

// Alert on error spike
fn check_error_alerts(metrics: &ErrorMetrics) {
    for kind in ErrorKind::all() {
        let rate = metrics.error_rate(kind, Duration::from_secs(60));
        if rate > THRESHOLD {
            Alert::send(ErrorRateAlert { kind, rate });
        }
    }
}
```

## TERAS Decision I-09

**IMPLEMENT** error logging:
1. Structured error logs
2. Sensitive data filtering
3. Security audit trail
4. Error metrics and alerting

### Architecture Decision ID: `TERAS-ARCH-I09-LOG-001`

---

# I-10: Error Handling in TERAS Products

## MENARA (Mobile Security)

```rust
// Mobile error hierarchy
enum MenaraError {
    Network(NetworkError),
    Permission(PermissionError),
    Threat(ThreatError),
    Device(DeviceError),
}

// Graceful degradation
fn check_threat(app: &AppInfo) -> Result<ThreatAssessment, MenaraError> {
    // Try online check first
    match online_threat_check(app).await {
        Ok(assessment) => Ok(assessment),
        Err(NetworkError::Offline) => {
            // Fallback to local database
            local_threat_check(app)
                .map_err(MenaraError::from)
        }
        Err(e) => Err(MenaraError::Network(e)),
    }
}
```

## GAPURA (WAF)

```rust
// Request processing errors
enum GapuraError {
    Parse(ParseError),
    Validation(ValidationError),
    Blocked(BlockReason),
    Backend(BackendError),
    RateLimit(RateLimitError),
}

// Safe error responses
impl GapuraError {
    fn to_response(&self) -> Response {
        match self {
            GapuraError::Blocked(reason) => {
                Audit::log(RequestBlocked { reason });
                Response::forbidden()  // No details to client
            }
            GapuraError::RateLimit(_) => {
                Response::too_many_requests()
            }
            GapuraError::Backend(_) => {
                Response::bad_gateway()  // Hide backend details
            }
            _ => Response::bad_request(),
        }
    }
}
```

## ZIRAH (EDR)

```rust
// Scan errors with recovery
enum ZirahError {
    Io(IoError),
    Permission(PermissionError),
    Timeout(TimeoutError),
    Malformed(MalformedError),
}

impl ZirahError {
    fn is_recoverable(&self) -> bool {
        matches!(self, 
            ZirahError::Timeout(_) | 
            ZirahError::Io(IoError::Interrupted)
        )
    }
}

fn scan_with_retry(path: &Path) -> ScanResult {
    retry(
        || scan_file(path),
        RetryConfig::for_scan(),
    )
    .unwrap_or_else(|e| {
        Audit::log(ScanFailed { path, error: &e });
        ScanResult::Inconclusive { reason: e.to_string() }
    })
}
```

## BENTENG (eKYC)

```rust
// Verification errors
enum BentengError {
    FaceMismatch { confidence: f64 },
    DocumentInvalid { reason: DocumentError },
    LivenessFailed { reason: LivenessError },
    SessionExpired,
}

// User-friendly messages
impl BentengError {
    fn user_message(&self) -> &str {
        match self {
            BentengError::FaceMismatch { .. } => 
                "Face does not match document photo. Please try again.",
            BentengError::DocumentInvalid { .. } => 
                "Document could not be verified. Ensure good lighting and try again.",
            BentengError::LivenessFailed { .. } => 
                "Liveness check failed. Please follow the on-screen instructions.",
            BentengError::SessionExpired => 
                "Session expired. Please start verification again.",
        }
    }
}
```

## SANDI (Digital Signatures)

```rust
// Signature errors
enum SandiError {
    InvalidKey(KeyError),
    HsmError(HsmError),
    CertificateError(CertError),
    TimestampError(TsaError),
}

// HSM errors require special handling
impl SandiError {
    fn requires_admin(&self) -> bool {
        matches!(self, SandiError::HsmError(HsmError::DeviceError(_)))
    }
    
    fn is_user_recoverable(&self) -> bool {
        matches!(self, 
            SandiError::CertificateError(CertError::Expired) |
            SandiError::TimestampError(TsaError::Unavailable)
        )
    }
}

// Signature with fallback TSA
fn sign_with_timestamp(
    data: &[u8],
    key: &SigningKey,
    tsas: &[TsaConfig],
) -> Result<TimestampedSignature, SandiError> {
    let sig = key.sign(data)?;
    
    for tsa in tsas {
        match request_timestamp(tsa, &sig) {
            Ok(ts) => return Ok(TimestampedSignature { sig, ts }),
            Err(e) => {
                Audit::log(TsaFailed { tsa: &tsa.url, error: &e });
                continue;
            }
        }
    }
    
    Err(SandiError::TimestampError(TsaError::AllUnavailable))
}
```

## TERAS Decision I-10

**IMPLEMENT** product errors:
1. Product-specific hierarchies
2. User-safe messages
3. Recovery strategies
4. Audit integration

### Architecture Decision ID: `TERAS-ARCH-I10-PROD-001`

---

# Domain I Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| I-01 | Foundations | TERAS-ARCH-I01-ERR-001 |
| I-02 | Result Type | TERAS-ARCH-I02-RES-001 |
| I-03 | Error Types | TERAS-ARCH-I03-TYP-001 |
| I-04 | Error Effects | TERAS-ARCH-I04-EFF-001 |
| I-05 | Panic/Abort | TERAS-ARCH-I05-PAN-001 |
| I-06 | Context | TERAS-ARCH-I06-CTX-001 |
| I-07 | Patterns | TERAS-ARCH-I07-PAT-001 |
| I-08 | Validation | TERAS-ARCH-I08-VAL-001 |
| I-09 | Logging | TERAS-ARCH-I09-LOG-001 |
| I-10 | Products | TERAS-ARCH-I10-PROD-001 |

## Domain I: COMPLETE

---

*Research Track Output â€” Domain I: Error Handling and Exceptions*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
