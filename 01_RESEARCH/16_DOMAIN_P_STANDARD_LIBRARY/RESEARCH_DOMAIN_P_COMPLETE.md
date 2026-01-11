# TERAS-LANG Research Domain P: Standard Library Design

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-P-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | P-01 through P-10 |
| Domain | P: Standard Library Design |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# P-01: Standard Library Foundations

## Executive Summary

The standard library provides foundational types, traits, and functions that all TERAS programs can rely on. For security systems, the stdlib must be secure-by-default, memory-safe, and provide security primitives as first-class citizens.

## Standard Library Goals

```
1. Security by Default
   - Safe APIs preferred
   - Unsafe clearly marked
   - Security primitives built-in

2. Zero-Cost Abstractions
   - No runtime overhead for safety
   - Compile-time guarantees
   - Efficient implementations

3. Minimal but Complete
   - Essential functionality
   - No bloat
   - Extensible via packages

4. Consistent Design
   - Uniform API patterns
   - Predictable naming
   - Comprehensive documentation
```

## Library Organization

```
teras::
├── core::                  # Core types (no_std compatible)
│   ├── primitive          # Primitive types
│   ├── option             # Option<T>
│   ├── result             # Result<T, E>
│   ├── slice              # Slice operations
│   └── str                # String slice
├── alloc::                 # Allocation (requires allocator)
│   ├── vec                # Vec<T>
│   ├── string             # String
│   ├── boxed              # Box<T>
│   ├── rc                 # Rc<T>, Arc<T>
│   └── collections        # HashMap, BTreeMap, etc.
├── std::                   # Full standard library
│   ├── io                 # I/O operations
│   ├── fs                 # File system
│   ├── net                # Networking
│   ├── time               # Time operations
│   ├── thread             # Threading
│   └── sync               # Synchronization
└── security::              # Security primitives
    ├── crypto             # Cryptography
    ├── auth               # Authentication
    ├── audit              # Audit logging
    ├── capability         # Capabilities
    └── ifc                # Information flow
```

## TERAS Decision P-01

**IMPLEMENT** stdlib:
1. Layered architecture
2. Security-first design
3. no_std support
4. Comprehensive documentation

### Architecture Decision ID: `TERAS-ARCH-P01-STD-001`

---

# P-02: Core Types

## Primitive Types

```rust
// Numeric types
i8, i16, i32, i64, i128, isize   // Signed integers
u8, u16, u32, u64, u128, usize   // Unsigned integers
f32, f64                          // Floating point

// Boolean
bool                              // true, false

// Character
char                              // Unicode scalar value (4 bytes)

// Unit
()                                // Unit type

// Never
!                                 // Never type (for diverging functions)
```

## Option Type

```rust
enum Option<T> {
    Some(T),
    None,
}

impl<T> Option<T> {
    // Querying
    fn is_some(&self) -> bool;
    fn is_none(&self) -> bool;
    
    // Extracting
    fn unwrap(self) -> T;
    fn unwrap_or(self, default: T) -> T;
    fn unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T;
    fn expect(self, msg: &str) -> T;
    
    // Transforming
    fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Option<U>;
    fn and_then<U, F: FnOnce(T) -> Option<U>>(self, f: F) -> Option<U>;
    fn or(self, other: Option<T>) -> Option<T>;
    fn or_else<F: FnOnce() -> Option<T>>(self, f: F) -> Option<T>;
    
    // Converting
    fn ok_or<E>(self, err: E) -> Result<T, E>;
    fn ok_or_else<E, F: FnOnce() -> E>(self, f: F) -> Result<T, E>;
    
    // References
    fn as_ref(&self) -> Option<&T>;
    fn as_mut(&mut self) -> Option<&mut T>;
}
```

## Result Type

```rust
enum Result<T, E> {
    Ok(T),
    Err(E),
}

impl<T, E> Result<T, E> {
    // Querying
    fn is_ok(&self) -> bool;
    fn is_err(&self) -> bool;
    
    // Extracting
    fn unwrap(self) -> T;
    fn unwrap_err(self) -> E;
    fn unwrap_or(self, default: T) -> T;
    fn unwrap_or_else<F: FnOnce(E) -> T>(self, f: F) -> T;
    fn expect(self, msg: &str) -> T;
    
    // Transforming
    fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Result<U, E>;
    fn map_err<F, O: FnOnce(E) -> F>(self, f: O) -> Result<T, F>;
    fn and_then<U, F: FnOnce(T) -> Result<U, E>>(self, f: F) -> Result<U, E>;
    fn or_else<F, O: FnOnce(E) -> Result<T, F>>(self, f: O) -> Result<T, F>;
    
    // Converting
    fn ok(self) -> Option<T>;
    fn err(self) -> Option<E>;
}
```

## TERAS Decision P-02

**IMPLEMENT** core types:
1. Standard primitives
2. Option/Result
3. Zero-cost abstractions
4. Rich combinators

### Architecture Decision ID: `TERAS-ARCH-P02-CORE-001`

---

# P-03: Collections

## Vector

```rust
struct Vec<T> {
    ptr: *mut T,
    len: usize,
    cap: usize,
}

impl<T> Vec<T> {
    // Construction
    fn new() -> Vec<T>;
    fn with_capacity(capacity: usize) -> Vec<T>;
    fn from_elem(elem: T, n: usize) -> Vec<T> where T: Clone;
    
    // Capacity
    fn capacity(&self) -> usize;
    fn reserve(&mut self, additional: usize);
    fn shrink_to_fit(&mut self);
    
    // Length
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    
    // Modification
    fn push(&mut self, value: T);
    fn pop(&mut self) -> Option<T>;
    fn insert(&mut self, index: usize, element: T);
    fn remove(&mut self, index: usize) -> T;
    fn clear(&mut self);
    fn truncate(&mut self, len: usize);
    
    // Access
    fn get(&self, index: usize) -> Option<&T>;
    fn get_mut(&mut self, index: usize) -> Option<&mut T>;
    fn first(&self) -> Option<&T>;
    fn last(&self) -> Option<&T>;
    
    // Iteration
    fn iter(&self) -> Iter<'_, T>;
    fn iter_mut(&mut self) -> IterMut<'_, T>;
}

// Secure vector that zeroizes on drop
struct SecureVec<T: Zeroize> {
    inner: Vec<T>,
}

impl<T: Zeroize> Drop for SecureVec<T> {
    fn drop(&mut self) {
        for item in &mut self.inner {
            item.zeroize();
        }
    }
}
```

## HashMap

```rust
struct HashMap<K, V, S = DefaultHasher> {
    table: RawTable<(K, V)>,
    hash_builder: S,
}

impl<K: Hash + Eq, V> HashMap<K, V> {
    fn new() -> HashMap<K, V>;
    fn with_capacity(capacity: usize) -> HashMap<K, V>;
    
    // Capacity
    fn capacity(&self) -> usize;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    
    // Modification
    fn insert(&mut self, k: K, v: V) -> Option<V>;
    fn remove(&mut self, k: &K) -> Option<V>;
    fn clear(&mut self);
    
    // Access
    fn get(&self, k: &K) -> Option<&V>;
    fn get_mut(&mut self, k: &K) -> Option<&mut V>;
    fn contains_key(&self, k: &K) -> bool;
    
    // Entry API
    fn entry(&mut self, key: K) -> Entry<'_, K, V>;
}

// SipHash for security (DoS resistant)
struct SipHasher {
    k0: u64,
    k1: u64,
}

impl Default for SipHasher {
    fn default() -> Self {
        // Random keys from secure RNG
        let (k0, k1) = secure_random_keys();
        SipHasher { k0, k1 }
    }
}
```

## BTreeMap

```rust
struct BTreeMap<K, V> {
    root: Option<Box<Node<K, V>>>,
    length: usize,
}

impl<K: Ord, V> BTreeMap<K, V> {
    fn new() -> BTreeMap<K, V>;
    
    // Same API as HashMap
    fn insert(&mut self, k: K, v: V) -> Option<V>;
    fn remove(&mut self, k: &K) -> Option<V>;
    fn get(&self, k: &K) -> Option<&V>;
    fn contains_key(&self, k: &K) -> bool;
    
    // Ordered operations
    fn range<R: RangeBounds<K>>(&self, range: R) -> Range<'_, K, V>;
    fn first_key_value(&self) -> Option<(&K, &V)>;
    fn last_key_value(&self) -> Option<(&K, &V)>;
}
```

## TERAS Decision P-03

**IMPLEMENT** collections:
1. Standard collections
2. Secure variants
3. DoS-resistant hashing
4. Rich APIs

### Architecture Decision ID: `TERAS-ARCH-P03-COLL-001`

---

# P-04: String Types

## String and str

```rust
// String slice (borrowed)
struct str {
    // Internally: [u8] with UTF-8 guarantee
}

impl str {
    // Length
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    
    // Iteration
    fn chars(&self) -> Chars<'_>;
    fn bytes(&self) -> Bytes<'_>;
    fn lines(&self) -> Lines<'_>;
    
    // Searching
    fn contains(&self, pat: &str) -> bool;
    fn starts_with(&self, pat: &str) -> bool;
    fn ends_with(&self, pat: &str) -> bool;
    fn find(&self, pat: &str) -> Option<usize>;
    
    // Transformation
    fn to_lowercase(&self) -> String;
    fn to_uppercase(&self) -> String;
    fn trim(&self) -> &str;
    fn split(&self, pat: &str) -> Split<'_, &str>;
    fn replace(&self, from: &str, to: &str) -> String;
    
    // Conversion
    fn as_bytes(&self) -> &[u8];
    fn parse<F: FromStr>(&self) -> Result<F, F::Err>;
}

// Owned string
struct String {
    vec: Vec<u8>,
}

impl String {
    fn new() -> String;
    fn with_capacity(capacity: usize) -> String;
    fn from_utf8(vec: Vec<u8>) -> Result<String, FromUtf8Error>;
    
    fn push(&mut self, ch: char);
    fn push_str(&mut self, s: &str);
    fn pop(&mut self) -> Option<char>;
    fn clear(&mut self);
    
    fn as_str(&self) -> &str;
}
```

## Secure String

```rust
// String that zeroizes on drop
struct SecureString {
    inner: String,
}

impl SecureString {
    fn new() -> Self {
        SecureString { inner: String::new() }
    }
    
    fn from_str(s: &str) -> Self {
        SecureString { inner: s.to_string() }
    }
    
    fn as_str(&self) -> &str {
        &self.inner
    }
}

impl Drop for SecureString {
    fn drop(&mut self) {
        // Zeroize memory
        let bytes = unsafe { self.inner.as_mut_vec() };
        for byte in bytes.iter_mut() {
            unsafe { std::ptr::write_volatile(byte, 0); }
        }
        std::sync::atomic::compiler_fence(std::sync::atomic::Ordering::SeqCst);
    }
}

impl Debug for SecureString {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "SecureString([REDACTED])")
    }
}
```

## TERAS Decision P-04

**IMPLEMENT** strings:
1. UTF-8 by default
2. Rich string API
3. Secure string variant
4. No information leakage

### Architecture Decision ID: `TERAS-ARCH-P04-STR-001`

---

# P-05: I/O and File System

## I/O Traits

```rust
trait Read {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, IoError>;
    
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<(), IoError> {
        // Default implementation
    }
    
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize, IoError>;
    fn read_to_string(&mut self, buf: &mut String) -> Result<usize, IoError>;
}

trait Write {
    fn write(&mut self, buf: &[u8]) -> Result<usize, IoError>;
    fn flush(&mut self) -> Result<(), IoError>;
    
    fn write_all(&mut self, buf: &[u8]) -> Result<(), IoError> {
        // Default implementation
    }
}

trait Seek {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, IoError>;
}

trait BufRead: Read {
    fn fill_buf(&mut self) -> Result<&[u8], IoError>;
    fn consume(&mut self, amt: usize);
    fn read_line(&mut self, buf: &mut String) -> Result<usize, IoError>;
    fn lines(&self) -> Lines<Self>;
}
```

## File System

```rust
// File operations
struct File {
    fd: FileDescriptor,
}

impl File {
    fn open(path: &Path) -> Result<File, IoError>;
    fn create(path: &Path) -> Result<File, IoError>;
    
    fn open_with_options(path: &Path, options: &OpenOptions) -> Result<File, IoError>;
    
    fn metadata(&self) -> Result<Metadata, IoError>;
    fn set_permissions(&self, perm: Permissions) -> Result<(), IoError>;
}

struct OpenOptions {
    read: bool,
    write: bool,
    append: bool,
    truncate: bool,
    create: bool,
    create_new: bool,
}

// Directory operations
fn read_dir(path: &Path) -> Result<ReadDir, IoError>;
fn create_dir(path: &Path) -> Result<(), IoError>;
fn create_dir_all(path: &Path) -> Result<(), IoError>;
fn remove_dir(path: &Path) -> Result<(), IoError>;
fn remove_dir_all(path: &Path) -> Result<(), IoError>;

// File operations
fn copy(from: &Path, to: &Path) -> Result<u64, IoError>;
fn rename(from: &Path, to: &Path) -> Result<(), IoError>;
fn remove_file(path: &Path) -> Result<(), IoError>;
fn metadata(path: &Path) -> Result<Metadata, IoError>;
```

## Secure I/O

```rust
// Capability-protected file operations
#[requires_capability(FileRead)]
fn secure_read(path: &Path) -> Result<Vec<u8>, IoError> {
    audit!(FileAccess { path, operation: "read" });
    std::fs::read(path)
}

#[requires_capability(FileWrite)]
fn secure_write(path: &Path, data: &[u8]) -> Result<(), IoError> {
    audit!(FileAccess { path, operation: "write" });
    std::fs::write(path, data)
}

// Secure file with audit
struct AuditedFile {
    file: File,
    path: PathBuf,
}

impl Read for AuditedFile {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, IoError> {
        let n = self.file.read(buf)?;
        audit!(FileRead { path: &self.path, bytes: n });
        Ok(n)
    }
}

impl Write for AuditedFile {
    fn write(&mut self, buf: &[u8]) -> Result<usize, IoError> {
        let n = self.file.write(buf)?;
        audit!(FileWrite { path: &self.path, bytes: n });
        Ok(n)
    }
    
    fn flush(&mut self) -> Result<(), IoError> {
        self.file.flush()
    }
}
```

## TERAS Decision P-05

**IMPLEMENT** I/O:
1. Standard traits
2. Capability protection
3. Audit integration
4. Secure operations

### Architecture Decision ID: `TERAS-ARCH-P05-IO-001`

---

# P-06: Networking

## TCP

```rust
// TCP listener
struct TcpListener {
    inner: Socket,
}

impl TcpListener {
    fn bind(addr: impl ToSocketAddrs) -> Result<TcpListener, IoError>;
    fn accept(&self) -> Result<(TcpStream, SocketAddr), IoError>;
    fn local_addr(&self) -> Result<SocketAddr, IoError>;
    fn incoming(&self) -> Incoming<'_>;
}

// TCP stream
struct TcpStream {
    inner: Socket,
}

impl TcpStream {
    fn connect(addr: impl ToSocketAddrs) -> Result<TcpStream, IoError>;
    
    fn peer_addr(&self) -> Result<SocketAddr, IoError>;
    fn local_addr(&self) -> Result<SocketAddr, IoError>;
    
    fn shutdown(&self, how: Shutdown) -> Result<(), IoError>;
    
    fn set_read_timeout(&self, dur: Option<Duration>) -> Result<(), IoError>;
    fn set_write_timeout(&self, dur: Option<Duration>) -> Result<(), IoError>;
    fn set_nodelay(&self, nodelay: bool) -> Result<(), IoError>;
}

impl Read for TcpStream { ... }
impl Write for TcpStream { ... }
```

## UDP

```rust
struct UdpSocket {
    inner: Socket,
}

impl UdpSocket {
    fn bind(addr: impl ToSocketAddrs) -> Result<UdpSocket, IoError>;
    
    fn recv_from(&self, buf: &mut [u8]) -> Result<(usize, SocketAddr), IoError>;
    fn send_to(&self, buf: &[u8], addr: impl ToSocketAddrs) -> Result<usize, IoError>;
    
    fn connect(&self, addr: impl ToSocketAddrs) -> Result<(), IoError>;
    fn recv(&self, buf: &mut [u8]) -> Result<usize, IoError>;
    fn send(&self, buf: &[u8]) -> Result<usize, IoError>;
}
```

## Secure Networking

```rust
// TLS wrapper
struct TlsStream<S> {
    inner: S,
    session: TlsSession,
}

impl<S: Read + Write> TlsStream<S> {
    fn client(stream: S, domain: &str, config: &TlsConfig) -> Result<Self, TlsError>;
    fn server(stream: S, config: &TlsConfig) -> Result<Self, TlsError>;
}

impl<S: Read + Write> Read for TlsStream<S> { ... }
impl<S: Read + Write> Write for TlsStream<S> { ... }

// Network capability
#[requires_capability(NetworkConnect)]
fn secure_connect(addr: &str) -> Result<TcpStream, IoError> {
    audit!(NetworkConnection { address: addr, direction: "outbound" });
    TcpStream::connect(addr)
}

#[requires_capability(NetworkListen)]
fn secure_listen(addr: &str) -> Result<TcpListener, IoError> {
    audit!(NetworkListen { address: addr });
    TcpListener::bind(addr)
}
```

## TERAS Decision P-06

**IMPLEMENT** networking:
1. TCP/UDP sockets
2. TLS integration
3. Capability protection
4. Connection auditing

### Architecture Decision ID: `TERAS-ARCH-P06-NET-001`

---

# P-07: Time and Duration

## Time Types

```rust
// Duration
struct Duration {
    secs: u64,
    nanos: u32,
}

impl Duration {
    const ZERO: Duration = Duration { secs: 0, nanos: 0 };
    const MAX: Duration = Duration { secs: u64::MAX, nanos: 999_999_999 };
    
    fn new(secs: u64, nanos: u32) -> Duration;
    fn from_secs(secs: u64) -> Duration;
    fn from_millis(millis: u64) -> Duration;
    fn from_micros(micros: u64) -> Duration;
    fn from_nanos(nanos: u64) -> Duration;
    
    fn as_secs(&self) -> u64;
    fn as_millis(&self) -> u128;
    fn as_micros(&self) -> u128;
    fn as_nanos(&self) -> u128;
    
    fn checked_add(&self, rhs: Duration) -> Option<Duration>;
    fn checked_sub(&self, rhs: Duration) -> Option<Duration>;
    fn checked_mul(&self, rhs: u32) -> Option<Duration>;
    fn checked_div(&self, rhs: u32) -> Option<Duration>;
}

// Instant (monotonic clock)
struct Instant {
    inner: u64,
}

impl Instant {
    fn now() -> Instant;
    fn elapsed(&self) -> Duration;
    fn duration_since(&self, earlier: Instant) -> Duration;
    fn checked_add(&self, duration: Duration) -> Option<Instant>;
    fn checked_sub(&self, duration: Duration) -> Option<Instant>;
}

// SystemTime (wall clock)
struct SystemTime {
    inner: i64,
}

impl SystemTime {
    const UNIX_EPOCH: SystemTime = SystemTime { inner: 0 };
    
    fn now() -> SystemTime;
    fn elapsed(&self) -> Result<Duration, SystemTimeError>;
    fn duration_since(&self, earlier: SystemTime) -> Result<Duration, SystemTimeError>;
}
```

## Secure Time

```rust
// Secure timestamp (tamper-evident)
struct SecureTimestamp {
    time: SystemTime,
    sequence: u64,
    signature: Signature,
}

impl SecureTimestamp {
    fn now(signing_key: &SigningKey) -> Self {
        static SEQUENCE: AtomicU64 = AtomicU64::new(0);
        
        let time = SystemTime::now();
        let seq = SEQUENCE.fetch_add(1, Ordering::SeqCst);
        
        let data = format!("{:?}:{}", time, seq);
        let signature = signing_key.sign(data.as_bytes());
        
        SecureTimestamp { time, sequence: seq, signature }
    }
    
    fn verify(&self, public_key: &PublicKey) -> bool {
        let data = format!("{:?}:{}", self.time, self.sequence);
        public_key.verify(data.as_bytes(), &self.signature)
    }
}

// Monotonic counter for timing-attack resistance
struct MonotonicCounter {
    value: AtomicU64,
}

impl MonotonicCounter {
    fn increment(&self) -> u64 {
        self.value.fetch_add(1, Ordering::SeqCst)
    }
    
    fn current(&self) -> u64 {
        self.value.load(Ordering::SeqCst)
    }
}
```

## TERAS Decision P-07

**IMPLEMENT** time:
1. Duration and Instant
2. System time
3. Secure timestamps
4. Monotonic counters

### Architecture Decision ID: `TERAS-ARCH-P07-TIME-001`

---

# P-08: Concurrency Primitives

## Threading

```rust
// Thread spawning
fn spawn<F, T>(f: F) -> JoinHandle<T>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static;

struct JoinHandle<T> {
    thread: Thread,
    result: Arc<Mutex<Option<T>>>,
}

impl<T> JoinHandle<T> {
    fn join(self) -> Result<T, JoinError>;
    fn thread(&self) -> &Thread;
    fn is_finished(&self) -> bool;
}

// Thread-local storage
macro_rules! thread_local {
    ($($tt:tt)*) => { ... }
}
```

## Synchronization

```rust
// Mutex
struct Mutex<T> {
    inner: sys::Mutex,
    data: UnsafeCell<T>,
}

impl<T> Mutex<T> {
    fn new(t: T) -> Mutex<T>;
    fn lock(&self) -> LockResult<MutexGuard<'_, T>>;
    fn try_lock(&self) -> TryLockResult<MutexGuard<'_, T>>;
    fn into_inner(self) -> LockResult<T>;
    fn get_mut(&mut self) -> LockResult<&mut T>;
}

// RwLock
struct RwLock<T> {
    inner: sys::RwLock,
    data: UnsafeCell<T>,
}

impl<T> RwLock<T> {
    fn new(t: T) -> RwLock<T>;
    fn read(&self) -> LockResult<RwLockReadGuard<'_, T>>;
    fn write(&self) -> LockResult<RwLockWriteGuard<'_, T>>;
    fn try_read(&self) -> TryLockResult<RwLockReadGuard<'_, T>>;
    fn try_write(&self) -> TryLockResult<RwLockWriteGuard<'_, T>>;
}

// Condvar
struct Condvar {
    inner: sys::Condvar,
}

impl Condvar {
    fn new() -> Condvar;
    fn wait<'a, T>(&self, guard: MutexGuard<'a, T>) -> LockResult<MutexGuard<'a, T>>;
    fn wait_timeout<'a, T>(&self, guard: MutexGuard<'a, T>, dur: Duration) 
        -> LockResult<(MutexGuard<'a, T>, WaitTimeoutResult)>;
    fn notify_one(&self);
    fn notify_all(&self);
}

// Barrier
struct Barrier {
    lock: Mutex<BarrierState>,
    cvar: Condvar,
    num_threads: usize,
}

impl Barrier {
    fn new(n: usize) -> Barrier;
    fn wait(&self) -> BarrierWaitResult;
}
```

## Atomic Types

```rust
struct AtomicBool { ... }
struct AtomicI8 { ... }
struct AtomicI16 { ... }
struct AtomicI32 { ... }
struct AtomicI64 { ... }
struct AtomicIsize { ... }
struct AtomicU8 { ... }
struct AtomicU16 { ... }
struct AtomicU32 { ... }
struct AtomicU64 { ... }
struct AtomicUsize { ... }
struct AtomicPtr<T> { ... }

enum Ordering {
    Relaxed,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

impl AtomicUsize {
    fn new(v: usize) -> Self;
    fn load(&self, order: Ordering) -> usize;
    fn store(&self, val: usize, order: Ordering);
    fn swap(&self, val: usize, order: Ordering) -> usize;
    fn compare_exchange(&self, current: usize, new: usize, 
        success: Ordering, failure: Ordering) -> Result<usize, usize>;
    fn fetch_add(&self, val: usize, order: Ordering) -> usize;
    fn fetch_sub(&self, val: usize, order: Ordering) -> usize;
    fn fetch_and(&self, val: usize, order: Ordering) -> usize;
    fn fetch_or(&self, val: usize, order: Ordering) -> usize;
    fn fetch_xor(&self, val: usize, order: Ordering) -> usize;
}
```

## TERAS Decision P-08

**IMPLEMENT** concurrency:
1. Thread spawning
2. Sync primitives
3. Atomics
4. Security context propagation

### Architecture Decision ID: `TERAS-ARCH-P08-CONC-001`

---

# P-09: Security Primitives

## Cryptographic Types

```rust
// Key types
struct AesKey<const BITS: usize> {
    material: SecureBox<[u8; BITS / 8]>,
}

struct Ed25519PublicKey([u8; 32]);
struct Ed25519PrivateKey(SecureBox<[u8; 64]>);
struct X25519PublicKey([u8; 32]);
struct X25519PrivateKey(SecureBox<[u8; 32]>);

// Hash types
struct Sha256Hash([u8; 32]);
struct Sha512Hash([u8; 64]);
struct Blake3Hash([u8; 32]);

// Signature type
struct Signature(Vec<u8>);

// Cryptographic operations
fn sha256(data: &[u8]) -> Sha256Hash;
fn sha512(data: &[u8]) -> Sha512Hash;
fn blake3(data: &[u8]) -> Blake3Hash;

fn hmac_sha256(key: &[u8], data: &[u8]) -> [u8; 32];

fn ed25519_sign(key: &Ed25519PrivateKey, data: &[u8]) -> Signature;
fn ed25519_verify(key: &Ed25519PublicKey, data: &[u8], sig: &Signature) -> bool;
```

## Capability Types

```rust
// Capability definition
trait Capability: Copy + Clone + Eq + Hash {
    fn name(&self) -> &'static str;
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
enum SystemCapability {
    FileRead,
    FileWrite,
    NetworkConnect,
    NetworkListen,
    ProcessSpawn,
    CryptoSign,
    CryptoEncrypt,
    AuditRead,
    AuditWrite,
}

// Capability set
struct CapabilitySet {
    bits: u64,
}

impl CapabilitySet {
    fn empty() -> Self;
    fn all() -> Self;
    fn insert(&mut self, cap: impl Capability);
    fn remove(&mut self, cap: impl Capability);
    fn contains(&self, cap: impl Capability) -> bool;
    fn union(&self, other: &Self) -> Self;
    fn intersection(&self, other: &Self) -> Self;
}
```

## IFC Types

```rust
// Security labels
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
enum SecurityLevel {
    Public = 0,
    Internal = 1,
    Confidential = 2,
    Secret = 3,
    TopSecret = 4,
}

struct Label {
    level: SecurityLevel,
    compartments: CompartmentSet,
}

impl Label {
    fn flows_to(&self, other: &Label) -> bool {
        self.level <= other.level && self.compartments.is_subset(&other.compartments)
    }
    
    fn join(&self, other: &Label) -> Label {
        Label {
            level: self.level.max(other.level),
            compartments: self.compartments.union(&other.compartments),
        }
    }
    
    fn meet(&self, other: &Label) -> Label {
        Label {
            level: self.level.min(other.level),
            compartments: self.compartments.intersection(&other.compartments),
        }
    }
}

// Labeled value
struct Labeled<T, L: Label> {
    value: T,
    label: L,
}

impl<T, L: Label> Labeled<T, L> {
    fn new(value: T, label: L) -> Self {
        Labeled { value, label }
    }
    
    fn unlabel(self) -> T
    where
        L: FlowsTo<CurrentPC>
    {
        self.value
    }
}
```

## Audit Types

```rust
// Audit event
trait AuditEvent: Serialize {
    fn event_type(&self) -> &'static str;
    fn severity(&self) -> Severity;
    fn timestamp(&self) -> SystemTime;
}

// Audit logger
struct AuditLogger {
    sink: Box<dyn AuditSink>,
}

impl AuditLogger {
    fn log<E: AuditEvent>(&self, event: E);
    fn flush(&self);
}

// Audit context
struct AuditContext {
    correlation_id: CorrelationId,
    session_id: Option<SessionId>,
    principal: Option<Principal>,
}

impl AuditContext {
    fn current() -> &'static AuditContext;
    fn with<T, F: FnOnce() -> T>(ctx: AuditContext, f: F) -> T;
}
```

## TERAS Decision P-09

**IMPLEMENT** security primitives:
1. Cryptographic types
2. Capability system
3. IFC labels
4. Audit infrastructure

### Architecture Decision ID: `TERAS-ARCH-P09-SEC-001`

---

# P-10: Product-Specific Extensions

## MENARA Extensions

```rust
// Mobile security types
mod menara {
    pub struct AppInfo {
        pub package_name: String,
        pub version: Version,
        pub permissions: Vec<Permission>,
        pub signatures: Vec<CertificateHash>,
    }
    
    pub struct ThreatAssessment {
        pub threat_level: ThreatLevel,
        pub indicators: Vec<ThreatIndicator>,
        pub recommendations: Vec<Action>,
    }
    
    pub trait MobileScanner {
        fn scan_app(&self, app: &AppInfo) -> ThreatAssessment;
        fn scan_network(&self) -> Vec<NetworkThreat>;
        fn verify_device_integrity(&self) -> IntegrityResult;
    }
}
```

## GAPURA Extensions

```rust
// WAF types
mod gapura {
    pub struct HttpRequest {
        pub method: Method,
        pub uri: Uri,
        pub headers: HeaderMap,
        pub body: Body,
    }
    
    pub struct WafRule {
        pub id: RuleId,
        pub pattern: Pattern,
        pub action: WafAction,
        pub severity: Severity,
    }
    
    pub enum WafDecision {
        Allow,
        Block(BlockReason),
        RateLimit(Duration),
        Challenge(ChallengeType),
    }
    
    pub trait WafEngine {
        fn check(&self, request: &HttpRequest) -> WafDecision;
        fn reload_rules(&mut self, rules: Vec<WafRule>);
    }
}
```

## ZIRAH Extensions

```rust
// EDR types
mod zirah {
    pub struct FileEvent {
        pub path: PathBuf,
        pub operation: FileOperation,
        pub process: ProcessInfo,
        pub timestamp: Instant,
    }
    
    pub struct ScanResult {
        pub path: PathBuf,
        pub verdict: Verdict,
        pub signatures: Vec<SignatureMatch>,
        pub behavior: Vec<BehaviorIndicator>,
    }
    
    pub trait EndpointScanner {
        fn scan_file(&self, path: &Path) -> ScanResult;
        fn scan_memory(&self, pid: ProcessId) -> ScanResult;
        fn quarantine(&self, path: &Path) -> Result<(), QuarantineError>;
    }
}
```

## BENTENG Extensions

```rust
// eKYC types
mod benteng {
    pub struct DocumentImage {
        pub image: Image,
        pub document_type: DocumentType,
    }
    
    pub struct FaceMatch {
        pub confidence: f64,
        pub landmarks: Vec<Landmark>,
    }
    
    pub struct VerificationResult {
        pub face_match: FaceMatch,
        pub document_valid: bool,
        pub liveness_score: f64,
        pub ocr_data: DocumentData,
    }
    
    pub trait EkycVerifier {
        fn verify_face(&self, selfie: &Image, document: &DocumentImage) -> FaceMatch;
        fn verify_liveness(&self, frames: &[Image]) -> LivenessResult;
        fn extract_document(&self, document: &DocumentImage) -> DocumentData;
    }
}
```

## SANDI Extensions

```rust
// Digital signature types
mod sandi {
    pub struct SignatureRequest {
        pub data: Vec<u8>,
        pub certificate: Certificate,
        pub timestamp: bool,
    }
    
    pub struct SignedDocument {
        pub signature: Signature,
        pub certificate_chain: Vec<Certificate>,
        pub timestamp: Option<Timestamp>,
    }
    
    pub struct VerificationResult {
        pub valid: bool,
        pub signer: Certificate,
        pub timestamp: Option<DateTime>,
        pub revocation_status: RevocationStatus,
    }
    
    pub trait SignatureService {
        fn sign(&self, request: SignatureRequest) -> Result<SignedDocument, SignError>;
        fn verify(&self, document: &SignedDocument) -> VerificationResult;
    }
}
```

## TERAS Decision P-10

**IMPLEMENT** product extensions:
1. Product-specific types
2. Domain traits
3. Integration points
4. Extension APIs

### Architecture Decision ID: `TERAS-ARCH-P10-PROD-001`

---

# Domain P Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| P-01 | Foundations | TERAS-ARCH-P01-STD-001 |
| P-02 | Core Types | TERAS-ARCH-P02-CORE-001 |
| P-03 | Collections | TERAS-ARCH-P03-COLL-001 |
| P-04 | Strings | TERAS-ARCH-P04-STR-001 |
| P-05 | I/O | TERAS-ARCH-P05-IO-001 |
| P-06 | Networking | TERAS-ARCH-P06-NET-001 |
| P-07 | Time | TERAS-ARCH-P07-TIME-001 |
| P-08 | Concurrency | TERAS-ARCH-P08-CONC-001 |
| P-09 | Security | TERAS-ARCH-P09-SEC-001 |
| P-10 | Products | TERAS-ARCH-P10-PROD-001 |

## Domain P: COMPLETE

---

*Research Track Output — Domain P: Standard Library Design*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
