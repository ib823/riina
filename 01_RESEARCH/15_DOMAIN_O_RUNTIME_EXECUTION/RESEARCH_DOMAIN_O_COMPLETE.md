# TERAS-LANG Research Domain O: Runtime and Execution Model

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-O-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | O-01 through O-10 |
| Domain | O: Runtime and Execution Model |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# O-01: Execution Model Foundations

## Executive Summary

The execution model defines how TERAS programs run, manage resources, and interact with the operating system. For security systems, the runtime must enforce security invariants, manage sensitive memory, and provide audit capabilities.

## Execution Models

```
1. Native Compilation (TERAS Primary)
   - Direct machine code
   - No runtime overhead
   - Full system access
   - Verified compilation

2. Managed Runtime (Not for TERAS)
   - Virtual machine
   - Garbage collection
   - Runtime checks
   - Portability

3. Hybrid
   - Native core + managed extensions
   - Sandboxed plugins
```

## TERAS Execution Architecture

```
┌─────────────────────────────────────────────────┐
│                 TERAS Application               │
├─────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────┐ │
│  │   Async     │  │   Effect    │  │  Audit  │ │
│  │   Runtime   │  │   Handlers  │  │  System │ │
│  └─────────────┘  └─────────────┘  └─────────┘ │
├─────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────┐ │
│  │   Memory    │  │  Security   │  │ Crypto  │ │
│  │   Manager   │  │   Context   │  │ Engine  │ │
│  └─────────────┘  └─────────────┘  └─────────┘ │
├─────────────────────────────────────────────────┤
│              Operating System                    │
├─────────────────────────────────────────────────┤
│                  Hardware                        │
└─────────────────────────────────────────────────┘
```

## Runtime Components

```rust
// Minimal runtime initialization
#[no_mangle]
pub extern "C" fn _teras_start() -> ! {
    // 1. Initialize security context
    security::init();
    
    // 2. Initialize memory manager
    memory::init();
    
    // 3. Initialize audit system
    audit::init();
    
    // 4. Initialize crypto
    crypto::init();
    
    // 5. Initialize async runtime
    async_runtime::init();
    
    // 6. Call main
    let result = main();
    
    // 7. Cleanup
    cleanup();
    
    // 8. Exit
    std::process::exit(result);
}
```

## TERAS Decision O-01

**IMPLEMENT** execution model:
1. Native compilation
2. Minimal runtime
3. Security-first initialization
4. Clean shutdown

### Architecture Decision ID: `TERAS-ARCH-O01-EXEC-001`

---

# O-02: Memory Management Runtime

## Secure Allocator

```rust
// Security-aware global allocator
struct SecureAllocator {
    inner: System,
    stats: AllocationStats,
}

unsafe impl GlobalAlloc for SecureAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = self.inner.alloc(layout);
        
        if !ptr.is_null() {
            // Zero memory on allocation
            std::ptr::write_bytes(ptr, 0, layout.size());
            
            // Track allocation
            self.stats.record_alloc(layout.size());
        }
        
        ptr
    }
    
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // Zero memory before deallocation
        std::ptr::write_bytes(ptr, 0, layout.size());
        
        // Track deallocation
        self.stats.record_dealloc(layout.size());
        
        self.inner.dealloc(ptr, layout);
    }
    
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let new_ptr = self.inner.realloc(ptr, layout, new_size);
        
        if !new_ptr.is_null() && new_size > layout.size() {
            // Zero new memory
            let new_bytes = new_ptr.add(layout.size());
            std::ptr::write_bytes(new_bytes, 0, new_size - layout.size());
        }
        
        new_ptr
    }
}

#[global_allocator]
static ALLOCATOR: SecureAllocator = SecureAllocator::new();
```

## Memory Pools

```rust
// Arena allocator for efficient allocation
struct Arena {
    chunks: Vec<Chunk>,
    current: *mut u8,
    end: *mut u8,
}

impl Arena {
    fn alloc<T>(&self) -> &mut T {
        let layout = Layout::new::<T>();
        let ptr = self.alloc_raw(layout);
        unsafe { &mut *(ptr as *mut T) }
    }
    
    fn alloc_raw(&self, layout: Layout) -> *mut u8 {
        let aligned = self.current.align_offset(layout.align());
        let ptr = unsafe { self.current.add(aligned) };
        let new_current = unsafe { ptr.add(layout.size()) };
        
        if new_current > self.end {
            self.grow();
            return self.alloc_raw(layout);
        }
        
        self.current = new_current;
        ptr
    }
    
    fn reset(&mut self) {
        // Zero all memory
        for chunk in &mut self.chunks {
            unsafe {
                std::ptr::write_bytes(chunk.ptr, 0, chunk.size);
            }
        }
        
        // Reset to first chunk
        if let Some(chunk) = self.chunks.first() {
            self.current = chunk.ptr;
            self.end = unsafe { chunk.ptr.add(chunk.size) };
        }
    }
}

// Secure arena with memory locking
struct SecureArena {
    arena: Arena,
    locked: bool,
}

impl SecureArena {
    fn new(size: usize) -> Self {
        let arena = Arena::with_capacity(size);
        
        // Lock memory
        unsafe {
            libc::mlock(arena.base_ptr() as *const _, size);
        }
        
        SecureArena { arena, locked: true }
    }
}

impl Drop for SecureArena {
    fn drop(&mut self) {
        // Zero before unlock and free
        self.arena.reset();
        
        if self.locked {
            unsafe {
                libc::munlock(self.arena.base_ptr() as *const _, self.arena.capacity());
            }
        }
    }
}
```

## TERAS Decision O-02

**IMPLEMENT** memory runtime:
1. Secure allocator
2. Zero on alloc/dealloc
3. Arena allocators
4. Memory locking

### Architecture Decision ID: `TERAS-ARCH-O02-MEM-001`

---

# O-03: Security Context Runtime

## Thread-Local Security Context

```rust
// Per-thread security context
thread_local! {
    static SECURITY_CONTEXT: RefCell<SecurityContext> = 
        RefCell::new(SecurityContext::default());
}

struct SecurityContext {
    // Current clearance level
    clearance: Clearance,
    
    // Active capabilities
    capabilities: CapabilitySet,
    
    // IFC program counter label
    pc_label: Label,
    
    // Audit context
    audit: AuditContext,
    
    // Principal identity
    principal: Option<Principal>,
}

impl SecurityContext {
    fn current() -> Ref<'static, SecurityContext> {
        SECURITY_CONTEXT.with(|ctx| ctx.borrow())
    }
    
    fn current_mut() -> RefMut<'static, SecurityContext> {
        SECURITY_CONTEXT.with(|ctx| ctx.borrow_mut())
    }
    
    fn with<T, F: FnOnce(&SecurityContext) -> T>(f: F) -> T {
        SECURITY_CONTEXT.with(|ctx| f(&ctx.borrow()))
    }
    
    fn with_mut<T, F: FnOnce(&mut SecurityContext) -> T>(f: F) -> T {
        SECURITY_CONTEXT.with(|ctx| f(&mut ctx.borrow_mut()))
    }
}
```

## Capability Runtime

```rust
// Runtime capability checking
impl SecurityContext {
    fn has_capability(&self, cap: Capability) -> bool {
        self.capabilities.contains(&cap)
    }
    
    fn require_capability(&self, cap: Capability) -> Result<(), SecurityError> {
        if self.has_capability(cap) {
            Audit::log(CapabilityUsed { capability: cap });
            Ok(())
        } else {
            Audit::log(CapabilityDenied { 
                capability: cap, 
                principal: self.principal.clone(),
            });
            Err(SecurityError::MissingCapability(cap))
        }
    }
    
    fn grant_capability(&mut self, cap: Capability) -> Result<CapabilityGuard, SecurityError> {
        // Check if we can grant this capability
        if !self.can_grant(&cap) {
            return Err(SecurityError::CannotGrantCapability(cap));
        }
        
        self.capabilities.insert(cap);
        Audit::log(CapabilityGranted { capability: cap });
        
        Ok(CapabilityGuard { cap })
    }
    
    fn revoke_capability(&mut self, cap: Capability) {
        self.capabilities.remove(&cap);
        Audit::log(CapabilityRevoked { capability: cap });
    }
}

struct CapabilityGuard {
    cap: Capability,
}

impl Drop for CapabilityGuard {
    fn drop(&mut self) {
        SecurityContext::with_mut(|ctx| {
            ctx.revoke_capability(self.cap);
        });
    }
}
```

## IFC Runtime

```rust
// Information flow control runtime
impl SecurityContext {
    fn check_flow(&self, from: &Label, to: &Label) -> bool {
        from.flows_to(to)
    }
    
    fn raise_pc(&mut self, label: &Label) {
        self.pc_label = self.pc_label.join(label);
    }
    
    fn check_read(&self, data_label: &Label) -> Result<(), IFCError> {
        // Reading raises PC
        if self.clearance.can_read(data_label) {
            Ok(())
        } else {
            Err(IFCError::ReadDenied {
                data_label: data_label.clone(),
                clearance: self.clearance,
            })
        }
    }
    
    fn check_write(&self, target_label: &Label) -> Result<(), IFCError> {
        // Writing requires PC ≤ target
        if self.pc_label.flows_to(target_label) {
            Ok(())
        } else {
            Err(IFCError::WriteDenied {
                pc_label: self.pc_label.clone(),
                target_label: target_label.clone(),
            })
        }
    }
}
```

## TERAS Decision O-03

**IMPLEMENT** security runtime:
1. Thread-local context
2. Capability checking
3. IFC enforcement
4. Audit integration

### Architecture Decision ID: `TERAS-ARCH-O03-SEC-001`

---

# O-04: Effect Handler Runtime

## Handler Stack

```rust
// Effect handler runtime
struct EffectRuntime {
    handler_stack: Vec<HandlerFrame>,
}

struct HandlerFrame {
    effect_id: TypeId,
    handler: Box<dyn AnyHandler>,
    resumption: Option<Resumption>,
}

impl EffectRuntime {
    fn perform<E: Effect>(&mut self, op: E::Operation) -> E::Result {
        // Find handler
        let frame = self.find_handler::<E>()
            .expect("No handler for effect");
        
        // Call handler
        let handler = frame.handler.downcast_ref::<E::Handler>().unwrap();
        handler.handle(op, &mut self.resumption_point())
    }
    
    fn find_handler<E: Effect>(&self) -> Option<&HandlerFrame> {
        let type_id = TypeId::of::<E>();
        self.handler_stack.iter().rev()
            .find(|f| f.effect_id == type_id)
    }
    
    fn install_handler<E: Effect, H: Handler<E>>(&mut self, handler: H) {
        self.handler_stack.push(HandlerFrame {
            effect_id: TypeId::of::<E>(),
            handler: Box::new(handler),
            resumption: None,
        });
    }
    
    fn uninstall_handler(&mut self) {
        self.handler_stack.pop();
    }
}

thread_local! {
    static EFFECT_RUNTIME: RefCell<EffectRuntime> = 
        RefCell::new(EffectRuntime::new());
}
```

## Continuation Management

```rust
// One-shot continuations
struct Continuation<T> {
    stack: StackSegment,
    result_slot: *mut MaybeUninit<T>,
    used: AtomicBool,
}

impl<T> Continuation<T> {
    fn resume(self, value: T) -> ! {
        // One-shot check
        if self.used.swap(true, Ordering::SeqCst) {
            panic!("Continuation already used");
        }
        
        // Store result
        unsafe {
            (*self.result_slot).write(value);
        }
        
        // Switch stack
        unsafe {
            switch_to_stack(self.stack);
        }
    }
}

// Multi-shot continuations (opt-in)
struct MultiContinuation<T> {
    stack: Arc<StackSegment>,
    result_slot: *mut MaybeUninit<T>,
}

impl<T> Clone for MultiContinuation<T> {
    fn clone(&self) -> Self {
        MultiContinuation {
            stack: Arc::new(self.stack.deep_copy()),
            result_slot: self.result_slot,
        }
    }
}
```

## TERAS Decision O-04

**IMPLEMENT** effect runtime:
1. Handler stack
2. One-shot continuations
3. Optional multi-shot
4. Efficient evidence passing

### Architecture Decision ID: `TERAS-ARCH-O04-EFF-001`

---

# O-05: Async Runtime

## Task Scheduler

```rust
// Async task runtime
struct AsyncRuntime {
    scheduler: Scheduler,
    io_driver: IoDriver,
    timer_driver: TimerDriver,
    worker_threads: Vec<WorkerThread>,
}

impl AsyncRuntime {
    fn block_on<F: Future>(&self, future: F) -> F::Output {
        let task = Task::new(future);
        self.scheduler.schedule(task.clone());
        
        loop {
            // Poll task
            if let Some(output) = task.try_take_output() {
                return output;
            }
            
            // Process I/O events
            self.io_driver.poll();
            
            // Process timers
            self.timer_driver.poll();
            
            // Run ready tasks
            while let Some(task) = self.scheduler.next_ready() {
                task.poll();
            }
            
            // Park if no work
            if self.scheduler.is_empty() {
                self.park();
            }
        }
    }
    
    fn spawn<F>(&self, future: F) -> JoinHandle<F::Output>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        let task = Task::new(future);
        let handle = task.handle();
        self.scheduler.schedule(task);
        handle
    }
}
```

## Work Stealing

```rust
// Work-stealing scheduler
struct WorkStealingScheduler {
    global_queue: Injector<Task>,
    local_queues: Vec<LocalQueue>,
    stealers: Vec<Stealer>,
}

impl WorkStealingScheduler {
    fn worker_loop(&self, id: usize) {
        let local = &self.local_queues[id];
        
        loop {
            // Try local queue
            if let Some(task) = local.pop() {
                self.run_task(task);
                continue;
            }
            
            // Try global queue
            if let Some(task) = self.global_queue.steal() {
                self.run_task(task);
                continue;
            }
            
            // Try stealing from others
            let mut rng = thread_rng();
            for _ in 0..self.stealers.len() {
                let victim = rng.gen_range(0..self.stealers.len());
                if victim != id {
                    if let Some(task) = self.stealers[victim].steal() {
                        self.run_task(task);
                        break;
                    }
                }
            }
            
            // Park if no work
            self.park(id);
        }
    }
}
```

## Security-Aware Async

```rust
// Security context propagation in async
struct SecureTask<F: Future> {
    future: F,
    security_context: SecurityContext,
}

impl<F: Future> Future for SecureTask<F> {
    type Output = F::Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // Install security context
        let _guard = SecurityContextGuard::install(&self.security_context);
        
        // Poll inner future
        let this = unsafe { self.get_unchecked_mut() };
        let future = unsafe { Pin::new_unchecked(&mut this.future) };
        future.poll(cx)
    }
}

fn spawn_secure<F>(future: F) -> JoinHandle<F::Output>
where
    F: Future + Send + 'static,
    F::Output: Send + 'static,
{
    let ctx = SecurityContext::current().clone();
    RUNTIME.spawn(SecureTask {
        future,
        security_context: ctx,
    })
}
```

## TERAS Decision O-05

**IMPLEMENT** async runtime:
1. Work-stealing scheduler
2. Security context propagation
3. Structured concurrency
4. I/O driver integration

### Architecture Decision ID: `TERAS-ARCH-O05-ASYNC-001`

---

# O-06: Audit Runtime

## Audit Logger

```rust
// High-performance audit logger
struct AuditLogger {
    buffer: RingBuffer<AuditEvent>,
    writer: AuditWriter,
    sequence: AtomicU64,
}

impl AuditLogger {
    fn log(&self, event: AuditEvent) {
        let seq = self.sequence.fetch_add(1, Ordering::SeqCst);
        
        let entry = AuditEntry {
            sequence: seq,
            timestamp: Timestamp::now(),
            event,
            context: AuditContext::current(),
        };
        
        // Non-blocking write to buffer
        if !self.buffer.try_push(entry) {
            // Buffer full - must block or drop
            self.handle_buffer_full(entry);
        }
    }
    
    fn flush(&self) {
        while let Some(entry) = self.buffer.pop() {
            self.writer.write(&entry);
        }
    }
}

// Async audit writer
struct AsyncAuditWriter {
    sender: mpsc::Sender<AuditEntry>,
    _worker: JoinHandle<()>,
}

impl AsyncAuditWriter {
    fn new(sink: impl AuditSink) -> Self {
        let (sender, receiver) = mpsc::channel(10000);
        
        let worker = std::thread::spawn(move || {
            let mut batch = Vec::with_capacity(100);
            
            loop {
                // Collect batch
                while batch.len() < 100 {
                    match receiver.recv_timeout(Duration::from_millis(10)) {
                        Ok(entry) => batch.push(entry),
                        Err(_) => break,
                    }
                }
                
                if !batch.is_empty() {
                    sink.write_batch(&batch);
                    batch.clear();
                }
            }
        });
        
        AsyncAuditWriter { sender, _worker: worker }
    }
}

// Global audit logger
static AUDIT: Lazy<AuditLogger> = Lazy::new(|| {
    AuditLogger::new(Config::from_env())
});

// Audit macro
macro_rules! audit {
    ($event:expr) => {
        AUDIT.log($event)
    };
}
```

## Structured Audit Events

```rust
// Audit event types
#[derive(Serialize)]
enum AuditEvent {
    // Authentication
    AuthAttempt { username: String, success: bool, ip: IpAddr },
    SessionCreated { session_id: SessionId, user_id: UserId },
    SessionDestroyed { session_id: SessionId, reason: String },
    
    // Authorization
    CapabilityUsed { capability: Capability, function: &'static str },
    CapabilityDenied { capability: Capability, principal: Principal },
    AccessGranted { resource: ResourceId, action: Action },
    AccessDenied { resource: ResourceId, action: Action, reason: String },
    
    // Cryptographic
    KeyGenerated { key_id: KeyId, algorithm: Algorithm },
    KeyUsed { key_id: KeyId, operation: CryptoOp },
    KeyDestroyed { key_id: KeyId },
    
    // Data
    DataAccessed { resource: ResourceId, label: Label },
    DataModified { resource: ResourceId, label: Label },
    DataExported { resource: ResourceId, destination: String },
    
    // System
    SystemStartup { version: String },
    SystemShutdown { reason: String },
    ConfigChanged { setting: String, old: String, new: String },
}
```

## TERAS Decision O-06

**IMPLEMENT** audit runtime:
1. Non-blocking logging
2. Async writer
3. Structured events
4. Guaranteed delivery

### Architecture Decision ID: `TERAS-ARCH-O06-AUDIT-001`

---

# O-07: Crypto Runtime

## Crypto Engine

```rust
// Cryptographic runtime
struct CryptoEngine {
    rng: SecureRng,
    key_store: KeyStore,
    algorithm_registry: AlgorithmRegistry,
}

impl CryptoEngine {
    fn init() -> Result<Self, CryptoError> {
        // Initialize RNG
        let rng = SecureRng::new()?;
        
        // Run self-tests
        Self::run_self_tests()?;
        
        // Initialize algorithm registry
        let registry = AlgorithmRegistry::default();
        
        Ok(CryptoEngine {
            rng,
            key_store: KeyStore::new(),
            algorithm_registry: registry,
        })
    }
    
    fn run_self_tests() -> Result<(), CryptoError> {
        // FIPS-style self-tests
        test_aes()?;
        test_sha256()?;
        test_hmac()?;
        test_ecdsa()?;
        test_rng()?;
        
        Ok(())
    }
    
    fn encrypt(&self, algorithm: Algorithm, key: &Key, data: &[u8]) -> Result<Vec<u8>, CryptoError> {
        // Validate key for algorithm
        self.algorithm_registry.validate_key(algorithm, key)?;
        
        // Get implementation
        let impl_ = self.algorithm_registry.get(algorithm)?;
        
        // Perform operation
        let nonce = self.rng.generate_nonce(impl_.nonce_size())?;
        let ciphertext = impl_.encrypt(key, &nonce, data)?;
        
        // Audit
        audit!(CryptoOperation { 
            operation: "encrypt",
            algorithm: algorithm.name(),
            data_size: data.len(),
        });
        
        Ok(ciphertext)
    }
}

thread_local! {
    static CRYPTO: RefCell<CryptoEngine> = RefCell::new(CryptoEngine::init().unwrap());
}
```

## Hardware Crypto Integration

```rust
// Hardware crypto detection and usage
struct HardwareCrypto {
    aes_ni: bool,
    sha_ni: bool,
    arm_crypto: bool,
    rdrand: bool,
}

impl HardwareCrypto {
    fn detect() -> Self {
        #[cfg(target_arch = "x86_64")]
        {
            let cpuid = raw_cpuid::CpuId::new();
            let features = cpuid.get_feature_info().unwrap();
            
            HardwareCrypto {
                aes_ni: features.has_aesni(),
                sha_ni: cpuid.get_extended_feature_info()
                    .map(|f| f.has_sha()).unwrap_or(false),
                arm_crypto: false,
                rdrand: features.has_rdrand(),
            }
        }
        
        #[cfg(target_arch = "aarch64")]
        {
            HardwareCrypto {
                aes_ni: false,
                sha_ni: false,
                arm_crypto: std::arch::is_aarch64_feature_detected!("aes"),
                rdrand: false,
            }
        }
    }
    
    fn aes_encrypt(&self, key: &[u8], block: &mut [u8; 16]) {
        if self.aes_ni {
            unsafe { aes_ni_encrypt(key, block); }
        } else if self.arm_crypto {
            unsafe { arm_aes_encrypt(key, block); }
        } else {
            software_aes_encrypt(key, block);
        }
    }
}
```

## TERAS Decision O-07

**IMPLEMENT** crypto runtime:
1. Self-testing
2. Algorithm registry
3. Hardware acceleration
4. Key management

### Architecture Decision ID: `TERAS-ARCH-O07-CRYPTO-001`

---

# O-08: Error Handling Runtime

## Panic Handler

```rust
// Custom panic handler
#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    // Log panic
    if let Some(location) = info.location() {
        eprintln!("Panic at {}:{}:{}", 
            location.file(), location.line(), location.column());
    }
    
    if let Some(message) = info.message() {
        eprintln!("Message: {}", message);
    }
    
    // Audit panic
    AUDIT.log_sync(AuditEvent::Panic {
        location: info.location().map(|l| l.to_string()),
        message: info.message().map(|m| m.to_string()),
    });
    
    // Secure cleanup
    secure_cleanup();
    
    // Abort
    std::process::abort();
}

fn secure_cleanup() {
    // Zeroize sensitive data
    CRYPTO.with(|c| c.borrow_mut().zeroize_all());
    
    // Flush audit log
    AUDIT.flush_sync();
    
    // Close secure connections
    close_all_sessions();
}
```

## Out of Memory Handler

```rust
// OOM handler
#[alloc_error_handler]
fn oom_handler(layout: Layout) -> ! {
    // Log OOM
    eprintln!("Out of memory: requested {} bytes", layout.size());
    
    // Audit
    AUDIT.log_sync(AuditEvent::OutOfMemory {
        requested_size: layout.size(),
    });
    
    // Try to free non-essential memory
    if try_free_memory(layout.size()) {
        // Retry allocation
        // (Not possible in standard handler, would need custom allocator)
    }
    
    // Secure cleanup and abort
    secure_cleanup();
    std::process::abort();
}
```

## Stack Overflow Handler

```rust
// Stack overflow detection
#[cfg(unix)]
fn install_stack_guard() {
    use libc::{sigaction, sigaltstack, SIGSEGV, SA_ONSTACK, SA_SIGINFO};
    
    // Allocate alternate signal stack
    let stack_size = 64 * 1024;
    let stack = unsafe { libc::mmap(
        std::ptr::null_mut(),
        stack_size,
        libc::PROT_READ | libc::PROT_WRITE,
        libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
        -1,
        0,
    ) };
    
    let ss = libc::stack_t {
        ss_sp: stack,
        ss_flags: 0,
        ss_size: stack_size,
    };
    
    unsafe { sigaltstack(&ss, std::ptr::null_mut()); }
    
    // Install handler
    let mut sa: sigaction = unsafe { std::mem::zeroed() };
    sa.sa_flags = SA_ONSTACK | SA_SIGINFO;
    sa.sa_sigaction = stack_overflow_handler as usize;
    
    unsafe { sigaction(SIGSEGV, &sa, std::ptr::null_mut()); }
}

extern "C" fn stack_overflow_handler(sig: i32, info: *mut libc::siginfo_t, _ctx: *mut libc::c_void) {
    // Check if this is stack overflow
    let si_addr = unsafe { (*info).si_addr() };
    
    if is_stack_address(si_addr) {
        eprintln!("Stack overflow detected");
        AUDIT.log_sync(AuditEvent::StackOverflow);
        secure_cleanup();
        std::process::abort();
    }
    
    // Not stack overflow, re-raise
    unsafe { libc::raise(sig); }
}
```

## TERAS Decision O-08

**IMPLEMENT** error runtime:
1. Custom panic handler
2. OOM handling
3. Stack overflow detection
4. Secure cleanup

### Architecture Decision ID: `TERAS-ARCH-O08-ERR-001`

---

# O-09: Signal Handling

## Signal Handler

```rust
// Signal handling for graceful shutdown
struct SignalHandler {
    shutdown: AtomicBool,
    handlers: Mutex<HashMap<Signal, Box<dyn Fn() + Send + Sync>>>,
}

impl SignalHandler {
    fn install() -> Arc<Self> {
        let handler = Arc::new(SignalHandler {
            shutdown: AtomicBool::new(false),
            handlers: Mutex::new(HashMap::new()),
        });
        
        // Install signal handlers
        #[cfg(unix)]
        {
            use signal_hook::consts::*;
            
            signal_hook::flag::register(SIGTERM, handler.shutdown.clone())?;
            signal_hook::flag::register(SIGINT, handler.shutdown.clone())?;
            
            // Custom handler for SIGHUP (reload config)
            let h = handler.clone();
            signal_hook::low_level::register(SIGHUP, move || {
                h.handle_signal(Signal::SIGHUP);
            })?;
        }
        
        handler
    }
    
    fn on_signal<F: Fn() + Send + Sync + 'static>(&self, signal: Signal, handler: F) {
        self.handlers.lock().unwrap().insert(signal, Box::new(handler));
    }
    
    fn is_shutdown(&self) -> bool {
        self.shutdown.load(Ordering::SeqCst)
    }
    
    fn handle_signal(&self, signal: Signal) {
        audit!(SignalReceived { signal });
        
        if let Some(handler) = self.handlers.lock().unwrap().get(&signal) {
            handler();
        }
    }
}

// Graceful shutdown
async fn graceful_shutdown(handler: Arc<SignalHandler>) {
    // Wait for shutdown signal
    while !handler.is_shutdown() {
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    
    audit!(ShutdownInitiated);
    
    // Stop accepting new requests
    // ...
    
    // Wait for in-flight requests
    // ...
    
    // Cleanup
    secure_cleanup();
    
    audit!(ShutdownComplete);
}
```

## TERAS Decision O-09

**IMPLEMENT** signal handling:
1. Graceful shutdown
2. Config reload
3. Audit all signals
4. Secure cleanup

### Architecture Decision ID: `TERAS-ARCH-O09-SIG-001`

---

# O-10: Runtime in TERAS Products

## MENARA Runtime

```rust
// Mobile runtime
struct MenaraRuntime {
    scanner_pool: ThreadPool,
    network_monitor: NetworkMonitor,
    notification_service: NotificationService,
}

impl MenaraRuntime {
    fn init() -> Self {
        // Low-power initialization for mobile
        let scanner_pool = ThreadPool::with_threads(2);  // Limited threads
        
        MenaraRuntime {
            scanner_pool,
            network_monitor: NetworkMonitor::new(),
            notification_service: NotificationService::new(),
        }
    }
    
    fn start_background_scan(&self) {
        self.scanner_pool.execute(|| {
            while !SHUTDOWN.load(Ordering::SeqCst) {
                scan_installed_apps();
                std::thread::sleep(Duration::from_secs(3600));  // Hourly
            }
        });
    }
}
```

## GAPURA Runtime

```rust
// WAF runtime
struct GapuraRuntime {
    acceptor: TcpAcceptor,
    worker_pool: WorkStealingPool,
    rule_engine: Arc<RwLock<RuleEngine>>,
    rate_limiter: RateLimiter,
}

impl GapuraRuntime {
    async fn run(&self) -> Result<(), Error> {
        loop {
            let conn = self.acceptor.accept().await?;
            let rules = self.rule_engine.clone();
            let limiter = self.rate_limiter.clone();
            
            self.worker_pool.spawn(async move {
                let result = process_request(conn, &rules, &limiter).await;
                if let Err(e) = result {
                    audit!(RequestError { error: e });
                }
            });
        }
    }
}
```

## ZIRAH Runtime

```rust
// EDR runtime
struct ZirahRuntime {
    file_monitor: FileMonitor,
    process_monitor: ProcessMonitor,
    scanner: ParallelScanner,
    quarantine: QuarantineService,
}

impl ZirahRuntime {
    fn start(&self) {
        // Start file system monitoring
        self.file_monitor.start(|event| {
            if let FileEvent::Created(path) | FileEvent::Modified(path) = event {
                self.scanner.queue_scan(&path);
            }
        });
        
        // Start process monitoring
        self.process_monitor.start(|event| {
            if let ProcessEvent::Started(pid) = event {
                self.analyze_process(pid);
            }
        });
    }
}
```

## BENTENG Runtime

```rust
// eKYC runtime
struct BentengRuntime {
    face_engine: FaceEngine,
    ocr_engine: OcrEngine,
    liveness_checker: LivenessChecker,
    session_manager: SessionManager,
}

impl BentengRuntime {
    async fn verify(&self, session_id: SessionId) -> VerificationResult {
        let session = self.session_manager.get(&session_id)?;
        
        // Parallel verification steps
        let (face_result, doc_result, liveness_result) = tokio::join!(
            self.face_engine.match_faces(&session.selfie, &session.document_photo),
            self.ocr_engine.extract(&session.document),
            self.liveness_checker.check(&session.liveness_frames),
        );
        
        VerificationResult {
            face_match: face_result?,
            document_data: doc_result?,
            is_live: liveness_result?,
        }
    }
}
```

## SANDI Runtime

```rust
// Digital signature runtime
struct SandiRuntime {
    hsm_pool: HsmConnectionPool,
    cert_store: CertificateStore,
    tsa_client: TsaClient,
    key_cache: KeyCache,
}

impl SandiRuntime {
    async fn sign(&self, request: SignRequest) -> Result<Signature, SandiError> {
        // Get key from HSM
        let hsm = self.hsm_pool.get().await?;
        
        // Sign
        let signature = hsm.sign(&request.key_id, &request.data).await?;
        
        // Timestamp if required
        let timestamp = if request.timestamp {
            Some(self.tsa_client.timestamp(&signature).await?)
        } else {
            None
        };
        
        Ok(Signature {
            value: signature,
            timestamp,
            certificate: self.cert_store.get(&request.key_id)?,
        })
    }
}
```

## TERAS Decision O-10

**IMPLEMENT** product runtimes:
1. Product-specific optimization
2. Resource management
3. Service integration
4. Performance tuning

### Architecture Decision ID: `TERAS-ARCH-O10-PROD-001`

---

# Domain O Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| O-01 | Foundations | TERAS-ARCH-O01-EXEC-001 |
| O-02 | Memory | TERAS-ARCH-O02-MEM-001 |
| O-03 | Security | TERAS-ARCH-O03-SEC-001 |
| O-04 | Effects | TERAS-ARCH-O04-EFF-001 |
| O-05 | Async | TERAS-ARCH-O05-ASYNC-001 |
| O-06 | Audit | TERAS-ARCH-O06-AUDIT-001 |
| O-07 | Crypto | TERAS-ARCH-O07-CRYPTO-001 |
| O-08 | Errors | TERAS-ARCH-O08-ERR-001 |
| O-09 | Signals | TERAS-ARCH-O09-SIG-001 |
| O-10 | Products | TERAS-ARCH-O10-PROD-001 |

## Domain O: COMPLETE

---

*Research Track Output — Domain O: Runtime and Execution Model*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
