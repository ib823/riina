# TERAS-LANG Research Domain H: Concurrency and Parallelism

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-H-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | H-01 through H-10 |
| Domain | H: Concurrency and Parallelism |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# H-01: Concurrency Foundations

## Executive Summary

Concurrency in security-critical systems requires eliminating data races, preventing deadlocks, and ensuring deterministic behavior for security properties. TERAS-LANG must provide safe concurrency primitives that maintain security invariants across thread boundaries.

## Concurrency vs Parallelism

```
Concurrency: Multiple logical threads of control
    - Interleaving execution
    - Shared state management
    - Synchronization primitives

Parallelism: Simultaneous execution
    - Multiple cores/processors
    - Data parallelism
    - Task parallelism

TERAS requires both:
    - Concurrent request handling (GAPURA, BENTENG)
    - Parallel scanning (ZIRAH)
    - Async I/O (all products)
```

## Concurrency Hazards

```
Data Races:
    Thread 1: read x → compute → write x
    Thread 2: read x → compute → write x
    Result: Lost update, inconsistent state

Race Conditions:
    Thread 1: if (authorized) { access_resource(); }
    Thread 2: revoke_authorization();
    Result: TOCTOU vulnerability

Deadlocks:
    Thread 1: lock(A) → lock(B)
    Thread 2: lock(B) → lock(A)
    Result: System hang

Priority Inversion:
    High-priority blocked by low-priority holding lock
    Result: Timing vulnerabilities
```

## TERAS Concurrency Model

```rust
// Data race prevention via ownership
fn safe_concurrent() {
    let data = vec![1, 2, 3, 4];
    
    // Move to thread - no sharing
    let handle = spawn(move || {
        process(data)  // data owned by thread
    });
    
    // data not accessible here - moved
}

// Shared state via synchronized types
fn shared_state() {
    let counter = Arc::new(Mutex::new(0));
    let counter2 = counter.clone();
    
    let h1 = spawn(move || {
        let mut c = counter.lock();
        *c += 1;
    });
    
    let h2 = spawn(move || {
        let mut c = counter2.lock();
        *c += 1;
    });
}
```

## TERAS Decision H-01

**IMPLEMENT** safe concurrency:
1. Ownership-based data race prevention
2. Send/Sync marker traits
3. No implicit sharing
4. Explicit synchronization

### Architecture Decision ID: `TERAS-ARCH-H01-CON-001`

---

# H-02: Send and Sync Markers

## Marker Trait Design

```rust
// Send: Safe to transfer between threads
// A type is Send if it can be sent to another thread
unsafe trait Send {}

// Sync: Safe to share references between threads
// A type is Sync if &T is Send
unsafe trait Sync {}

// Relationships
// T: Sync ⟹ &T: Send
// T: Send + Copy ⟹ T: Sync (for most types)
```

## Automatic Derivation

```rust
// Primitives are Send + Sync
impl Send for i32 {}
impl Sync for i32 {}

// Composite types derive from components
struct Point { x: i32, y: i32 }
// Point: Send + Sync (both fields are)

struct Container<T> { value: T }
// Container<T>: Send iff T: Send
// Container<T>: Sync iff T: Sync
```

## Non-Send/Sync Types

```rust
// Rc is not Send (non-atomic refcount)
struct Rc<T> { ... }
impl<T> !Send for Rc<T> {}

// Cell is not Sync (interior mutability without sync)
struct Cell<T> { ... }
impl<T> !Sync for Cell<T> {}

// Raw pointers are neither by default
impl<T> !Send for *const T {}
impl<T> !Sync for *const T {}
```

## TERAS Security Extensions

```rust
// Security label must be preserved across threads
trait SecureSend: Send {
    type Label: SecurityLabel;
}

// Thread-local security context
struct ThreadSecurityContext {
    clearance: Clearance,
    capabilities: CapabilitySet,
    audit_context: AuditContext,
}

// Spawn with security context
fn secure_spawn<F, T>(f: F) -> JoinHandle<T>
where
    F: FnOnce() -> T + SecureSend,
    T: SecureSend,
{
    let ctx = ThreadSecurityContext::current();
    spawn(move || {
        ThreadSecurityContext::set(ctx);
        f()
    })
}
```

## TERAS Decision H-02

**IMPLEMENT** Send/Sync:
1. Rust-style marker traits
2. Automatic derivation
3. Security context propagation
4. Capability transfer rules

### Architecture Decision ID: `TERAS-ARCH-H02-SS-001`

---

# H-03: Synchronization Primitives

## Mutex

```rust
// Mutex with poison detection
struct Mutex<T> {
    inner: sys::Mutex,
    data: UnsafeCell<T>,
    poisoned: AtomicBool,
}

impl<T> Mutex<T> {
    fn lock(&self) -> LockResult<MutexGuard<T>> {
        self.inner.lock();
        if self.poisoned.load(Ordering::Acquire) {
            Err(PoisonError::new(MutexGuard::new(self)))
        } else {
            Ok(MutexGuard::new(self))
        }
    }
    
    fn try_lock(&self) -> TryLockResult<MutexGuard<T>> {
        if self.inner.try_lock() {
            // ... similar to lock
        } else {
            Err(TryLockError::WouldBlock)
        }
    }
}

// RAII guard
struct MutexGuard<'a, T> {
    mutex: &'a Mutex<T>,
}

impl<T> Drop for MutexGuard<'_, T> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.mutex.poisoned.store(true, Ordering::Release);
        }
        self.mutex.inner.unlock();
    }
}
```

## RwLock

```rust
// Read-Write Lock
struct RwLock<T> {
    inner: sys::RwLock,
    data: UnsafeCell<T>,
}

impl<T> RwLock<T> {
    fn read(&self) -> LockResult<RwLockReadGuard<T>> {
        self.inner.read_lock();
        Ok(RwLockReadGuard::new(self))
    }
    
    fn write(&self) -> LockResult<RwLockWriteGuard<T>> {
        self.inner.write_lock();
        Ok(RwLockWriteGuard::new(self))
    }
}

// Multiple readers OR one writer
// Readers: Sync access, no mutation
// Writer: Exclusive access, can mutate
```

## Condition Variables

```rust
// Condvar for waiting
struct Condvar {
    inner: sys::Condvar,
}

impl Condvar {
    fn wait<'a, T>(&self, guard: MutexGuard<'a, T>) -> LockResult<MutexGuard<'a, T>> {
        // Release mutex, wait, reacquire
        self.inner.wait(guard.mutex.inner);
        Ok(guard)
    }
    
    fn wait_while<'a, T, F>(
        &self,
        mut guard: MutexGuard<'a, T>,
        mut condition: F
    ) -> LockResult<MutexGuard<'a, T>>
    where
        F: FnMut(&mut T) -> bool,
    {
        while condition(&mut *guard) {
            guard = self.wait(guard)?;
        }
        Ok(guard)
    }
    
    fn notify_one(&self) { self.inner.notify_one(); }
    fn notify_all(&self) { self.inner.notify_all(); }
}
```

## TERAS Security-Aware Locks

```rust
// Lock with capability requirement
struct CapabilityMutex<T, C: Capability> {
    mutex: Mutex<T>,
    _cap: PhantomData<C>,
}

impl<T, C: Capability> CapabilityMutex<T, C> {
    fn lock(&self) -> LockResult<MutexGuard<T>>
    where
        CurrentContext: HasCapability<C>
    {
        self.mutex.lock()
    }
}

// Lock with audit
struct AuditedMutex<T> {
    mutex: Mutex<T>,
    name: &'static str,
}

impl<T> AuditedMutex<T> {
    fn lock(&self) -> LockResult<AuditedMutexGuard<T>> {
        let start = Instant::now();
        let guard = self.mutex.lock();
        Audit::log(LockAcquired {
            name: self.name,
            wait_time: start.elapsed(),
        });
        guard.map(|g| AuditedMutexGuard { guard: g, name: self.name })
    }
}
```

## TERAS Decision H-03

**IMPLEMENT** synchronization:
1. RAII-based guards
2. Poison detection
3. RwLock for readers/writer
4. Capability-protected locks
5. Audit integration

### Architecture Decision ID: `TERAS-ARCH-H03-SYNC-001`

---

# H-04: Atomic Operations

## Atomic Types

```rust
// Atomic primitives
struct AtomicBool { v: UnsafeCell<u8> }
struct AtomicI32 { v: UnsafeCell<i32> }
struct AtomicI64 { v: UnsafeCell<i64> }
struct AtomicUsize { v: UnsafeCell<usize> }
struct AtomicPtr<T> { p: UnsafeCell<*mut T> }

impl AtomicI64 {
    fn load(&self, order: Ordering) -> i64;
    fn store(&self, val: i64, order: Ordering);
    fn swap(&self, val: i64, order: Ordering) -> i64;
    fn compare_exchange(
        &self,
        current: i64,
        new: i64,
        success: Ordering,
        failure: Ordering
    ) -> Result<i64, i64>;
    fn fetch_add(&self, val: i64, order: Ordering) -> i64;
    fn fetch_sub(&self, val: i64, order: Ordering) -> i64;
    fn fetch_and(&self, val: i64, order: Ordering) -> i64;
    fn fetch_or(&self, val: i64, order: Ordering) -> i64;
    fn fetch_xor(&self, val: i64, order: Ordering) -> i64;
}
```

## Memory Ordering

```rust
enum Ordering {
    // No ordering constraints
    Relaxed,
    
    // Acquire: Reads after this see writes before Release
    Acquire,
    
    // Release: Writes before this are seen after Acquire
    Release,
    
    // Both Acquire and Release
    AcqRel,
    
    // Total ordering (sequential consistency)
    SeqCst,
}

// Example: Lock-free queue
struct Queue<T> {
    head: AtomicPtr<Node<T>>,
    tail: AtomicPtr<Node<T>>,
}

impl<T> Queue<T> {
    fn push(&self, value: T) {
        let node = Box::into_raw(Box::new(Node { value, next: AtomicPtr::new(null_mut()) }));
        loop {
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*tail).next.load(Ordering::Acquire) };
            if next.is_null() {
                if unsafe { (*tail).next.compare_exchange(
                    null_mut(), node, Ordering::Release, Ordering::Relaxed
                ).is_ok() } {
                    self.tail.compare_exchange(tail, node, Ordering::Release, Ordering::Relaxed);
                    return;
                }
            } else {
                self.tail.compare_exchange(tail, next, Ordering::Release, Ordering::Relaxed);
            }
        }
    }
}
```

## TERAS Security Atomics

```rust
// Atomic with constant-time operations for secrets
struct SecureAtomicU64 {
    value: AtomicU64,
}

impl SecureAtomicU64 {
    // Constant-time compare (for counters, etc.)
    fn ct_compare_exchange(&self, current: u64, new: u64) -> bool {
        // Uses compare_exchange but with constant-time comparison
        let result = self.value.compare_exchange(
            current, new, Ordering::SeqCst, Ordering::SeqCst
        );
        // Return in constant time
        let success = result.is_ok();
        let dummy = if success { new } else { current };
        compiler_fence(Ordering::SeqCst);
        success
    }
}

// Atomic capability counter
struct AtomicCapabilityRef {
    refcount: AtomicUsize,
    revoked: AtomicBool,
}

impl AtomicCapabilityRef {
    fn try_acquire(&self) -> Option<CapabilityGuard> {
        if self.revoked.load(Ordering::Acquire) {
            return None;
        }
        let old = self.refcount.fetch_add(1, Ordering::AcqRel);
        if self.revoked.load(Ordering::Acquire) {
            self.refcount.fetch_sub(1, Ordering::Release);
            return None;
        }
        Some(CapabilityGuard { inner: self })
    }
    
    fn revoke(&self) {
        self.revoked.store(true, Ordering::Release);
        // Wait for all users to release
        while self.refcount.load(Ordering::Acquire) > 0 {
            std::hint::spin_loop();
        }
    }
}
```

## TERAS Decision H-04

**IMPLEMENT** atomics:
1. Standard atomic types
2. Full memory ordering support
3. Lock-free data structures
4. Security-aware atomics

### Architecture Decision ID: `TERAS-ARCH-H04-ATM-001`

---

# H-05: Channels and Message Passing

## Channel Types

```rust
// Multi-producer, single-consumer (mpsc)
fn mpsc_channel<T>() -> (Sender<T>, Receiver<T>);

// Multi-producer, multi-consumer (mpmc)
fn mpmc_channel<T>(capacity: usize) -> (Sender<T>, Receiver<T>);

// Single-producer, single-consumer (spsc) - most efficient
fn spsc_channel<T>(capacity: usize) -> (Sender<T>, Receiver<T>);

// Oneshot - single value
fn oneshot<T>() -> (OneshotSender<T>, OneshotReceiver<T>);
```

## MPSC Implementation

```rust
struct Sender<T> {
    inner: Arc<ChannelInner<T>>,
}

struct Receiver<T> {
    inner: Arc<ChannelInner<T>>,
}

struct ChannelInner<T> {
    queue: Mutex<VecDeque<T>>,
    not_empty: Condvar,
    disconnected: AtomicBool,
}

impl<T> Sender<T> {
    fn send(&self, value: T) -> Result<(), SendError<T>> {
        if self.inner.disconnected.load(Ordering::Acquire) {
            return Err(SendError(value));
        }
        let mut queue = self.inner.queue.lock().unwrap();
        queue.push_back(value);
        self.inner.not_empty.notify_one();
        Ok(())
    }
}

impl<T> Receiver<T> {
    fn recv(&self) -> Result<T, RecvError> {
        let mut queue = self.inner.queue.lock().unwrap();
        loop {
            if let Some(value) = queue.pop_front() {
                return Ok(value);
            }
            if self.inner.disconnected.load(Ordering::Acquire) {
                return Err(RecvError);
            }
            queue = self.inner.not_empty.wait(queue).unwrap();
        }
    }
    
    fn try_recv(&self) -> Result<T, TryRecvError> {
        let mut queue = self.inner.queue.lock().unwrap();
        match queue.pop_front() {
            Some(value) => Ok(value),
            None if self.inner.disconnected.load(Ordering::Acquire) => 
                Err(TryRecvError::Disconnected),
            None => Err(TryRecvError::Empty),
        }
    }
}
```

## Typed Channels with Security

```rust
// Channel respects security labels
struct LabeledChannel<T, L: Label> {
    inner: Channel<T>,
    _label: PhantomData<L>,
}

impl<T, L: Label> LabeledChannel<T, L> {
    fn send(&self, value: T) -> Result<(), SendError<T>>
    where
        CurrentPC: FlowsTo<L>  // Can only send if PC ≤ Label
    {
        self.inner.send(value)
    }
    
    fn recv(&self) -> Result<T, RecvError>
    where
        L: FlowsTo<CurrentPC>  // Recv raises PC to Label
    {
        self.inner.recv()
    }
}

// Capability-protected channel
struct CapChannel<T, C: Capability> {
    inner: Channel<T>,
    _cap: PhantomData<C>,
}

impl<T, C: Capability> CapChannel<T, C> {
    fn send(&self, value: T) -> Result<(), SendError<T>>
    where
        CurrentContext: HasCapability<C>
    {
        Audit::log(ChannelSend { channel: type_name::<C>() });
        self.inner.send(value)
    }
}
```

## TERAS Decision H-05

**IMPLEMENT** channels:
1. MPSC as primary
2. Bounded and unbounded variants
3. Security label propagation
4. Capability protection
5. Audit integration

### Architecture Decision ID: `TERAS-ARCH-H05-CHAN-001`

---

# H-06: Async/Await

## Future Trait

```rust
trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

enum Poll<T> {
    Ready(T),
    Pending,
}

// Async function desugars to Future
async fn fetch_data(url: &str) -> Data {
    let response = http_get(url).await;
    parse(response)
}

// Equivalent to:
fn fetch_data(url: &str) -> impl Future<Output = Data> {
    async move {
        let response = http_get(url).await;
        parse(response)
    }
}
```

## Async Runtime

```rust
// Runtime executes futures
struct Runtime {
    scheduler: Scheduler,
    io_driver: IoDriver,
    timer_driver: TimerDriver,
}

impl Runtime {
    fn block_on<F: Future>(&self, future: F) -> F::Output {
        // Run future to completion
        let mut future = pin!(future);
        loop {
            let waker = self.create_waker();
            let mut cx = Context::from_waker(&waker);
            match future.as_mut().poll(&mut cx) {
                Poll::Ready(output) => return output,
                Poll::Pending => self.park(),
            }
        }
    }
    
    fn spawn<F>(&self, future: F) -> JoinHandle<F::Output>
    where
        F: Future + Send + 'static,
        F::Output: Send + 'static,
    {
        let task = Task::new(future);
        self.scheduler.schedule(task);
        task.handle()
    }
}
```

## TERAS Async Effects

```rust
// Async as effect
effect Async {
    fn spawn<T: Send>(future: impl Future<Output = T> + Send) -> JoinHandle<T>;
    fn yield_now();
    fn sleep(duration: Duration);
}

// Handler wraps runtime
handler tokio_handler for Async {
    spawn(future) resume => {
        let handle = tokio::spawn(future);
        resume(handle)
    }
    
    yield_now() resume => {
        tokio::task::yield_now().await;
        resume(())
    }
    
    sleep(duration) resume => {
        tokio::time::sleep(duration).await;
        resume(())
    }
}

// Security-aware async
effect SecureAsync {
    fn spawn_secure<T: SecureSend>(
        future: impl Future<Output = T> + SecureSend,
        clearance: Clearance
    ) -> SecureJoinHandle<T>;
}

handler secure_async_handler for SecureAsync {
    spawn_secure(future, clearance) resume => {
        let ctx = SecurityContext::current();
        if ctx.clearance < clearance {
            return Err(SecurityError::InsufficientClearance);
        }
        let handle = tokio::spawn(async move {
            SecurityContext::set_clearance(clearance);
            future.await
        });
        resume(SecureJoinHandle::new(handle, clearance))
    }
}
```

## TERAS Decision H-06

**IMPLEMENT** async:
1. Future-based model
2. Async as effect
3. Security context propagation
4. Clearance-aware spawning

### Architecture Decision ID: `TERAS-ARCH-H06-ASYNC-001`

---

# H-07: Structured Concurrency

## Scope-Based Spawning

```rust
// Scoped threads - all threads complete before scope exits
fn scoped<'env, F, R>(f: F) -> R
where
    F: FnOnce(&Scope<'env>) -> R,
{
    let scope = Scope::new();
    let result = f(&scope);
    scope.join_all();  // Wait for all spawned threads
    result
}

struct Scope<'env> {
    threads: Vec<JoinHandle<()>>,
    _marker: PhantomData<&'env mut &'env ()>,
}

impl<'env> Scope<'env> {
    fn spawn<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'env,  // Can borrow from 'env
    {
        // Safe: scope ensures thread completes before 'env ends
        let handle = unsafe { spawn_unchecked(f) };
        self.threads.push(handle);
    }
}

// Usage
fn process_data(data: &[Item]) {
    scoped(|s| {
        for chunk in data.chunks(100) {
            s.spawn(|| {
                // Can borrow chunk - lives long enough
                process_chunk(chunk);
            });
        }
    });
    // All threads completed, data can be dropped
}
```

## Async Structured Concurrency

```rust
// TaskGroup - structured async spawning
struct TaskGroup<'a, T> {
    tasks: Vec<JoinHandle<T>>,
    _scope: PhantomData<&'a ()>,
}

impl<'a, T: Send + 'static> TaskGroup<'a, T> {
    async fn spawn(&mut self, future: impl Future<Output = T> + Send + 'a) {
        let handle = tokio::spawn(future);
        self.tasks.push(handle);
    }
    
    async fn join_all(self) -> Vec<T> {
        let mut results = Vec::with_capacity(self.tasks.len());
        for task in self.tasks {
            results.push(task.await.unwrap());
        }
        results
    }
}

// Nursery pattern (from Trio)
async fn nursery<F, R>(f: F) -> R
where
    F: FnOnce(&mut Nursery) -> Pin<Box<dyn Future<Output = R> + Send>>,
{
    let mut nursery = Nursery::new();
    let result = f(&mut nursery).await;
    nursery.wait_all().await;
    result
}
```

## Cancellation

```rust
// Cancellation token
struct CancellationToken {
    cancelled: Arc<AtomicBool>,
    notify: Arc<Notify>,
}

impl CancellationToken {
    fn new() -> Self {
        Self {
            cancelled: Arc::new(AtomicBool::new(false)),
            notify: Arc::new(Notify::new()),
        }
    }
    
    fn cancel(&self) {
        self.cancelled.store(true, Ordering::Release);
        self.notify.notify_waiters();
    }
    
    fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }
    
    async fn cancelled(&self) {
        if self.is_cancelled() {
            return;
        }
        self.notify.notified().await;
    }
    
    fn child_token(&self) -> CancellationToken {
        // Child cancelled when parent is
        CancellationToken {
            cancelled: self.cancelled.clone(),
            notify: Arc::new(Notify::new()),
        }
    }
}

// Cancellable operation
async fn cancellable_operation(token: CancellationToken) -> Result<Data, Cancelled> {
    tokio::select! {
        result = do_work() => Ok(result),
        _ = token.cancelled() => Err(Cancelled),
    }
}
```

## TERAS Decision H-07

**IMPLEMENT** structured concurrency:
1. Scoped spawning
2. Task groups
3. Cancellation tokens
4. Parent-child relationships

### Architecture Decision ID: `TERAS-ARCH-H07-STRUCT-001`

---

# H-08: Parallel Iterators

## Parallel Iterator Trait

```rust
trait ParallelIterator: Sized {
    type Item;
    
    fn for_each<F>(self, f: F)
    where
        F: Fn(Self::Item) + Sync + Send;
    
    fn map<F, R>(self, f: F) -> Map<Self, F>
    where
        F: Fn(Self::Item) -> R + Sync + Send;
    
    fn filter<F>(self, f: F) -> Filter<Self, F>
    where
        F: Fn(&Self::Item) -> bool + Sync + Send;
    
    fn reduce<F>(self, identity: Self::Item, f: F) -> Self::Item
    where
        F: Fn(Self::Item, Self::Item) -> Self::Item + Sync + Send;
    
    fn collect<C>(self) -> C
    where
        C: FromParallelIterator<Self::Item>;
}

// Convert sequential to parallel
trait IntoParallelIterator {
    type Item;
    type Iter: ParallelIterator<Item = Self::Item>;
    
    fn into_par_iter(self) -> Self::Iter;
}

impl<T: Send> IntoParallelIterator for Vec<T> {
    type Item = T;
    type Iter = VecParIter<T>;
    
    fn into_par_iter(self) -> Self::Iter {
        VecParIter::new(self)
    }
}
```

## Work Stealing

```rust
// Work-stealing scheduler
struct WorkStealingPool {
    workers: Vec<Worker>,
    injector: Injector<Task>,
}

struct Worker {
    local: LocalQueue<Task>,
    stealers: Vec<Stealer<Task>>,
}

impl Worker {
    fn run(&self) {
        loop {
            // Try local queue first
            if let Some(task) = self.local.pop() {
                task.run();
                continue;
            }
            
            // Try to steal from others
            for stealer in &self.stealers {
                if let Some(task) = stealer.steal() {
                    task.run();
                    break;
                }
            }
            
            // Try global injector
            if let Some(task) = self.injector.steal() {
                task.run();
                continue;
            }
            
            // Park if no work
            self.park();
        }
    }
}
```

## Security-Aware Parallelism

```rust
// Parallel with security labels
trait SecureParallelIterator: ParallelIterator {
    fn for_each_secure<F, L: Label>(self, f: F)
    where
        F: Fn(Self::Item) + Sync + Send,
        Self::Item: HasLabel<L>;
}

// Deterministic parallelism for IFC
trait DeterministicParallelIterator: ParallelIterator {
    // No timing channels - deterministic scheduling
    fn for_each_det<F>(self, f: F)
    where
        F: Fn(Self::Item) + Sync + Send;
}

// Example: Parallel scan with audit
fn parallel_scan(files: Vec<FilePath>) -> Vec<ScanResult> {
    files.into_par_iter()
        .map(|path| {
            Audit::log(ScanStarted { path: &path });
            let result = scan_file(&path);
            Audit::log(ScanCompleted { path: &path, result: &result });
            result
        })
        .collect()
}
```

## TERAS Decision H-08

**IMPLEMENT** parallel iterators:
1. Rayon-style API
2. Work-stealing scheduler
3. Security context propagation
4. Deterministic mode for IFC

### Architecture Decision ID: `TERAS-ARCH-H08-PAR-001`

---

# H-09: Lock-Free Data Structures

## Lock-Free Stack

```rust
struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    value: T,
    next: *mut Node<T>,
}

impl<T> LockFreeStack<T> {
    fn push(&self, value: T) {
        let node = Box::into_raw(Box::new(Node {
            value,
            next: null_mut(),
        }));
        
        loop {
            let head = self.head.load(Ordering::Acquire);
            unsafe { (*node).next = head; }
            
            if self.head.compare_exchange(
                head, node, Ordering::Release, Ordering::Relaxed
            ).is_ok() {
                return;
            }
        }
    }
    
    fn pop(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            if head.is_null() {
                return None;
            }
            
            let next = unsafe { (*head).next };
            
            if self.head.compare_exchange(
                head, next, Ordering::Release, Ordering::Relaxed
            ).is_ok() {
                let value = unsafe { Box::from_raw(head).value };
                return Some(value);
            }
        }
    }
}
```

## Lock-Free Queue (Michael-Scott)

```rust
struct LockFreeQueue<T> {
    head: AtomicPtr<Node<T>>,
    tail: AtomicPtr<Node<T>>,
}

impl<T> LockFreeQueue<T> {
    fn new() -> Self {
        let sentinel = Box::into_raw(Box::new(Node {
            value: MaybeUninit::uninit(),
            next: AtomicPtr::new(null_mut()),
        }));
        Self {
            head: AtomicPtr::new(sentinel),
            tail: AtomicPtr::new(sentinel),
        }
    }
    
    fn enqueue(&self, value: T) {
        let node = Box::into_raw(Box::new(Node {
            value: MaybeUninit::new(value),
            next: AtomicPtr::new(null_mut()),
        }));
        
        loop {
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*tail).next.load(Ordering::Acquire) };
            
            if next.is_null() {
                if unsafe { (*tail).next.compare_exchange(
                    null_mut(), node, Ordering::Release, Ordering::Relaxed
                ).is_ok() } {
                    self.tail.compare_exchange(
                        tail, node, Ordering::Release, Ordering::Relaxed
                    );
                    return;
                }
            } else {
                self.tail.compare_exchange(
                    tail, next, Ordering::Release, Ordering::Relaxed
                );
            }
        }
    }
    
    fn dequeue(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*head).next.load(Ordering::Acquire) };
            
            if head == tail {
                if next.is_null() {
                    return None;
                }
                self.tail.compare_exchange(
                    tail, next, Ordering::Release, Ordering::Relaxed
                );
            } else {
                let value = unsafe { (*next).value.assume_init_read() };
                if self.head.compare_exchange(
                    head, next, Ordering::Release, Ordering::Relaxed
                ).is_ok() {
                    unsafe { drop(Box::from_raw(head)); }
                    return Some(value);
                }
            }
        }
    }
}
```

## Epoch-Based Reclamation

```rust
// Safe memory reclamation for lock-free structures
struct Epoch {
    global: AtomicUsize,
    local: ThreadLocal<LocalEpoch>,
    garbage: [Mutex<Vec<Garbage>>; 3],
}

impl Epoch {
    fn pin(&self) -> Guard {
        let local = self.local.get_or_create();
        local.enter(self.global.load(Ordering::Acquire));
        Guard { epoch: self, local }
    }
}

struct Guard<'a> {
    epoch: &'a Epoch,
    local: &'a LocalEpoch,
}

impl Drop for Guard<'_> {
    fn drop(&mut self) {
        self.local.exit();
        self.epoch.try_collect();
    }
}

impl Guard<'_> {
    fn defer_drop<T>(&self, ptr: *mut T) {
        self.epoch.add_garbage(Garbage::new(ptr));
    }
}
```

## TERAS Decision H-09

**IMPLEMENT** lock-free:
1. Standard lock-free structures
2. Epoch-based reclamation
3. Hazard pointers alternative
4. Verification of lock-freedom

### Architecture Decision ID: `TERAS-ARCH-H09-LF-001`

---

# H-10: Concurrency in TERAS Products

## MENARA (Mobile Security)

```rust
// Concurrent threat detection
async fn menara_monitor(config: MenaraConfig) -> ! {
    let (tx, rx) = mpsc::channel::<ThreatEvent>(1000);
    
    // Parallel monitors
    let monitors = vec![
        spawn(network_monitor(tx.clone())),
        spawn(app_monitor(tx.clone())),
        spawn(permission_monitor(tx.clone())),
    ];
    
    // Central threat processor
    while let Some(event) = rx.recv().await {
        let severity = assess_threat(&event).await;
        if severity >= Severity::High {
            alert_user(&event).await;
        }
        log_threat(&event).await;
    }
}
```

## GAPURA (WAF)

```rust
// High-concurrency request processing
async fn gapura_server(config: GapuraConfig) -> Result<(), Error> {
    let listener = TcpListener::bind(&config.addr).await?;
    let rules = Arc::new(RwLock::new(load_rules(&config)?));
    
    loop {
        let (stream, addr) = listener.accept().await?;
        let rules = rules.clone();
        
        spawn(async move {
            let rules = rules.read().await;
            match process_request(stream, &rules).await {
                Ok(response) => send_response(response).await,
                Err(blocked) => send_block_response(blocked).await,
            }
        });
    }
}

// Lock-free rate limiter
struct RateLimiter {
    buckets: DashMap<IpAddr, AtomicTokenBucket>,
}

impl RateLimiter {
    fn check(&self, ip: IpAddr) -> bool {
        self.buckets
            .entry(ip)
            .or_insert_with(|| AtomicTokenBucket::new(100, Duration::from_secs(1)))
            .try_consume(1)
    }
}
```

## ZIRAH (EDR)

```rust
// Parallel file scanning
fn zirah_scan(paths: Vec<PathBuf>, config: ZirahConfig) -> ScanReport {
    let progress = Arc::new(AtomicUsize::new(0));
    let threats = Arc::new(Mutex::new(Vec::new()));
    
    paths.into_par_iter()
        .for_each(|path| {
            if let Some(threat) = scan_file(&path, &config) {
                threats.lock().unwrap().push(threat);
            }
            progress.fetch_add(1, Ordering::Relaxed);
        });
    
    ScanReport {
        scanned: progress.load(Ordering::Acquire),
        threats: Arc::try_unwrap(threats).unwrap().into_inner().unwrap(),
    }
}
```

## BENTENG (eKYC)

```rust
// Concurrent verification pipeline
async fn benteng_verify(request: VerifyRequest) -> VerifyResult {
    // Parallel verification steps
    let (face_result, doc_result, liveness_result) = tokio::join!(
        verify_face(&request.selfie, &request.document_photo),
        verify_document(&request.document),
        verify_liveness(&request.liveness_frames),
    );
    
    // Aggregate results
    VerifyResult {
        face_match: face_result?,
        document_valid: doc_result?,
        is_live: liveness_result?,
    }
}
```

## SANDI (Digital Signatures)

```rust
// Concurrent signature verification
fn sandi_batch_verify(
    signatures: Vec<(Document, Signature, PublicKey)>
) -> Vec<VerifyResult> {
    signatures.into_par_iter()
        .map(|(doc, sig, pk)| {
            let hash = hash_document(&doc);
            verify_signature(&pk, &hash, &sig)
        })
        .collect()
}

// HSM connection pooling
struct HsmPool {
    connections: Vec<Mutex<HsmConnection>>,
    next: AtomicUsize,
}

impl HsmPool {
    async fn sign(&self, data: &[u8]) -> Signature {
        let idx = self.next.fetch_add(1, Ordering::Relaxed) % self.connections.len();
        let mut conn = self.connections[idx].lock().await;
        conn.sign(data).await
    }
}
```

## TERAS Decision H-10

**IMPLEMENT** product concurrency:
1. Product-specific patterns
2. Async for I/O bound (GAPURA, BENTENG)
3. Parallel for CPU bound (ZIRAH)
4. Connection pooling (SANDI)
5. Lock-free where performance critical

### Architecture Decision ID: `TERAS-ARCH-H10-PROD-001`

---

# Domain H Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| H-01 | Foundations | TERAS-ARCH-H01-CON-001 |
| H-02 | Send/Sync | TERAS-ARCH-H02-SS-001 |
| H-03 | Synchronization | TERAS-ARCH-H03-SYNC-001 |
| H-04 | Atomics | TERAS-ARCH-H04-ATM-001 |
| H-05 | Channels | TERAS-ARCH-H05-CHAN-001 |
| H-06 | Async/Await | TERAS-ARCH-H06-ASYNC-001 |
| H-07 | Structured | TERAS-ARCH-H07-STRUCT-001 |
| H-08 | Parallel | TERAS-ARCH-H08-PAR-001 |
| H-09 | Lock-Free | TERAS-ARCH-H09-LF-001 |
| H-10 | Products | TERAS-ARCH-H10-PROD-001 |

## Domain H: COMPLETE

---

*Research Track Output — Domain H: Concurrency and Parallelism*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
