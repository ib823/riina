# TERAS-LANG Research Domain L: Foreign Function Interface

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-L-COMPLETE |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Sessions | L-01 through L-10 |
| Domain | L: Foreign Function Interface |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# L-01: FFI Foundations

## Executive Summary

Foreign Function Interface (FFI) enables TERAS code to interact with external libraries written in C, C++, or other languages. For security systems, FFI is both essential (for OS APIs, hardware interfaces) and dangerous (unsafe boundary crossing).

## FFI Necessity

```
Why FFI is Required:

1. Operating System APIs
   - System calls
   - Security primitives (mlock, mprotect)
   - Hardware access

2. Cryptographic Libraries
   - HACL*/Jasmin verified implementations
   - Hardware crypto (AES-NI, ARM Crypto)
   - HSM interfaces

3. Legacy Integration
   - Existing security tools
   - Customer systems
   - Third-party services

4. Performance
   - Hand-optimized assembly
   - SIMD operations
   - Platform-specific code
```

## FFI Security Risks

```
Risk Categories:

1. Memory Safety Violations
   - Buffer overflows in C code
   - Use-after-free
   - Double-free

2. Type Mismatches
   - Wrong argument types
   - Wrong calling convention
   - Struct layout differences

3. Ownership Confusion
   - Who frees the memory?
   - Dangling pointers
   - Resource leaks

4. Untrusted Code Execution
   - Malicious libraries
   - Supply chain attacks
   - DLL hijacking

TERAS Mitigations:
- Minimal FFI surface
- Verified wrappers
- Audit all FFI calls
- Sandbox foreign code
```

## TERAS Decision L-01

**IMPLEMENT** FFI foundation:
1. Minimal FFI surface
2. Safe wrappers required
3. Audit all FFI calls
4. Sandboxing where possible

### Architecture Decision ID: `TERAS-ARCH-L01-FFI-001`

---

# L-02: C ABI and Calling Conventions

## C ABI Basics

```rust
// C-compatible function
#[no_mangle]
pub extern "C" fn teras_encrypt(
    key: *const u8,
    key_len: usize,
    data: *const u8,
    data_len: usize,
    out: *mut u8,
    out_len: *mut usize,
) -> i32 {
    // Implementation
}

// Calling conventions
extern "C" { }        // C calling convention (default for FFI)
extern "stdcall" { }  // Windows stdcall
extern "fastcall" { } // Windows fastcall
extern "system" { }   // Platform-specific (stdcall on Windows, C elsewhere)
extern "win64" { }    // Windows x64
extern "sysv64" { }   // System V AMD64 (Linux, macOS)
```

## Type Mappings

```rust
// Primitive type mappings
// Rust           C
// i8             int8_t / signed char
// u8             uint8_t / unsigned char
// i16            int16_t / short
// u16            uint16_t / unsigned short
// i32            int32_t / int
// u32            uint32_t / unsigned int
// i64            int64_t / long long
// u64            uint64_t / unsigned long long
// isize          intptr_t / ssize_t
// usize          uintptr_t / size_t
// f32            float
// f64            double
// bool           _Bool (C99) or int
// char           uint32_t (Unicode scalar value, NOT char)
// *const T       const T*
// *mut T         T*

// C types module
use std::ffi::{c_char, c_int, c_void};
use std::os::raw::{c_long, c_ulong};
```

## Struct Layout

```rust
// C-compatible struct
#[repr(C)]
struct Point {
    x: i32,
    y: i32,
}

// Packed struct (no padding)
#[repr(C, packed)]
struct PackedData {
    flag: u8,
    value: u32,  // No padding before this
}

// Aligned struct
#[repr(C, align(16))]
struct AlignedBlock {
    data: [u8; 64],
}

// Enum representation
#[repr(C)]
enum Status {
    Ok = 0,
    Error = 1,
    Pending = 2,
}

#[repr(i32)]
enum ErrorCode {
    Success = 0,
    InvalidArg = -1,
    OutOfMemory = -2,
}
```

## TERAS Decision L-02

**IMPLEMENT** C ABI:
1. Standard calling conventions
2. Explicit type mappings
3. Repr(C) for FFI structs
4. Document layout guarantees

### Architecture Decision ID: `TERAS-ARCH-L02-ABI-001`

---

# L-03: Unsafe FFI Wrappers

## Raw FFI Declaration

```rust
// External C function declarations
extern "C" {
    fn memcpy(dest: *mut c_void, src: *const c_void, n: usize) -> *mut c_void;
    fn memset(s: *mut c_void, c: c_int, n: usize) -> *mut c_void;
    fn malloc(size: usize) -> *mut c_void;
    fn free(ptr: *mut c_void);
}

// OpenSSL example
extern "C" {
    fn EVP_CIPHER_CTX_new() -> *mut EVP_CIPHER_CTX;
    fn EVP_CIPHER_CTX_free(ctx: *mut EVP_CIPHER_CTX);
    fn EVP_EncryptInit_ex(
        ctx: *mut EVP_CIPHER_CTX,
        cipher: *const EVP_CIPHER,
        impl_: *mut ENGINE,
        key: *const u8,
        iv: *const u8,
    ) -> c_int;
}
```

## Safe Wrapper Pattern

```rust
// RAII wrapper for C resource
struct CipherContext {
    ptr: *mut EVP_CIPHER_CTX,
}

impl CipherContext {
    fn new() -> Result<Self, CryptoError> {
        let ptr = unsafe { EVP_CIPHER_CTX_new() };
        if ptr.is_null() {
            Err(CryptoError::AllocationFailed)
        } else {
            Ok(CipherContext { ptr })
        }
    }
    
    fn encrypt_init(&mut self, key: &[u8], iv: &[u8]) -> Result<(), CryptoError> {
        // Validate inputs
        if key.len() != 32 {
            return Err(CryptoError::InvalidKeySize);
        }
        if iv.len() != 16 {
            return Err(CryptoError::InvalidIvSize);
        }
        
        let result = unsafe {
            EVP_EncryptInit_ex(
                self.ptr,
                EVP_aes_256_gcm(),
                std::ptr::null_mut(),
                key.as_ptr(),
                iv.as_ptr(),
            )
        };
        
        if result == 1 {
            Ok(())
        } else {
            Err(CryptoError::InitFailed)
        }
    }
}

impl Drop for CipherContext {
    fn drop(&mut self) {
        unsafe {
            EVP_CIPHER_CTX_free(self.ptr);
        }
    }
}

// Now safe API
fn encrypt(key: &[u8; 32], iv: &[u8; 16], data: &[u8]) -> Result<Vec<u8>, CryptoError> {
    let mut ctx = CipherContext::new()?;
    ctx.encrypt_init(key, iv)?;
    ctx.encrypt_update(data)?;
    ctx.encrypt_final()
}
```

## TERAS Decision L-03

**IMPLEMENT** wrappers:
1. RAII for all C resources
2. Input validation in wrappers
3. Type-safe public API
4. No raw pointers in public API

### Architecture Decision ID: `TERAS-ARCH-L03-WRAP-001`

---

# L-04: String Handling

## C Strings

```rust
use std::ffi::{CStr, CString};

// Creating C strings
fn create_c_string(s: &str) -> Result<CString, NulError> {
    CString::new(s)  // Adds null terminator, fails if s contains \0
}

// Passing to C
extern "C" {
    fn puts(s: *const c_char) -> c_int;
}

fn print_string(s: &str) -> Result<(), Error> {
    let c_string = CString::new(s)?;
    unsafe {
        puts(c_string.as_ptr());
    }
    Ok(())
}

// Receiving from C
extern "C" {
    fn get_error_message() -> *const c_char;
}

fn get_error() -> String {
    unsafe {
        let ptr = get_error_message();
        if ptr.is_null() {
            return String::new();
        }
        CStr::from_ptr(ptr)
            .to_string_lossy()
            .into_owned()
    }
}
```

## Owned vs Borrowed

```rust
// Borrowed: &CStr - doesn't own the data
fn process_c_string(ptr: *const c_char) -> Option<&str> {
    if ptr.is_null() {
        return None;
    }
    unsafe {
        CStr::from_ptr(ptr).to_str().ok()
    }
}

// Owned: CString - owns the data
fn take_ownership(ptr: *mut c_char) -> CString {
    unsafe {
        CString::from_raw(ptr)  // Takes ownership, will free on drop
    }
}

// Be careful about ownership!
extern "C" {
    // C allocates, we must free with C's free()
    fn strdup(s: *const c_char) -> *mut c_char;
}

fn safe_strdup(s: &str) -> Result<String, Error> {
    let c_string = CString::new(s)?;
    let ptr = unsafe { strdup(c_string.as_ptr()) };
    if ptr.is_null() {
        return Err(Error::AllocationFailed);
    }
    let result = unsafe { CStr::from_ptr(ptr).to_string_lossy().into_owned() };
    unsafe { libc::free(ptr as *mut c_void); }  // Must use C's free
    Ok(result)
}
```

## TERAS Security Strings

```rust
// Secure string handling
struct SecureCString {
    inner: CString,
}

impl SecureCString {
    fn new(s: &str) -> Result<Self, NulError> {
        Ok(SecureCString {
            inner: CString::new(s)?,
        })
    }
    
    fn as_ptr(&self) -> *const c_char {
        self.inner.as_ptr()
    }
}

impl Drop for SecureCString {
    fn drop(&mut self) {
        // Zeroize before dropping
        let bytes = self.inner.as_bytes_with_nul();
        let ptr = bytes.as_ptr() as *mut u8;
        unsafe {
            std::ptr::write_bytes(ptr, 0, bytes.len());
        }
    }
}
```

## TERAS Decision L-04

**IMPLEMENT** strings:
1. CStr/CString for C interop
2. Explicit ownership tracking
3. Secure string zeroization
4. UTF-8 validation

### Architecture Decision ID: `TERAS-ARCH-L04-STR-001`

---

# L-05: Memory Management Across FFI

## Ownership Rules

```rust
// Rule 1: Allocator consistency
// Memory allocated by C must be freed by C
// Memory allocated by Rust must be freed by Rust

// C allocates
extern "C" {
    fn create_buffer(size: usize) -> *mut u8;
    fn free_buffer(ptr: *mut u8);
}

struct CBuffer {
    ptr: *mut u8,
    len: usize,
}

impl Drop for CBuffer {
    fn drop(&mut self) {
        if !self.ptr.is_null() {
            unsafe { free_buffer(self.ptr); }
        }
    }
}

// Rust allocates for C
#[no_mangle]
pub extern "C" fn teras_alloc(size: usize) -> *mut u8 {
    let layout = Layout::from_size_align(size, 8).unwrap();
    unsafe { std::alloc::alloc(layout) }
}

#[no_mangle]
pub extern "C" fn teras_free(ptr: *mut u8, size: usize) {
    if !ptr.is_null() {
        let layout = Layout::from_size_align(size, 8).unwrap();
        unsafe { std::alloc::dealloc(ptr, layout); }
    }
}
```

## Buffer Passing

```rust
// Passing slice to C (borrowed)
extern "C" {
    fn process_data(data: *const u8, len: usize) -> c_int;
}

fn process(data: &[u8]) -> Result<(), Error> {
    let result = unsafe {
        process_data(data.as_ptr(), data.len())
    };
    if result == 0 { Ok(()) } else { Err(Error::ProcessFailed) }
}

// Receiving buffer from C
extern "C" {
    fn get_data(out: *mut u8, out_len: *mut usize) -> c_int;
}

fn get_data_safe() -> Result<Vec<u8>, Error> {
    let mut len: usize = 0;
    
    // First call to get length
    let result = unsafe { get_data(std::ptr::null_mut(), &mut len) };
    if result != 0 { return Err(Error::Failed); }
    
    // Allocate buffer
    let mut buf = vec![0u8; len];
    
    // Second call to get data
    let result = unsafe { get_data(buf.as_mut_ptr(), &mut len) };
    if result != 0 { return Err(Error::Failed); }
    
    buf.truncate(len);
    Ok(buf)
}
```

## TERAS Secure Memory FFI

```rust
// Secure buffer for FFI
struct SecureFFIBuffer {
    ptr: *mut u8,
    len: usize,
    capacity: usize,
}

impl SecureFFIBuffer {
    fn new(capacity: usize) -> Self {
        let ptr = unsafe {
            let p = std::alloc::alloc_zeroed(Layout::from_size_align(capacity, 8).unwrap());
            // Lock memory
            libc::mlock(p as *const c_void, capacity);
            p
        };
        SecureFFIBuffer { ptr, len: 0, capacity }
    }
    
    fn as_mut_ptr(&mut self) -> *mut u8 {
        self.ptr
    }
    
    fn set_len(&mut self, len: usize) {
        assert!(len <= self.capacity);
        self.len = len;
    }
}

impl Drop for SecureFFIBuffer {
    fn drop(&mut self) {
        unsafe {
            // Zeroize
            std::ptr::write_bytes(self.ptr, 0, self.capacity);
            // Unlock
            libc::munlock(self.ptr as *const c_void, self.capacity);
            // Free
            std::alloc::dealloc(self.ptr, Layout::from_size_align(self.capacity, 8).unwrap());
        }
    }
}
```

## TERAS Decision L-05

**IMPLEMENT** memory:
1. Clear ownership rules
2. Allocator consistency
3. Secure buffers for FFI
4. Memory zeroization

### Architecture Decision ID: `TERAS-ARCH-L05-MEM-001`

---

# L-06: Error Handling Across FFI

## C Error Conventions

```rust
// Return code pattern
extern "C" {
    fn operation(input: *const u8, output: *mut u8) -> c_int;
    // Returns 0 on success, negative on error
}

fn safe_operation(input: &[u8]) -> Result<Vec<u8>, Error> {
    let mut output = vec![0u8; MAX_OUTPUT_SIZE];
    let result = unsafe {
        operation(input.as_ptr(), output.as_mut_ptr())
    };
    match result {
        0 => Ok(output),
        -1 => Err(Error::InvalidInput),
        -2 => Err(Error::BufferTooSmall),
        _ => Err(Error::Unknown(result)),
    }
}

// errno pattern
extern "C" {
    fn open(pathname: *const c_char, flags: c_int) -> c_int;
}

fn safe_open(path: &str) -> Result<FileHandle, Error> {
    let c_path = CString::new(path)?;
    let fd = unsafe { open(c_path.as_ptr(), O_RDONLY) };
    if fd < 0 {
        let errno = std::io::Error::last_os_error();
        Err(Error::OsError(errno))
    } else {
        Ok(FileHandle(fd))
    }
}

// Output parameter pattern
extern "C" {
    fn get_value(result: *mut c_int, error: *mut *const c_char) -> c_int;
}

fn safe_get_value() -> Result<i32, Error> {
    let mut result: c_int = 0;
    let mut error: *const c_char = std::ptr::null();
    
    let status = unsafe { get_value(&mut result, &mut error) };
    
    if status != 0 {
        let msg = if error.is_null() {
            "Unknown error".to_string()
        } else {
            unsafe { CStr::from_ptr(error).to_string_lossy().into_owned() }
        };
        Err(Error::Foreign(msg))
    } else {
        Ok(result)
    }
}
```

## Panic Safety

```rust
// Catch panics at FFI boundary
#[no_mangle]
pub extern "C" fn teras_operation(input: *const u8, len: usize) -> c_int {
    let result = std::panic::catch_unwind(|| {
        // Safe to panic here
        let slice = unsafe { std::slice::from_raw_parts(input, len) };
        process(slice)
    });
    
    match result {
        Ok(Ok(())) => 0,
        Ok(Err(e)) => e.code(),
        Err(_) => -999,  // Panic occurred
    }
}

// Audit panics at FFI boundary
#[no_mangle]
pub extern "C" fn teras_secure_operation(input: *const u8, len: usize) -> c_int {
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let slice = unsafe { std::slice::from_raw_parts(input, len) };
        process(slice)
    }));
    
    match result {
        Ok(Ok(())) => 0,
        Ok(Err(e)) => {
            Audit::log(FFIError { error: &e });
            e.code()
        }
        Err(panic) => {
            Audit::log(FFIPanic { info: format!("{:?}", panic) });
            -999
        }
    }
}
```

## TERAS Decision L-06

**IMPLEMENT** error handling:
1. Map C errors to Result
2. Catch panics at boundary
3. Audit FFI errors
4. Never expose internals

### Architecture Decision ID: `TERAS-ARCH-L06-ERR-001`

---

# L-07: Callback Functions

## Function Pointers

```rust
// C callback type
type Callback = extern "C" fn(data: *const u8, len: usize) -> c_int;

extern "C" {
    fn register_callback(cb: Callback);
    fn process_with_callback(data: *const u8, len: usize, cb: Callback) -> c_int;
}

// Implementing callback
extern "C" fn my_callback(data: *const u8, len: usize) -> c_int {
    if data.is_null() || len == 0 {
        return -1;
    }
    let slice = unsafe { std::slice::from_raw_parts(data, len) };
    // Process slice...
    0
}

fn register() {
    unsafe { register_callback(my_callback); }
}
```

## Closures as Callbacks

```rust
// Closures need special handling
extern "C" {
    fn set_handler(
        callback: extern "C" fn(*mut c_void, *const u8, usize),
        user_data: *mut c_void,
    );
}

// Trampoline function
extern "C" fn trampoline<F>(user_data: *mut c_void, data: *const u8, len: usize)
where
    F: FnMut(&[u8]),
{
    let closure = unsafe { &mut *(user_data as *mut F) };
    let slice = unsafe { std::slice::from_raw_parts(data, len) };
    closure(slice);
}

fn set_closure_handler<F: FnMut(&[u8]) + 'static>(mut f: F) {
    let user_data = Box::into_raw(Box::new(f)) as *mut c_void;
    unsafe {
        set_handler(trampoline::<F>, user_data);
    }
}
```

## TERAS Secure Callbacks

```rust
// Capability-checked callback
struct SecureCallback {
    callback: Box<dyn Fn(&[u8]) -> Result<(), Error> + Send + Sync>,
    required_cap: CapabilitySet,
}

impl SecureCallback {
    fn call(&self, data: &[u8]) -> Result<(), Error> {
        // Check capability before calling
        if !current_context().has_capabilities(&self.required_cap) {
            Audit::log(CallbackCapabilityDenied { required: &self.required_cap });
            return Err(Error::InsufficientCapability);
        }
        
        Audit::log(CallbackInvoked { cap: &self.required_cap });
        (self.callback)(data)
    }
}

// FFI wrapper with security
extern "C" fn secure_callback_wrapper(
    user_data: *mut c_void,
    data: *const u8,
    len: usize,
) -> c_int {
    let callback = unsafe { &*(user_data as *const SecureCallback) };
    let slice = unsafe { std::slice::from_raw_parts(data, len) };
    
    match callback.call(slice) {
        Ok(()) => 0,
        Err(e) => e.code(),
    }
}
```

## TERAS Decision L-07

**IMPLEMENT** callbacks:
1. Type-safe function pointers
2. Closure trampoline pattern
3. Capability checking
4. Audit callback invocations

### Architecture Decision ID: `TERAS-ARCH-L07-CB-001`

---

# L-08: Building and Linking

## Build Scripts

```rust
// build.rs
fn main() {
    // Link native library
    println!("cargo:rustc-link-lib=ssl");
    println!("cargo:rustc-link-lib=crypto");
    
    // Search path
    println!("cargo:rustc-link-search=/usr/local/lib");
    
    // Rebuild if changed
    println!("cargo:rerun-if-changed=wrapper.h");
    
    // Generate bindings
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .generate()
        .expect("Unable to generate bindings");
    
    bindings
        .write_to_file(PathBuf::from(env::var("OUT_DIR").unwrap()).join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
```

## Bindgen

```rust
// wrapper.h
#include <openssl/evp.h>
#include <openssl/aes.h>

// build.rs with bindgen
fn main() {
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        // Whitelist specific functions
        .whitelist_function("EVP_.*")
        .whitelist_function("AES_.*")
        // Whitelist types
        .whitelist_type("EVP_.*")
        // Block system headers
        .blocklist_type("__.*")
        // Generate
        .generate()
        .expect("Unable to generate bindings");
}

// Usage
mod bindings {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

use bindings::*;
```

## Static vs Dynamic Linking

```rust
// build.rs
fn main() {
    // Static linking (preferred for security)
    println!("cargo:rustc-link-lib=static=crypto");
    
    // Dynamic linking
    println!("cargo:rustc-link-lib=dylib=ssl");
    
    // Framework (macOS)
    println!("cargo:rustc-link-lib=framework=Security");
}

// Cargo.toml features
[features]
static-openssl = []
vendored-openssl = ["openssl/vendored"]
```

## TERAS Decision L-08

**IMPLEMENT** building:
1. Automated bindgen
2. Static linking preferred
3. Vendored dependencies
4. Reproducible builds

### Architecture Decision ID: `TERAS-ARCH-L08-BUILD-001`

---

# L-09: Platform-Specific FFI

## Windows APIs

```rust
#[cfg(windows)]
mod windows_ffi {
    use windows_sys::Win32::{
        Foundation::*,
        Security::*,
        System::Memory::*,
    };
    
    pub fn lock_memory(ptr: *mut u8, size: usize) -> bool {
        unsafe { VirtualLock(ptr as *const _, size) != 0 }
    }
    
    pub fn protect_memory(ptr: *mut u8, size: usize) -> bool {
        let mut old_protect = 0;
        unsafe {
            VirtualProtect(
                ptr as *const _,
                size,
                PAGE_READONLY,
                &mut old_protect,
            ) != 0
        }
    }
}
```

## Unix APIs

```rust
#[cfg(unix)]
mod unix_ffi {
    use libc::{mlock, mprotect, PROT_READ};
    
    pub fn lock_memory(ptr: *mut u8, size: usize) -> bool {
        unsafe { mlock(ptr as *const _, size) == 0 }
    }
    
    pub fn protect_memory(ptr: *mut u8, size: usize) -> bool {
        unsafe { mprotect(ptr as *mut _, size, PROT_READ) == 0 }
    }
}
```

## Hardware Crypto

```rust
// AES-NI (x86_64)
#[cfg(target_arch = "x86_64")]
mod aesni {
    use std::arch::x86_64::*;
    
    #[target_feature(enable = "aes")]
    unsafe fn aes_encrypt_block(key: &[u8; 16], block: &mut [u8; 16]) {
        let key_schedule = load_key_schedule(key);
        let mut state = _mm_loadu_si128(block.as_ptr() as *const __m128i);
        
        state = _mm_xor_si128(state, key_schedule[0]);
        for i in 1..10 {
            state = _mm_aesenc_si128(state, key_schedule[i]);
        }
        state = _mm_aesenclast_si128(state, key_schedule[10]);
        
        _mm_storeu_si128(block.as_mut_ptr() as *mut __m128i, state);
    }
}

// ARM Crypto
#[cfg(target_arch = "aarch64")]
mod arm_crypto {
    use std::arch::aarch64::*;
    
    #[target_feature(enable = "aes")]
    unsafe fn aes_encrypt_block(key: &[u8; 16], block: &mut [u8; 16]) {
        // ARM crypto extension implementation
    }
}
```

## TERAS Decision L-09

**IMPLEMENT** platform FFI:
1. Unified abstraction layer
2. Platform-specific implementations
3. Hardware crypto detection
4. Fallback implementations

### Architecture Decision ID: `TERAS-ARCH-L09-PLAT-001`

---

# L-10: FFI in TERAS Products

## MENARA FFI (Android/iOS)

```rust
// Android JNI
#[cfg(target_os = "android")]
mod android {
    use jni::JNIEnv;
    use jni::objects::{JClass, JString};
    
    #[no_mangle]
    pub extern "system" fn Java_com_teras_menara_Scanner_scan(
        env: JNIEnv,
        _class: JClass,
        path: JString,
    ) -> jint {
        let path: String = env.get_string(path).unwrap().into();
        match scan_app(&path) {
            Ok(result) => result.threat_level as jint,
            Err(_) => -1,
        }
    }
}

// iOS
#[cfg(target_os = "ios")]
mod ios {
    use objc::runtime::Object;
    
    #[no_mangle]
    pub extern "C" fn teras_menara_scan(path: *const c_char) -> c_int {
        let path = unsafe { CStr::from_ptr(path).to_str().unwrap() };
        match scan_app(path) {
            Ok(result) => result.threat_level as c_int,
            Err(_) => -1,
        }
    }
}
```

## GAPURA FFI (Web Server Integration)

```rust
// Nginx module
#[no_mangle]
pub extern "C" fn ngx_teras_gapura_check_request(
    request: *mut ngx_http_request_t,
) -> ngx_int_t {
    let req = unsafe { &*request };
    
    let uri = extract_uri(req);
    let headers = extract_headers(req);
    let body = extract_body(req);
    
    match check_request(&uri, &headers, &body) {
        WafDecision::Allow => NGX_OK,
        WafDecision::Block(reason) => {
            Audit::log(RequestBlocked { uri: &uri, reason: &reason });
            NGX_HTTP_FORBIDDEN
        }
    }
}

// Apache module
#[no_mangle]
pub extern "C" fn teras_gapura_handler(r: *mut request_rec) -> c_int {
    // Apache module implementation
}
```

## ZIRAH FFI (Kernel/Driver)

```rust
// Linux kernel module interface
#[cfg(target_os = "linux")]
mod kernel {
    #[no_mangle]
    pub extern "C" fn teras_zirah_scan_file(
        fd: c_int,
        result: *mut ScanResult,
    ) -> c_int {
        // Interface with kernel module
    }
}

// Windows driver interface
#[cfg(windows)]
mod driver {
    #[no_mangle]
    pub extern "system" fn TerasZirahScanFile(
        FileHandle: HANDLE,
        Result: *mut SCAN_RESULT,
    ) -> NTSTATUS {
        // Interface with Windows driver
    }
}
```

## BENTENG FFI (Biometric Libraries)

```rust
// Face recognition library
extern "C" {
    fn face_detect(
        image: *const u8,
        width: c_int,
        height: c_int,
        faces: *mut FaceRect,
        max_faces: c_int,
    ) -> c_int;
    
    fn face_compare(
        template1: *const u8,
        template2: *const u8,
        template_size: c_int,
    ) -> c_float;
}

pub fn detect_faces(image: &Image) -> Vec<FaceRect> {
    let mut faces = vec![FaceRect::default(); 10];
    let count = unsafe {
        face_detect(
            image.data.as_ptr(),
            image.width as c_int,
            image.height as c_int,
            faces.as_mut_ptr(),
            10,
        )
    };
    faces.truncate(count as usize);
    faces
}
```

## SANDI FFI (HSM)

```rust
// PKCS#11 interface
extern "C" {
    fn C_Initialize(pInitArgs: *mut CK_C_INITIALIZE_ARGS) -> CK_RV;
    fn C_GetSlotList(
        tokenPresent: CK_BBOOL,
        pSlotList: *mut CK_SLOT_ID,
        pulCount: *mut CK_ULONG,
    ) -> CK_RV;
    fn C_OpenSession(
        slotID: CK_SLOT_ID,
        flags: CK_FLAGS,
        pApplication: *mut c_void,
        Notify: CK_NOTIFY,
        phSession: *mut CK_SESSION_HANDLE,
    ) -> CK_RV;
    fn C_Sign(
        hSession: CK_SESSION_HANDLE,
        pData: *mut CK_BYTE,
        ulDataLen: CK_ULONG,
        pSignature: *mut CK_BYTE,
        pulSignatureLen: *mut CK_ULONG,
    ) -> CK_RV;
}

pub struct HsmSession {
    handle: CK_SESSION_HANDLE,
}

impl HsmSession {
    pub fn sign(&self, data: &[u8]) -> Result<Vec<u8>, HsmError> {
        let mut sig_len: CK_ULONG = 256;
        let mut signature = vec![0u8; sig_len as usize];
        
        let rv = unsafe {
            C_Sign(
                self.handle,
                data.as_ptr() as *mut _,
                data.len() as CK_ULONG,
                signature.as_mut_ptr(),
                &mut sig_len,
            )
        };
        
        if rv == CKR_OK {
            signature.truncate(sig_len as usize);
            Ok(signature)
        } else {
            Err(HsmError::from_pkcs11(rv))
        }
    }
}
```

## TERAS Decision L-10

**IMPLEMENT** product FFI:
1. Platform SDK integration
2. Hardware interfaces
3. Third-party biometrics
4. HSM PKCS#11

### Architecture Decision ID: `TERAS-ARCH-L10-PROD-001`

---

# Domain L Summary

| Session | Topic | Decision ID |
|---------|-------|-------------|
| L-01 | Foundations | TERAS-ARCH-L01-FFI-001 |
| L-02 | C ABI | TERAS-ARCH-L02-ABI-001 |
| L-03 | Wrappers | TERAS-ARCH-L03-WRAP-001 |
| L-04 | Strings | TERAS-ARCH-L04-STR-001 |
| L-05 | Memory | TERAS-ARCH-L05-MEM-001 |
| L-06 | Errors | TERAS-ARCH-L06-ERR-001 |
| L-07 | Callbacks | TERAS-ARCH-L07-CB-001 |
| L-08 | Building | TERAS-ARCH-L08-BUILD-001 |
| L-09 | Platform | TERAS-ARCH-L09-PLAT-001 |
| L-10 | Products | TERAS-ARCH-L10-PROD-001 |

## Domain L: COMPLETE

---

*Research Track Output â€” Domain L: Foreign Function Interface*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
