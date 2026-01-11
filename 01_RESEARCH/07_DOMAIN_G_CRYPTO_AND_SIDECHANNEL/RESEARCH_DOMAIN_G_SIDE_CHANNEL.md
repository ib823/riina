# TERAS-LANG Research Domain G: Side-Channel Attacks

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-G-SIDE-CHANNEL |
| Version | 1.0.0 |
| Date | 2026-01-04 |
| Sessions | G-01 through G-15 |
| Domain | G: Side-Channel Attacks |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# G-01: Side-Channel Attack Foundations

## Executive Summary

Side-channel attacks extract secret information by observing physical implementation characteristics rather than exploiting algorithmic weaknesses. This domain covers all major side-channel classes, their countermeasures, and their relevance to TERAS security.

## 1. Side-Channel Taxonomy

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Side-Channel Attack Taxonomy                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  TIMING CHANNELS                                                    │
│  ├── Cache timing (Prime+Probe, Flush+Reload, Evict+Time)          │
│  ├── Branch timing (branch misprediction)                          │
│  ├── Memory access timing (DRAM row buffer)                        │
│  ├── Network timing (remote timing attacks)                        │
│  └── Instruction timing (data-dependent operations)                │
│                                                                     │
│  POWER CHANNELS                                                     │
│  ├── Simple Power Analysis (SPA)                                   │
│  ├── Differential Power Analysis (DPA)                             │
│  ├── Correlation Power Analysis (CPA)                              │
│  ├── High-Order DPA (masked implementations)                       │
│  └── Template attacks                                              │
│                                                                     │
│  ELECTROMAGNETIC CHANNELS                                           │
│  ├── Simple EM Analysis (SEMA)                                     │
│  ├── Differential EM Analysis (DEMA)                               │
│  ├── Near-field probing                                            │
│  └── Far-field analysis                                            │
│                                                                     │
│  ACOUSTIC CHANNELS                                                  │
│  ├── Keyboard acoustic emanations                                  │
│  ├── CPU acoustic emanations                                       │
│  ├── Printer/scanner analysis                                      │
│  └── Hard drive analysis                                           │
│                                                                     │
│  FAULT INJECTION                                                    │
│  ├── Voltage glitching                                             │
│  ├── Clock glitching                                               │
│  ├── Laser fault injection                                         │
│  ├── EM fault injection                                            │
│  └── Rowhammer (software-induced)                                  │
│                                                                     │
│  SPECULATIVE EXECUTION                                              │
│  ├── Spectre variants                                              │
│  ├── Meltdown variants                                             │
│  ├── MDS (Microarchitectural Data Sampling)                        │
│  └── LVI (Load Value Injection)                                    │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. Kocher's Original Timing Attack (1996)

### 2.1 Attack Principle

```
RSA Timing Attack (Kocher 1996):

Modular Exponentiation: c^d mod n (decryption)

Square-and-Multiply Algorithm:
for each bit b in d (MSB to LSB):
    result = result² mod n           // Always square
    if b == 1:
        result = result × c mod n    // Conditional multiply

Timing Difference:
├── Bit = 1: Square + Multiply (longer)
├── Bit = 0: Square only (shorter)
└── Total time leaks exponent bits

Attack:
1. Measure decryption times for many ciphertexts
2. Correlate timing with guessed key bits
3. Recover key one bit at a time
4. Statistical analysis distinguishes bit values

Countermeasures:
├── Montgomery multiplication (constant operations)
├── RSA blinding: c' = c × r^e, d' = (c')^d × r^-1
├── Constant-time implementation
└── Time padding (noise addition)
```

## 3. Attack Surface Analysis

### 3.1 Observable Channels

```
Channel          │ Bandwidth   │ Distance    │ Equipment
─────────────────┼─────────────┼─────────────┼──────────────────
CPU cache timing │ ~MB/s       │ Same system │ Software only
Power            │ ~KB/s       │ Contact     │ Oscilloscope
EM (near-field)  │ ~KB/s       │ Centimeters │ EM probe, SDR
EM (far-field)   │ ~B/s        │ Meters      │ Antenna, SDR
Acoustic         │ ~B/s        │ Meters      │ Microphone
Network timing   │ Bits/query  │ Global      │ Network access
```

## TERAS Decision G-01

**FOR TERAS:**
1. All cryptographic operations must be constant-time
2. Side-channel resistance is mandatory, not optional
3. Document attack surface for each component
4. Implement defense-in-depth against side-channels

### Architecture Decision ID: `TERAS-ARCH-G01-FOUNDATION-001`

---

# G-02: Timing Attacks - Cache-Based

## 1. CPU Cache Architecture

### 1.1 Cache Hierarchy

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Modern CPU Cache Hierarchy                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Core 0                           Core 1                            │
│  ┌────────────────────┐           ┌────────────────────┐           │
│  │    Registers       │           │    Registers       │           │
│  │    ~1 cycle        │           │    ~1 cycle        │           │
│  ├────────────────────┤           ├────────────────────┤           │
│  │  L1 Data   L1 Inst │           │  L1 Data   L1 Inst │           │
│  │  32KB      32KB    │           │  32KB      32KB    │           │
│  │  ~4 cycles         │           │  ~4 cycles         │           │
│  ├────────────────────┤           ├────────────────────┤           │
│  │       L2 Cache     │           │       L2 Cache     │           │
│  │       256KB-1MB    │           │       256KB-1MB    │           │
│  │       ~12 cycles   │           │       ~12 cycles   │           │
│  └─────────┬──────────┘           └─────────┬──────────┘           │
│            └──────────────┬─────────────────┘                      │
│                           ▼                                         │
│            ┌──────────────────────────┐                            │
│            │      L3 Cache (LLC)      │                            │
│            │      8MB-64MB            │                            │
│            │      ~40 cycles          │                            │
│            │      Shared across cores │                            │
│            └──────────────────────────┘                            │
│                           │                                         │
│                           ▼                                         │
│            ┌──────────────────────────┐                            │
│            │      Main Memory         │                            │
│            │      ~200 cycles         │                            │
│            └──────────────────────────┘                            │
│                                                                     │
│  Cache Organization:                                                │
│  ├── Set-associative (typically 8-16 way)                          │
│  ├── Cache line: 64 bytes                                          │
│  ├── Inclusive vs exclusive (varies by CPU)                        │
│  └── Replacement: LRU or pseudo-LRU                                │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. Cache Attack Techniques

### 2.1 Prime+Probe

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Prime+Probe Attack                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  PRIME Phase (Attacker fills cache set):                           │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  Cache Set N:  [A0][A1][A2][A3][A4][A5][A6][A7]             │   │
│  │                 ▲   ▲   ▲   ▲   ▲   ▲   ▲   ▲              │   │
│  │                 └───┴───┴───┴───┴───┴───┴───┘              │   │
│  │                    Attacker's data                          │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  VICTIM Executes (accesses cache):                                  │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  Cache Set N:  [A0][V ][A2][A3][A4][A5][A6][A7]             │   │
│  │                      ▲                                      │   │
│  │                 Victim's data evicts A1                     │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  PROBE Phase (Attacker re-accesses):                               │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  Access A0: FAST (cache hit)                                │   │
│  │  Access A1: SLOW (cache miss) ← VICTIM ACCESSED THIS SET!   │   │
│  │  Access A2: FAST (cache hit)                                │   │
│  │  ...                                                        │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  Requirements:                                                      │
│  ├── Know cache geometry (sets, ways)                              │
│  ├── Create eviction set (addresses mapping to same set)           │
│  ├── No need for shared memory with victim                         │
│  └── Works across processes, VMs, containers                       │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 Flush+Reload

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Flush+Reload Attack                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Prerequisite: Shared memory between attacker and victim            │
│  (e.g., shared libraries, deduplication)                           │
│                                                                     │
│  FLUSH Phase:                                                       │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  clflush(target_address)                                    │   │
│  │  Evicts target from ALL cache levels                        │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  WAIT for victim to execute                                        │
│                                                                     │
│  RELOAD Phase:                                                      │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  start = rdtsc()                                            │   │
│  │  access(target_address)                                     │   │
│  │  end = rdtsc()                                              │   │
│  │                                                              │   │
│  │  if (end - start < THRESHOLD):                              │   │
│  │      // FAST: Victim accessed this address                  │   │
│  │  else:                                                       │   │
│  │      // SLOW: Victim did NOT access this address            │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  Advantages:                                                        │
│  ├── Higher precision than Prime+Probe                             │
│  ├── Cache-line granularity (64 bytes)                             │
│  └── Works across cores                                            │
│                                                                     │
│  Disadvantages:                                                     │
│  ├── Requires shared memory                                        │
│  └── Requires clflush instruction                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.3 Evict+Time

```
Evict+Time Attack:
1. Measure victim operation time (baseline)
2. Access memory to evict victim's cache lines
3. Measure victim operation time again
4. Compare times:
   - Longer: victim needed evicted data
   - Same: victim didn't use that data

Less precise than Flush+Reload but doesn't require shared memory
```

## 3. Cache Attack Examples

### 3.1 AES T-Table Attack

```c
// Vulnerable AES implementation (T-Table)
// Final round:
for (i = 0; i < 16; i++) {
    output[i] = SBox[state[i] ^ round_key[i]];
}

// Attack:
// 1. Last round key XORed with state before S-box lookup
// 2. S-box lookup address = state[i] ^ key[i]
// 3. Attacker controls ciphertext (= state before last round key XOR)
// 4. Monitor which cache lines accessed
// 5. If cache line for SBox[c ^ k] accessed → deduce key byte k

// For each key byte (16 total):
// - Try all 256 possible key values
// - Measure cache access for SBox[known_ciphertext ^ guess]
// - Cache hit reveals correct key byte
```

### 3.2 RSA Cache Attack

```
RSA Square-and-Multiply with Lookup Table:
- Precomputed table of powers: g, g², g³, ...
- Exponentiation uses table lookups
- Cache access pattern reveals exponent bits

Attack (Flush+Reload on table):
1. Flush all table entries
2. Victim performs exponentiation
3. Reload and time each table entry
4. Access pattern reveals which powers used
5. Reconstruct exponent (private key)
```

## 4. Countermeasures

### 4.1 Constant-Time Implementation

```c
// VULNERABLE: Secret-dependent table lookup
uint8_t sbox_lookup(uint8_t input) {
    return sbox[input];  // Cache-timing leak
}

// SECURE: Constant-time lookup (scan entire table)
uint8_t constant_time_lookup(uint8_t input) {
    uint8_t result = 0;
    for (int i = 0; i < 256; i++) {
        // Constant-time conditional: no branch
        uint8_t mask = ct_eq(i, input);  // 0xFF if equal, 0x00 otherwise
        result |= (sbox[i] & mask);
    }
    return result;
}

// Constant-time equality check
uint8_t ct_eq(uint8_t a, uint8_t b) {
    uint8_t diff = a ^ b;
    // If diff == 0, returns 0xFF; else returns 0x00
    return (uint8_t)(((int32_t)diff - 1) >> 8);
}

// Constant-time select
uint64_t ct_select(uint64_t a, uint64_t b, uint64_t selector) {
    // selector must be 0 or 1
    uint64_t mask = (uint64_t)(-(int64_t)selector);
    return (a & mask) | (b & ~mask);
}
```

### 4.2 Hardware Countermeasures

```
Cache Partitioning:
├── Intel CAT (Cache Allocation Technology)
├── Separate cache partitions for security domains
└── Prevents cross-tenant cache attacks

Scatter-Gather Tables:
├── AES-NI: Lookup-free AES implementation
├── Vectorized computation
└── No memory access patterns

Address Space Layout Randomization (ASLR):
├── Randomize memory layout
├── Makes eviction set creation harder
└── Not sufficient alone (can be defeated)
```

## TERAS Decision G-02

**FOR TERAS:**
1. Ban secret-dependent memory access
2. Use bitsliced or constant-time crypto implementations
3. Prefer AES-NI over table-based AES
4. Implement cache attack testing in validation suite

### Architecture Decision ID: `TERAS-ARCH-G02-CACHE-001`

---

# G-03: Timing Attacks - Branch and Control Flow

## 1. Branch Prediction Side Channels

### 1.1 Branch Predictor Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Modern Branch Predictor                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    Branch Target Buffer (BTB)                │   │
│  │  - Maps PC to predicted target                              │   │
│  │  - Indexed by PC bits                                       │   │
│  │  - Shared across processes (before mitigations)             │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                  Pattern History Table (PHT)                 │   │
│  │  - 2-bit saturating counters                                │   │
│  │  - Indexed by PC XOR branch history                         │   │
│  │  - Predicts taken/not-taken                                 │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                Branch History Buffer (BHB)                   │   │
│  │  - Records recent branch outcomes                           │   │
│  │  - Global or per-branch                                     │   │
│  │  - Used for correlated prediction                           │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                Return Stack Buffer (RSB)                     │   │
│  │  - Predicts return addresses                                │   │
│  │  - CALL pushes, RET pops                                    │   │
│  │  - Can underflow/overflow                                   │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Branch Timing Attack

```c
// VULNERABLE: Secret-dependent branch
void process_secret(uint8_t* key, int len) {
    for (int i = 0; i < len; i++) {
        if (key[i] & 0x80) {  // Branch depends on key bit
            operation_a();     // ~100 cycles
        } else {
            operation_b();     // ~100 cycles
        }
    }
}

// Attack:
// 1. Prime branch predictor
// 2. Victim executes with secret
// 3. Misprediction timing reveals branch direction
// 4. Branch direction reveals key bit

// Timing difference:
// - Correctly predicted branch: ~1 cycle penalty
// - Mispredicted branch: ~15-20 cycle penalty

// SECURE: Branchless implementation
void process_secret_secure(uint8_t* key, int len) {
    for (int i = 0; i < len; i++) {
        uint8_t bit = (key[i] >> 7) & 1;
        // Both operations always execute
        result_a = operation_a_inline();
        result_b = operation_b_inline();
        // Select result without branch
        result[i] = ct_select(result_a, result_b, bit);
    }
}
```

## 2. Spectre Attacks

### 2.1 Spectre v1 (Bounds Check Bypass)

```c
// VULNERABLE CODE:
if (x < array1_size) {
    y = array2[array1[x] * 4096];
}

// ATTACK SEQUENCE:
// 1. Train branch predictor: x < array1_size is TRUE
// 2. Flush array2 from cache
// 3. Call with x = malicious_index (out of bounds)
// 4. Branch predictor predicts TRUE (incorrectly)
// 5. Speculative execution reads array1[malicious_index]
// 6. Value used to index array2 (speculatively)
// 7. array2[secret * 4096] loaded into cache
// 8. Branch resolves as FALSE, speculative state discarded
// 9. BUT: Cache state persists!
// 10. Probe array2 to find which page was cached
// 11. Cached page index reveals secret byte

// MITIGATION: Speculation barrier
if (x < array1_size) {
    __asm__ __volatile__("lfence" ::: "memory");  // Serialize
    y = array2[array1[x] * 4096];
}

// MITIGATION: Index masking
x_masked = x & (-(x < array1_size));  // x if in bounds, 0 otherwise
y = array2[array1[x_masked] * 4096];
```

### 2.2 Spectre v2 (Branch Target Injection)

```
Attack Flow:
1. Attacker trains indirect branch predictor
   - Make it predict victim's indirect call goes to gadget
   
2. Victim executes indirect call
   - Branch predictor mispredicts to attacker's gadget
   
3. Gadget executes speculatively
   - Leaks secret via cache side channel
   
4. Speculation resolved, but cache state reveals secret

Mitigations:
├── Retpoline: Replace indirect branch with return trampoline
│   - JMP *rax becomes:
│     call retpoline_call
│   retpoline_call:
│     mov rax, [rsp]
│     lfence
│     jmp *rax
│     
├── IBRS (Indirect Branch Restricted Speculation)
│   - Prevent user→kernel and VM→hypervisor BTB injection
│   
├── IBPB (Indirect Branch Predictor Barrier)
│   - Flush branch predictor on context switch
│   
└── eIBRS (Enhanced IBRS)
    - Hardware always-on mode
```

### 2.3 Spectre-RSB (Return Stack Buffer)

```
Attack:
1. Attacker fills RSB with malicious addresses
2. Victim executes deep call stack
3. RSB underflows (returns exceed recorded calls)
4. CPU falls back to BTB prediction
5. Mispredicted return executes attacker-controlled code speculatively

Mitigation:
├── RSB stuffing: Fill RSB on context switch
└── IBRS: Prevents cross-domain RSB attacks
```

## 3. Constant-Time Control Flow

### 3.1 Conditional Selection

```c
// VULNERABLE: Branch
int max(int a, int b) {
    if (a > b) return a;
    else return b;
}

// SECURE: Branchless
int max_ct(int a, int b) {
    int diff = a - b;
    int mask = diff >> 31;  // All 1s if a < b, all 0s if a >= b
    return a ^ ((a ^ b) & mask);
}

// Generic constant-time select
static inline uint64_t ct_select64(uint64_t a, uint64_t b, int condition) {
    // condition must be 0 or 1
    uint64_t mask = -(uint64_t)condition;
    return (a & mask) | (b & ~mask);
}
```

### 3.2 Constant-Time Comparison

```c
// VULNERABLE: Early-exit comparison
int memcmp(const void* a, const void* b, size_t n) {
    const uint8_t* pa = a;
    const uint8_t* pb = b;
    for (size_t i = 0; i < n; i++) {
        if (pa[i] != pb[i])
            return pa[i] - pb[i];  // Early exit leaks position
    }
    return 0;
}

// SECURE: Constant-time comparison
int ct_memcmp(const void* a, const void* b, size_t n) {
    const volatile uint8_t* pa = a;
    const volatile uint8_t* pb = b;
    uint8_t diff = 0;
    for (size_t i = 0; i < n; i++) {
        diff |= pa[i] ^ pb[i];  // Always processes all bytes
    }
    return diff;  // 0 if equal, non-zero otherwise
}
```

## TERAS Decision G-03

**FOR TERAS:**
1. Eliminate all secret-dependent branches
2. Use constant-time primitives library
3. Enable Spectre mitigations in runtime
4. Test for timing side-channels in CI

### Architecture Decision ID: `TERAS-ARCH-G03-BRANCH-001`

---

# G-04: Power Analysis Attacks

## 1. Simple Power Analysis (SPA)

### 1.1 Power Consumption Model

```
┌─────────────────────────────────────────────────────────────────────┐
│                    CMOS Power Consumption                            │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  P_total = P_static + P_dynamic                                    │
│                                                                     │
│  P_static = V_dd × I_leak  (leakage current)                       │
│                                                                     │
│  P_dynamic = α × C × V_dd² × f                                     │
│             ↓   ↓   ↓     ↓                                        │
│             │   │   │     └── Frequency                            │
│             │   │   └──────── Supply voltage                       │
│             │   └──────────── Capacitance                          │
│             └──────────────── Activity factor (0 to 1 transitions) │
│                                                                     │
│  Key insight: Activity factor depends on DATA being processed      │
│                                                                     │
│  Hamming Weight Model:                                              │
│  P ≈ a × HW(data) + b                                              │
│  where HW(x) = number of 1-bits in x                               │
│                                                                     │
│  Hamming Distance Model:                                            │
│  P ≈ a × HD(old_data, new_data) + b                                │
│  where HD(x,y) = HW(x ⊕ y) = number of differing bits             │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 SPA on RSA

```
┌─────────────────────────────────────────────────────────────────────┐
│                    SPA Attack on RSA                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Square-and-Multiply Power Trace:                                   │
│                                                                     │
│  Key bits:    1    0    1    1    0    1    0    ...               │
│                                                                     │
│  Power:  ┌──┐   ┌──┐   ┌──┐   ┌──┐   ┌──┐   ┌──┐   ┌──┐           │
│          │S │   │S │   │S │   │S │   │S │   │S │   │S │           │
│          │  │   │  │   │  │   │  │   │  │   │  │   │  │           │
│          │M │   │  │   │M │   │M │   │  │   │M │   │  │           │
│          └──┘   └──┘   └──┘   └──┘   └──┘   └──┘   └──┘           │
│           ▲             ▲     ▲             ▲                       │
│           │             │     │             │                       │
│         Multiply     Multiply Multiply   Multiply                   │
│         visible      visible  visible    visible                    │
│                                                                     │
│  Attack: Visually identify square vs square+multiply patterns       │
│  Key bit = 1 where multiply follows square                         │
│                                                                     │
│  Countermeasure: Always perform multiply (Montgomery ladder)        │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. Differential Power Analysis (DPA)

### 2.1 DPA Attack Principle

```
┌─────────────────────────────────────────────────────────────────────┐
│                    DPA Attack on AES                                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Target: First-round S-box output                                   │
│  S_out = SBox[plaintext[i] ⊕ key[i]]                               │
│                                                                     │
│  Attack for one key byte (key[i]):                                  │
│                                                                     │
│  1. Collect N power traces with different plaintexts               │
│     Traces: T₁, T₂, T₃, ..., Tₙ                                    │
│     Plaintexts: P₁, P₂, P₃, ..., Pₙ                                │
│                                                                     │
│  2. For each key guess k ∈ [0, 255]:                               │
│     - Compute hypothetical S-box outputs:                          │
│       H_i = SBox[P_i[byte] ⊕ k]                                    │
│     - Compute hypothetical power: HW(H_i)                          │
│     - Correlate with actual traces                                 │
│                                                                     │
│  3. Correct key guess: High correlation at S-box time              │
│     Wrong key guesses: Low/no correlation                          │
│                                                                     │
│  Correlation:                                                       │
│  ρ = Σ(T_i - T̄)(H_i - H̄) / √(Σ(T_i - T̄)² × Σ(H_i - H̄)²)         │
│                                                                     │
│  Correct key shows spike at operation time                         │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 2.2 Number of Traces Required

```
Traces needed vs. SNR:

SNR (Signal-to-Noise Ratio) │ Traces for 99% success
────────────────────────────┼───────────────────────
         0.1                │    ~10,000
         0.5                │    ~400
         1.0                │    ~100
         2.0                │    ~25
         5.0                │    ~4

Factors affecting SNR:
├── Measurement equipment quality
├── Device power filtering
├── Algorithmic complexity
├── Masking order
└── Noise injection
```

## 3. Countermeasures

### 3.1 Masking

```c
// UNMASKED S-box (vulnerable):
uint8_t sbox_output = SBox[plaintext ^ key];

// FIRST-ORDER MASKED:
// Split secret into two shares: x = x₁ ⊕ x₂
uint8_t x1 = random();
uint8_t x2 = (plaintext ^ key) ^ x1;  // x2 = input ⊕ x1

// Masked S-box: S(x) = S(x₁ ⊕ x₂)
// Need pre-computed masked tables or secure computation
uint8_t y1 = MaskedSBox_part1[x1][x2];
uint8_t y2 = MaskedSBox_part2[x1][x2];
// Result: y = y₁ ⊕ y₂ = SBox[plaintext ^ key]

// Properties:
// - Each share individually is random
// - Power consumption of one share reveals nothing
// - Attack requires combining both shares (higher-order DPA)

// HIGHER-ORDER MASKING:
// d-order masking uses d+1 shares
// Requires d+1-order DPA to attack (exponentially harder)
```

### 3.2 Hiding

```
Hiding Countermeasures:

Random Delays:
├── Insert random wait cycles
├── Desynchronizes traces
└── Defeated by trace alignment

Shuffling:
├── Randomize operation order
├── E.g., process S-box bytes in random order
└── Increases traces needed

Noise Addition:
├── Random operations consuming power
├── Degrades SNR
└── Combined with masking

Dual-Rail Logic:
├── Every bit has complement signal
├── Constant Hamming weight
├── Hardware implementation
```

## TERAS Decision G-04

**FOR TERAS:**
1. Document power analysis threat for each product
2. Use masked implementations for constrained devices
3. Recommend HSM for high-value key operations
4. Implement power analysis testing for MENARA components

### Architecture Decision ID: `TERAS-ARCH-G04-POWER-001`

---

# G-05: Electromagnetic Analysis

## 1. EM Side-Channel Fundamentals

### 1.1 EM Emission Sources

```
┌─────────────────────────────────────────────────────────────────────┐
│                    EM Emission Sources                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Current Flow → Magnetic Field (Ampère's Law)                      │
│  B = μ₀I / (2πr)                                                   │
│                                                                     │
│  Voltage Changes → Electric Field (Faraday's Law)                  │
│  E = -dΦ/dt                                                        │
│                                                                     │
│  Emission Sources:                                                  │
│  ├── Power/Ground traces: Carry supply current                     │
│  ├── Signal traces: Data-dependent currents                        │
│  ├── Bond wires: Package inductance                                │
│  ├── On-chip interconnects: Local emissions                        │
│  └── Decoupling capacitors: Resonance effects                      │
│                                                                     │
│  Advantages over Power Analysis:                                    │
│  ├── Can probe specific chip regions (near-field)                  │
│  ├── May bypass power filtering                                    │
│  ├── Can work at distance (far-field)                              │
│  └── Multiple probe positions = multiple channels                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Measurement Setup

```
Near-Field EM Probe Setup:

┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  ┌─────────────┐                                                   │
│  │ Amplifier   │◄─── Low-noise amplifier (30-60 dB)               │
│  └──────┬──────┘                                                   │
│         │                                                           │
│  ┌──────▼──────┐                                                   │
│  │ Oscilloscope│◄─── High sample rate (1+ GSa/s)                  │
│  │ / SDR       │     High bandwidth (500+ MHz)                     │
│  └──────┬──────┘                                                   │
│         │                                                           │
│         ▼                                                           │
│  ┌─────────────┐                                                   │
│  │ EM Probe    │◄─── Small loop or H-field probe                  │
│  │ ○           │     Position: 1-5mm from chip                    │
│  └──────┬──────┘                                                   │
│         │                                                           │
│  ┌──────▼──────┐                                                   │
│  │ Target      │◄─── DUT (Device Under Test)                      │
│  │ Device      │                                                   │
│  └─────────────┘                                                   │
│                                                                     │
│  Trigger: Synchronize capture with crypto operation                 │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. EM Attack Variants

### 2.1 DEMA (Differential EM Analysis)

```
DEMA on AES (similar to DPA):

1. Position probe over target area (e.g., AES unit)
2. Collect EM traces for many encryptions
3. Apply DPA statistical analysis to EM traces
4. Correlation reveals key bits

Advantage: Can focus on specific chip area
- Position over crypto block → better SNR
- Avoid noise from unrelated logic
```

### 2.2 SEMA (Simple EM Analysis)

```
SEMA Attack Example:

RSA Exponentiation EM Trace:
- Different operations have distinct EM signatures
- Square vs multiply may be distinguishable
- Key bits directly visible

ECC Scalar Multiplication:
- Point addition vs doubling
- Conditional operations visible
```

## 3. Far-Field EM Attacks

### 3.1 Van Eck Phreaking (TEMPEST)

```
Unintentional EM Radiation:

Display Emanations:
├── CRT: Raster scan EM emissions
├── LCD: LVDS cable emissions
├── HDMI: Cable radiation
└── Reconstructed at distance (10+ meters)

Keyboard/Mouse:
├── Wireless: RF interception
├── Wired USB: Power line radiation
└── PS/2: Direct cable emission

Mitigation:
├── TEMPEST shielding (conductive enclosure)
├── Emission filtering
├── Zone control (secure areas)
└── Font-based defenses (for displays)
```

## TERAS Decision G-05

**FOR TERAS:**
1. Consider EM threats for hardware deployments
2. Recommend shielded enclosures for sensitive operations
3. Same countermeasures as power analysis apply
4. Document EM requirements for high-security deployments

### Architecture Decision ID: `TERAS-ARCH-G05-EM-001`

---

# G-06: Acoustic Side Channels

## 1. Acoustic Emanations

### 1.1 Sources and Attacks

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Acoustic Side-Channel Sources                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  CPU/Computer:                                                      │
│  ├── Capacitor whine (coil whine)                                  │
│  │   - Piezoelectric effect in ceramic capacitors                  │
│  │   - Frequency modulated by workload                             │
│  │   - RSA key extraction demonstrated (Genkin et al.)             │
│  │                                                                  │
│  ├── Fan noise modulation                                          │
│  │   - Speed varies with computation                               │
│  │   - Coarse-grained information leak                             │
│  │                                                                  │
│  └── Hard drive noise                                              │
│      - Seek patterns reveal file access                            │
│      - Encryption key recovery possible                            │
│                                                                     │
│  Keyboards:                                                         │
│  ├── Each key has distinct acoustic signature                      │
│  ├── Keystroke recognition from audio                              │
│  ├── 80%+ accuracy demonstrated                                    │
│  └── Works over VoIP, phone calls                                  │
│                                                                     │
│  Printers:                                                          │
│  ├── Dot-matrix: Direct character recognition                      │
│  └── Inkjet/laser: Page content inference                          │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 RSA Key Extraction via Acoustics

```
Genkin et al. Attack (2013):

Target: GnuPG RSA decryption
Equipment: Parabolic microphone or phone

Attack:
1. Record acoustic emanations during decryption
2. Chosen-ciphertext attack sends crafted messages
3. Different ciphertexts cause different acoustic patterns
4. Frequency analysis reveals key bits
5. Full 4096-bit RSA key extracted

Distance: Up to 4 meters with parabolic mic
Time: ~1 hour of adaptive queries

Mitigation:
├── Constant-time implementation
├── Acoustic shielding
├── Noise masking
└── Use acoustic-resistant algorithms
```

## 2. Ultrasonic Channels

### 2.1 Covert Communication

```
Air-Gap Exfiltration via Ultrasonics:

Transmission:
├── Software modulates speaker output at >18kHz
├── Inaudible to humans
├── Detectable by nearby microphones
└── Data rates: ~20 bits/second

Reception:
├── Smartphone, laptop with mic
├── Software demodulates signal
└── No network connection required

Demonstrated Attacks:
├── Exfiltration from air-gapped systems
├── Tracking via ultrasonic beacons
└── Cross-device communication
```

## TERAS Decision G-06

**FOR TERAS:**
1. Consider acoustic threats in threat model
2. Recommend acoustic isolation for high-security
3. Use constant-time crypto (addresses multiple channels)
4. Document acoustic requirements for secure facilities

### Architecture Decision ID: `TERAS-ARCH-G06-ACOUSTIC-001`

---

# G-07: Network Timing Attacks

## 1. Remote Timing Attacks

### 1.1 Brumley-Boneh Attack (2003)

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Remote SSL/TLS Timing Attack                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Target: RSA decryption in SSL/TLS handshake                       │
│                                                                     │
│  Attack:                                                            │
│  1. Send crafted ciphertext to server                              │
│  2. Measure response time over network                             │
│  3. Timing reveals information about private key                   │
│                                                                     │
│  Challenges:                                                        │
│  ├── Network jitter adds noise                                     │
│  ├── Server processing variance                                    │
│  └── Need many samples (thousands)                                 │
│                                                                     │
│  Results:                                                           │
│  ├── Extract RSA key over LAN: practical                           │
│  ├── Over WAN: more samples needed                                 │
│  └── OpenSSL vulnerable until patched                              │
│                                                                     │
│  Mitigation: RSA blinding                                           │
│  c' = c × r^e mod n  (random r)                                    │
│  m' = (c')^d mod n                                                 │
│  m = m' × r^(-1) mod n                                             │
│  → Timing independent of actual c                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Lucky Thirteen Attack (2013)

```
TLS CBC-Mode Timing Attack:

CBC-MAC Verification Timing:
1. TLS computes MAC over decrypted plaintext
2. MAC computation time depends on plaintext length
3. Padding errors reveal length information
4. Chosen-ciphertext attack recovers plaintext

Attack Steps:
1. Intercept TLS ciphertext
2. Modify ciphertext, submit to server
3. Measure time until alert
4. Time difference reveals padding validity
5. Recover plaintext byte-by-byte

Impact:
├── Decrypt HTTPS cookies
├── Break authentication tokens
└── Affected all TLS implementations

Mitigation:
├── Constant-time MAC verification
├── Encrypt-then-MAC (TLS 1.2 extension)
└── AEAD modes (GCM, ChaCha20-Poly1305)
```

## 2. Microservice Timing Attacks

### 2.1 Internal Network Attacks

```
Cloud/Microservice Timing:

Attack Surface:
├── Service-to-service calls
├── Database query timing
├── Cache hit vs miss
├── Authentication timing

Example: Database Timing
- Query for user "admin": 10ms (exists, full check)
- Query for user "xyz": 5ms (not found, early exit)
→ User enumeration via timing

Example: Password Comparison
- Compare "password123" vs actual: fail at position 1
- Compare "passxxxxxx" vs actual: fail at position 5
→ Timing reveals correct prefix length

Mitigation:
├── Constant-time comparisons
├── Rate limiting
├── Artificial delays (noise)
└── Cache warming
```

## 3. DNS and Routing Attacks

### 3.1 Traffic Analysis

```
Traffic Analysis (not content, just metadata):

Observable:
├── Packet sizes
├── Packet timing
├── Connection patterns
├── DNS queries

Attacks:
├── Website fingerprinting (even over Tor)
├── User behavior inference
├── Application identification
└── Keystroke reconstruction (SSH)

SSH Keystroke Timing:
- Each keystroke sends packet
- Inter-keystroke timing reveals words
- Can identify passwords
- Mitigation: Random padding, batching
```

## TERAS Decision G-07

**FOR TERAS:**
1. All authentication must be constant-time
2. Add rate limiting to all security-sensitive endpoints
3. Use AEAD modes (no CBC timing issues)
4. Document timing attack mitigations for each product

### Architecture Decision ID: `TERAS-ARCH-G07-NETWORK-001`

---

# G-08: Speculative Execution Attacks (Deep Dive)

## 1. Comprehensive Spectre/Meltdown Coverage

### 1.1 Attack Family Tree

```
┌─────────────────────────────────────────────────────────────────────┐
│             Transient Execution Attack Family                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  SPECTRE (Speculative Execution)                                    │
│  ├── Spectre-V1: Bounds Check Bypass (BCB)                         │
│  │   └── Variant: Spectre-PHT (Pattern History Table)              │
│  │                                                                  │
│  ├── Spectre-V2: Branch Target Injection (BTI)                     │
│  │   └── Variant: Spectre-BTB (Branch Target Buffer)               │
│  │                                                                  │
│  ├── Spectre-V4: Speculative Store Bypass (SSB)                    │
│  │                                                                  │
│  ├── Spectre-RSB: Return Stack Buffer                              │
│  │   └── ret2spec, SpectreRSB                                      │
│  │                                                                  │
│  ├── Spectre-STL: Speculative Store-to-Load                        │
│  │                                                                  │
│  └── Spectre-BHB: Branch History Buffer (2022)                     │
│                                                                     │
│  MELTDOWN (Fault Handling)                                          │
│  ├── Meltdown-US: User-Space read of kernel                        │
│  ├── Meltdown-P: Kernel read of protected pages                    │
│  ├── Meltdown-GP: General Protection fault                         │
│  ├── Meltdown-NM: FP/SIMD state                                    │
│  ├── Meltdown-BR: Bounds Check fault                               │
│  ├── Meltdown-SS: Stack Segment fault                              │
│  └── Meltdown-RW: Read-only Write                                  │
│                                                                     │
│  MDS (Microarchitectural Data Sampling)                             │
│  ├── RIDL: Rogue In-flight Data Load                               │
│  ├── Fallout: Store Buffer leak                                    │
│  ├── ZombieLoad: Fill Buffer leak                                  │
│  └── TAA: TSX Asynchronous Abort                                   │
│                                                                     │
│  OTHER                                                              │
│  ├── LVI: Load Value Injection                                     │
│  ├── CacheOut: L1 Data Eviction Sampling                          │
│  ├── SGAxe: Enhanced SGX attack                                    │
│  ├── ÆPIC Leak: APIC register disclosure                          │
│  ├── Downfall: AVX Gather leak                                     │
│  ├── Inception: Phantom speculation                                │
│  └── Zenbleed: AMD register leak                                   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Spectre-PHT Deep Dive

```c
// Detailed Spectre-V1 gadget analysis

// GADGET TYPE 1: Direct array access
if (x < array1_size) {        // Bounds check
    temp = array1[x];          // Speculative OOB read
    temp2 = array2[temp * 256]; // Transmit via cache
}

// GADGET TYPE 2: Indirect array access
if (x < array1_size) {
    idx = ptr_array[x];        // Speculative OOB read
    temp = array2[idx * 256];  // Transmit via cache
}

// GADGET TYPE 3: Spectre 1.1 (Bounds Check Store)
if (x < array_size) {
    array[x] = value;          // Speculative OOB write
}
// Overwrites return address, function pointer, etc.

// GADGET TYPE 4: Spectre 1.2 (Read-only bypass)
if (x < readonly_array_size) {
    y = readonly_array[x];     // Spec bypass of read-only check
}

// Detection patterns for TERAS:
// - Array access after bounds check
// - User input flows to array index
// - Speculative window between check and use
```

### 1.3 Comprehensive Mitigations

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Speculative Execution Mitigations                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  SOFTWARE MITIGATIONS:                                              │
│  ├── Serialization barriers                                        │
│  │   ├── lfence: Load fence (Intel)                               │
│  │   ├── csdb: Consumption of Speculative Data Barrier (ARM)      │
│  │   └── sb: Speculation Barrier (ARM)                            │
│  │                                                                  │
│  ├── Index masking                                                 │
│  │   └── x &= (x < bound) - 1                                     │
│  │                                                                  │
│  ├── Pointer poisoning                                             │
│  │   └── Clear speculative pointer bits                           │
│  │                                                                  │
│  └── Retpoline (for V2)                                            │
│      └── Replace indirect branches with return trampoline          │
│                                                                     │
│  HARDWARE MITIGATIONS (CPU microcode/features):                     │
│  ├── IBRS: Indirect Branch Restricted Speculation                  │
│  ├── eIBRS: Enhanced IBRS (always-on)                              │
│  ├── IBPB: Indirect Branch Predictor Barrier                       │
│  ├── STIBP: Single Thread Indirect Branch Predictors               │
│  ├── SSBD: Speculative Store Bypass Disable                        │
│  ├── VERW: Clear CPU buffers (MDS)                                 │
│  └── BHI_DIS_S: Branch History Injection disable                   │
│                                                                     │
│  OS MITIGATIONS:                                                    │
│  ├── KPTI: Kernel Page Table Isolation (Meltdown)                  │
│  ├── Process isolation improvements                                │
│  └── Syscall hardening                                             │
│                                                                     │
│  COMPILER MITIGATIONS:                                              │
│  ├── Speculative Load Hardening (LLVM)                             │
│  ├── -mspeculative-load-hardening                                  │
│  └── Automatic barrier insertion                                   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. MDS Attacks

### 2.1 RIDL/ZombieLoad/Fallout

```
MDS Attack Mechanism:

Fill Buffers / Line Fill Buffers:
├── Temporary storage for pending memory ops
├── Shared across hyperthreads
├── Data persists after transaction completion
└── Speculative loads can access stale data

Attack:
1. Victim thread accesses secret data
2. Data temporarily in fill buffer
3. Attacker thread (same core) performs load
4. Load faults but data read speculatively
5. Cache side-channel transmits data

Impact:
├── Cross-hyperthread data leakage
├── Kernel data from userspace
├── SGX enclave data
└── VM-to-VM leakage

Mitigation:
├── VERW instruction clears buffers
├── Disable hyperthreading
├── Flush buffers on context switch
└── Hardware fixes in newer CPUs
```

## TERAS Decision G-08

**FOR TERAS:**
1. Enable all available speculative execution mitigations
2. Compile with speculative load hardening
3. Audit code for Spectre gadgets
4. Test with speculation-based attack tools
5. Document performance impact of mitigations

### Architecture Decision ID: `TERAS-ARCH-G08-SPECTRE-001`

---

# G-09: Rowhammer and Memory Attacks

## 1. Rowhammer Fundamentals

### 1.1 DRAM Physics

```
┌─────────────────────────────────────────────────────────────────────┐
│                    DRAM Cell Structure                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Single DRAM Cell:                                                  │
│  ┌─────────────────────────────────┐                               │
│  │  Word Line (Row Select)         │                               │
│  │         ┃                       │                               │
│  │    ┌────╋────┐                  │                               │
│  │    │Transistor│                  │                               │
│  │    └────┬────┘                  │                               │
│  │         │                       │                               │
│  │    ┌────┴────┐                  │                               │
│  │    │Capacitor│ ← Stores charge (0 or 1)                        │
│  │    └────┬────┘                  │                               │
│  │         │                       │                               │
│  │    Bit Line (Column)            │                               │
│  └─────────────────────────────────┘                               │
│                                                                     │
│  Rowhammer Effect:                                                  │
│  ├── Capacitors are tiny (~20nm spacing)                           │
│  ├── Activating a row causes electromagnetic interference          │
│  ├── Adjacent rows lose charge faster                              │
│  ├── Repeated activation → bit flips before refresh                │
│  └── Refresh interval: ~64ms                                       │
│                                                                     │
│  Row Layout:                                                        │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │  Row N-1  │  Row N (aggressor)  │  Row N+1  │  Row N+2      │   │
│  │  (victim) │  ← HAMMER THIS →   │  (victim) │               │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Attack Variants

```
SINGLE-SIDED ROWHAMMER:
- Hammer one row
- Affects adjacent rows
- Less effective than double-sided

DOUBLE-SIDED ROWHAMMER:
- Hammer rows on both sides of victim
- More bit flips
- Requires knowing physical address mapping

ONE-LOCATION HAMMER:
- Hammer single address repeatedly
- Row buffer misses trigger row activation
- Works without clflush

TRRespass (2020):
- Bypass Target Row Refresh (TRR)
- Hammer many rows (not just adjacent)
- "Many-sided" rowhammer

HALF-DOUBLE (2021):
- Hammer row N and N+2
- Affects row N+1 in between
- Bypasses additional mitigations

BLACKSMITH (2021):
- Automated pattern discovery
- Finds optimal hammering patterns
- Defeats all current mitigations
```

### 1.3 Exploitation Techniques

```
Page Table Attack:
1. Spray memory with page table entries
2. Find PTE at known physical address
3. Hammer to flip bit in PTE
4. Gain arbitrary read/write via modified PTE

OpCode Flipping:
1. Place carefully crafted code in memory
2. Hammer to flip specific bits
3. Turn "safe" instruction into "dangerous" one
4. JNE (0x75) → JMP (0x74) with single bit flip

RSA Key Corruption:
1. Identify RSA key in memory
2. Hammer to flip bit in public exponent or modulus
3. Faulty signatures leak private key (fault attack)

VM Escape:
1. Co-locate VMs on same physical host
2. Hammer to corrupt hypervisor structures
3. Escape to host or other VMs
```

## 2. Countermeasures

### 2.1 Hardware Mitigations

```
Target Row Refresh (TRR):
├── Track most-accessed rows
├── Refresh their neighbors
├── Implemented in DRAM controller
└── BYPASSED by TRRespass, Half-Double

ECC Memory:
├── Detect single-bit errors
├── Correct single-bit errors
├── Cannot handle multi-bit flips
└── ECCploit: Timing leak reveals ECC bits

Increased Refresh Rate:
├── Refresh more often
├── Reduces bit flip window
├── Performance and power cost
└── Not complete mitigation

PARA (Probabilistic Adjacent Row Activation):
├── Randomly refresh neighbors
├── Probabilistic defense
└── Increases difficulty
```

### 2.2 Software Mitigations

```
Memory Isolation:
├── Don't share physical memory with untrusted
├── Guard rows between security domains
├── Reserve rows as buffers

Flush Prevention:
├── Restrict clflush instruction
├── Makes single-sided harder
└── Doesn't prevent all variants

Address Obfuscation:
├── Randomize physical addresses
├── Makes targeting specific rows harder
└── Not complete solution
```

## TERAS Decision G-09

**FOR TERAS:**
1. Recommend ECC memory for high-security deployments
2. Design for memory isolation (separate security domains)
3. Consider Rowhammer in threat model for cloud deployments
4. Monitor for new Rowhammer variants and mitigations

### Architecture Decision ID: `TERAS-ARCH-G09-ROWHAMMER-001`

---

# G-10: Fault Injection Attacks

## 1. Voltage and Clock Glitching

### 1.1 Voltage Glitching

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Voltage Glitching Attack                          │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Normal Operation:                                                  │
│  Vdd ──────────────────────────────────────────                    │
│                                                                     │
│  Glitch:                                                            │
│  Vdd ──────┐      ┌─────────────────────────                       │
│            │      │                                                 │
│            │      │  ← Voltage drop causes timing violation        │
│            └──────┘                                                 │
│                ↑                                                    │
│            Glitch window (~10-100ns)                               │
│                                                                     │
│  Effect:                                                            │
│  ├── Logic gates fail to switch properly                           │
│  ├── Register values corrupted                                     │
│  ├── Instructions skipped or corrupted                             │
│  └── Security checks bypassed                                      │
│                                                                     │
│  Equipment:                                                         │
│  ├── FPGA-based glitcher (ChipWhisperer)                          │
│  ├── Custom power supply with fast switching                       │
│  └── Precise timing (synchronized to target clock)                 │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Clock Glitching

```
Clock Glitching:

Normal:
CLK ──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──
      └──┘  └──┘  └──┘  └──┘  └──┘

Glitch (extra edge):
CLK ──┐  ┌──┐  ┌┐┌──┐  ┌──┐  ┌──┐  ┌──
      └──┘  └──┘└┘  └──┘  └──┘  └──┘
                ↑
            Extra clock edge

Glitch (shortened period):
CLK ──┐  ┌──┐  ┌┐  ┌──┐  ┌──┐  ┌──
      └──┘  └──┘└──┘  └──┘  └──┘
              ↑
         Short period

Effect:
├── Setup/hold time violations
├── Incorrect data captured in registers
├── Instruction fetch errors
└── Branch misprediction forcing
```

## 2. Laser Fault Injection

### 2.1 Optical Fault Induction

```
Laser Fault Attack:

Equipment:
├── Pulsed laser (typically 1064nm IR)
├── XY positioning stage
├── Microscope for targeting
├── Synchronization with target clock
└── Chip decapsulation (for frontside)

Mechanism:
├── Photons generate electron-hole pairs
├── Transient current in transistors
├── Single-bit or multi-bit faults
├── Very precise spatial targeting

Backside Attack:
├── Target through silicon substrate
├── No decapsulation needed (thinner silicon)
├── Requires IR-transparent path
└── Modern defense: backside shields

Applications:
├── Skip security checks
├── Corrupt cryptographic computations
├── Force specific branch outcomes
├── Read protected memory
```

### 2.2 EM Fault Injection

```
Electromagnetic Fault Injection:

Equipment:
├── High-power EM pulse generator
├── Small coil/antenna near chip
├── Precise timing control
└── No physical contact needed

Mechanism:
├── Induced currents in chip traces
├── Similar effect to voltage glitch
├── Can target specific chip areas
└── Works through packaging

Advantages:
├── Non-invasive (no decapsulation)
├── Can work at short distance
├── Harder to detect
└── Complements other techniques
```

## 3. Fault Attack on Cryptography

### 3.1 Differential Fault Analysis (DFA)

```
DFA on AES:

Attack:
1. Obtain correct ciphertext C
2. Inject fault in round 8 or 9
3. Obtain faulty ciphertext C'
4. Analyze difference: C ⊕ C'

Mathematics:
├── Fault in one byte propagates through MixColumns
├── Known propagation pattern constrains key space
├── Multiple faults → unique key recovery
└── Requires ~2-8 faulty ciphertexts

Countermeasures:
├── Redundant computation
├── Check ciphertext against re-encryption
├── Infection countermeasures
└── Error detection codes
```

### 3.2 Bellcore Attack on RSA-CRT

```
RSA-CRT Fault Attack:

RSA-CRT Optimization:
m_p = c^(d mod (p-1)) mod p
m_q = c^(d mod (q-1)) mod q
m = CRT(m_p, m_q)

Attack:
1. Inject fault during m_p computation
2. Get faulty signature s' (correct m_q, wrong m_p)
3. Compute: gcd(s'^e - m, n) = p or q
4. Factor n, recover private key

Why it works:
├── s' = CRT(m_p + fault, m_q)
├── (s')^e ≡ m (mod q)  [correct]
├── (s')^e ≢ m (mod p)  [faulty]
└── gcd reveals factor

Countermeasure:
├── Verify signature before releasing
├── sig^e == m? If not, abort
```

## TERAS Decision G-10

**FOR TERAS:**
1. Implement crypto verification (check before output)
2. Document fault attack threats per deployment model
3. Recommend secure hardware for high-value operations
4. Implement redundant computation for critical paths

### Architecture Decision ID: `TERAS-ARCH-G10-FAULT-001`

---

# G-11: Cold Boot and Memory Remanence

## 1. Memory Remanence Attack

### 1.1 DRAM Decay Characteristics

```
┌─────────────────────────────────────────────────────────────────────┐
│                    DRAM Remanence vs Temperature                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Temperature  │  Retention Time  │  Practical Window               │
│  ─────────────┼──────────────────┼─────────────────────────────    │
│  +20°C        │  ~1-2 seconds    │  Marginal for attack            │
│  0°C          │  ~10 seconds     │  Possible with quick reboot     │
│  -20°C        │  ~1 minute       │  Comfortable attack window      │
│  -50°C        │  ~10 minutes     │  Ample time for imaging         │
│  -196°C (LN2) │  Hours+          │  Remove DIMMs, analyze offline  │
│                                                                     │
│  Cooling Methods:                                                   │
│  ├── Compressed air (inverted can): -50°C briefly                  │
│  ├── Freeze spray: -40°C sustained                                 │
│  ├── Liquid nitrogen: -196°C                                       │
│  └── Thermoelectric cooler: -30°C controlled                       │
│                                                                     │
│  Attack Procedure:                                                  │
│  1. Target system running with keys in memory                      │
│  2. Cool DRAM modules                                              │
│  3. Power cycle or cold reset                                      │
│  4. Boot from USB to forensic imager                               │
│  5. Dump physical memory                                           │
│  6. Search for cryptographic keys                                  │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Key Finding Techniques

```
Finding Keys in Memory:

AES Key Schedules:
├── Characteristic expansion pattern
├── Round keys have known relationships
├── AESKeyFinder: Automated search tool
└── Search for key schedule structure

RSA Private Keys:
├── Look for prime factors p, q
├── ASN.1 DER structure markers
├── Large integers with specific properties
└── RSAKeyFinder tool

Disk Encryption Keys:
├── BitLocker: FVEK in specific structure
├── LUKS: Master key in memory
├── FileVault: Volume key derivation
└── VeraCrypt: Key in specific location
```

## 2. Countermeasures

### 2.1 Software Mitigations

```c
// TRESOR: Keys in CPU registers only
// Store AES key in debug registers (DR0-DR3)
// Never in RAM

// Limitations:
// - Only 128/256 bits available
// - Requires kernel modification
// - Incompatible with debugging

// Loop Amnesia: Continuous key derivation
// Key = PBKDF2(password, hardware_state)
// Re-derive on each use, never store

// Memory encryption software (dm-crypt with CPU key)
// Encrypt all RAM contents
// Key derived from password + PCR values
```

### 2.2 Hardware Mitigations

```
Intel TME (Total Memory Encryption):
├── AES-XTS encryption of all DRAM
├── Key generated at boot, stored in CPU
├── Transparent to software
└── Cold boot sees only ciphertext

AMD SME (Secure Memory Encryption):
├── Similar to Intel TME
├── Per-page encryption keys possible
└── Integrated with SEV for VMs

Memory Scrubbing:
├── BIOS/firmware option
├── Clears memory on cold boot
├── Does NOT help with power removal attack

Physical Countermeasures:
├── Solder DIMMs (prevent removal)
├── Tamper-responsive enclosure
├── Intrusion detection → key zeroization
```

## TERAS Decision G-11

**FOR TERAS:**
1. Recommend memory encryption (TME/SME) where available
2. Design for immediate key zeroization on shutdown
3. Minimize key presence in RAM (derive on demand)
4. Document physical security requirements

### Architecture Decision ID: `TERAS-ARCH-G11-COLDBOOT-001`

---

# G-12: Website and Traffic Fingerprinting

## 1. Website Fingerprinting

### 1.1 Attack on Encrypted Traffic

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Website Fingerprinting Attack                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Scenario:                                                          │
│  ├── User visits website over HTTPS or Tor                         │
│  ├── Attacker observes encrypted traffic (ISP, network admin)      │
│  ├── Content is encrypted but metadata visible                     │
│  └── Goal: Identify which website user is visiting                 │
│                                                                     │
│  Observable Features:                                               │
│  ├── Packet sizes                                                  │
│  ├── Packet timing                                                 │
│  ├── Packet direction (up/down)                                    │
│  ├── Total transfer size                                           │
│  ├── Burst patterns                                                │
│  └── TCP/TLS handshake characteristics                             │
│                                                                     │
│  Machine Learning Approach:                                         │
│  1. Collect traffic traces for known websites                      │
│  2. Extract features from traces                                   │
│  3. Train classifier (CNN, RF, k-NN)                               │
│  4. Classify victim's traffic                                      │
│                                                                     │
│  Accuracy (closed-world):                                           │
│  ├── HTTPS: 90%+ accuracy                                          │
│  ├── Tor: 80-90%+ accuracy (improved attacks)                      │
│  ├── VPN: 85%+ accuracy                                            │
│  └── Open-world (many sites): Lower but still significant          │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Tor Traffic Analysis

```
Tor Circuit:
User → Guard → Middle → Exit → Website

Attack Positions:
├── Guard node: Sees user IP, can fingerprint
├── Exit node: Sees destination, unencrypted data
├── Both: Timing correlation → deanonymize
└── ISP: Fingerprint Tor traffic patterns

Defenses:
├── Traffic padding: Add dummy packets
├── Traffic morphing: Make all sites look similar
├── Random delays: Disrupt timing patterns
└── Pluggable transports: Disguise Tor protocol
```

## 2. Keystroke and Input Timing

### 2.1 SSH Keystroke Analysis

```
SSH Timing Attack:

Observation:
├── Each keystroke sends separate packet
├── Encrypted but size/timing visible
├── Inter-keystroke timing reveals:
│   ├── Typing rhythm (user identification)
│   ├── Word patterns (dictionary attack)
│   └── Password structure

Attack:
1. Observe timing between SSH packets
2. Model keystroke timing distributions
3. Match against known words/passwords
4. Probabilistic password recovery

Song et al. Results:
├── Reduce password search space by 50%
├── User identification possible
└── Works over Internet
```

## TERAS Decision G-12

**FOR TERAS:**
1. Consider traffic analysis in threat model
2. Implement traffic padding for sensitive operations
3. Document metadata leakage risks
4. Recommend Tor/VPN for sensitive TERAS communications

### Architecture Decision ID: `TERAS-ARCH-G12-TRAFFIC-001`

---

# G-13: Covert and Side Channels in Cloud

## 1. Cloud Side-Channel Threats

### 1.1 Multi-Tenant Risks

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Cloud Side-Channel Attack Surface                 │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Shared Resources (Cross-VM Attack Surface):                        │
│  ├── CPU cache (L3/LLC often shared)                               │
│  ├── Memory bus                                                    │
│  ├── TLB (Translation Lookaside Buffer)                            │
│  ├── Branch predictor state                                        │
│  ├── DRAM row buffer                                               │
│  └── Network infrastructure                                        │
│                                                                     │
│  Demonstrated Attacks:                                              │
│  ├── Hey You, Get Off My Cloud (2009): Co-location detection       │
│  ├── Prime+Probe across VMs: Cache timing attack                   │
│  ├── Flush+Reload on KSM: Dedup enables shared memory             │
│  ├── Rowhammer VM escape: Memory corruption across VMs            │
│  └── Spectre/Meltdown: Speculative execution across boundaries    │
│                                                                     │
│  Cloud Provider Mitigations:                                        │
│  ├── Dedicated hosts (no sharing)                                  │
│  ├── Core/cache isolation                                          │
│  ├── KSM disabled                                                  │
│  ├── Microcode patches (Spectre/Meltdown)                         │
│  └── Hardware refresh cycles                                       │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Container Isolation Issues

```
Container Side Channels:

Shared Kernel:
├── Containers share host kernel
├── Less isolation than VMs
├── procfs/sysfs information leakage
└── Kernel vulnerabilities affect all containers

Cgroup Side Channels:
├── CPU usage visible via cgroups
├── Memory pressure observable
├── I/O patterns inferrable
└── Network namespace doesn't hide timing

Attack Examples:
├── Detect crypto operations via CPU contention
├── Infer database queries from memory/CPU
├── Identify applications from resource patterns
└── Deanonymize Tor exits via timing
```

## 2. Covert Channels in Cloud

### 2.1 Resource-Based Covert Channels

```
Cache Covert Channel:
├── Sender: Access/don't access specific cache sets
├── Receiver: Prime+Probe to detect access
├── Bandwidth: ~100 Kbps demonstrated
└── Cross-VM communication proven

Memory Bus Covert Channel:
├── Sender: Cause memory bus contention
├── Receiver: Measure memory access timing
├── Lower bandwidth but harder to detect
└── Works across VMs

Network Covert Channel:
├── Timing modulation of legitimate traffic
├── Storage in unused packet fields
├── DNS tunneling
└── ICMP payload encoding
```

## TERAS Decision G-13

**FOR TERAS:**
1. Recommend dedicated hosts for high-security workloads
2. Document cloud deployment security requirements
3. Implement timing noise for cloud operations
4. Consider container vs VM isolation tradeoffs

### Architecture Decision ID: `TERAS-ARCH-G13-CLOUD-001`

---

# G-14: Side-Channel Resistant Implementations

## 1. Constant-Time Programming

### 1.1 Principles and Patterns

```c
// PRINCIPLE 1: No secret-dependent branches
// BAD:
if (secret) { do_a(); } else { do_b(); }

// GOOD:
do_a_masked = do_a() & mask;
do_b_masked = do_b() & ~mask;
result = do_a_masked | do_b_masked;

// PRINCIPLE 2: No secret-dependent memory access
// BAD:
result = table[secret_index];

// GOOD:
result = 0;
for (int i = 0; i < TABLE_SIZE; i++) {
    result |= table[i] & ct_mask(i == secret_index);
}

// PRINCIPLE 3: No secret-dependent loop bounds
// BAD:
for (int i = 0; i < secret_length; i++) { ... }

// GOOD:
for (int i = 0; i < MAX_LENGTH; i++) {
    if (ct_lt(i, secret_length)) { ... }
}

// PRINCIPLE 4: No early termination on secrets
// BAD:
if (memcmp(input, secret, len) == 0) { grant(); }

// GOOD:
if (ct_memcmp(input, secret, len) == 0) { grant(); }
```

### 1.2 Constant-Time Primitives Library

```c
// Constant-time comparison (returns 0 if equal)
int ct_compare(const void* a, const void* b, size_t len) {
    const volatile uint8_t* pa = a;
    const volatile uint8_t* pb = b;
    volatile uint8_t diff = 0;
    
    for (size_t i = 0; i < len; i++) {
        diff |= pa[i] ^ pb[i];
    }
    
    return (1 & ((diff - 1) >> 8)) - 1;
}

// Constant-time conditional select
uint64_t ct_select(uint64_t a, uint64_t b, uint64_t choice) {
    // choice must be 0 or 1
    uint64_t mask = (uint64_t)(-(int64_t)choice);
    return (a & mask) | (b & ~mask);
}

// Constant-time conditional swap
void ct_cswap(uint64_t* a, uint64_t* b, uint64_t swap) {
    uint64_t mask = (uint64_t)(-(int64_t)swap);
    uint64_t t = mask & (*a ^ *b);
    *a ^= t;
    *b ^= t;
}

// Constant-time minimum
uint64_t ct_min(uint64_t a, uint64_t b) {
    uint64_t mask = (uint64_t)(-(int64_t)(a < b));
    return (a & mask) | (b & ~mask);
}
```

## 2. Verification Tools

### 2.1 Static Analysis

```
ct-verif (Constant-Time Verifier):
├── Based on LLVM
├── Checks for secret-dependent branches/memory
├── Used by libsodium, OpenSSL
└── Some false positives

dudect:
├── Statistical testing approach
├── Run with random inputs
├── Detect timing variations
└── Black-box testing

timecop:
├── Valgrind-based checker
├── Taint tracking for secrets
├── Detects secret-dependent operations
└── Runtime checking
```

## TERAS Decision G-14

**FOR TERAS:**
1. Provide constant-time primitives library
2. Mandate ct-verif checking for crypto code
3. Include timing tests in CI
4. Document constant-time requirements

### Architecture Decision ID: `TERAS-ARCH-G14-CONSTANT-001`

---

# G-15: Side-Channel Integration for TERAS

## 1. TERAS Side-Channel Defense Strategy

### 1.1 Comprehensive Framework

```
┌─────────────────────────────────────────────────────────────────────┐
│                TERAS Side-Channel Defense Framework                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  LAYER 1: Constant-Time Implementation                              │
│  ├── All crypto operations constant-time                           │
│  ├── No secret-dependent branches                                  │
│  ├── No secret-dependent memory access                             │
│  ├── Verified with ct-verif                                        │
│  └── Tested with dudect                                            │
│                                                                     │
│  LAYER 2: Hardware Feature Utilization                              │
│  ├── AES-NI for AES (no table lookups)                            │
│  ├── CLMUL for GCM multiplication                                  │
│  ├── SHA-NI for hashing                                            │
│  ├── RDRAND/RDSEED for randomness                                  │
│  └── CET for control flow protection                               │
│                                                                     │
│  LAYER 3: Speculative Execution Mitigations                         │
│  ├── Enable IBRS/eIBRS                                             │
│  ├── Enable SSBD                                                   │
│  ├── Retpoline compilation                                         │
│  ├── Speculative Load Hardening                                    │
│  └── KPTI enabled                                                  │
│                                                                     │
│  LAYER 4: Isolation                                                 │
│  ├── Process isolation for crypto                                  │
│  ├── Memory protection (separate pages)                            │
│  ├── Cache partitioning where available                            │
│  └── Core pinning for sensitive operations                         │
│                                                                     │
│  LAYER 5: Operational Security                                      │
│  ├── HSM for key operations (highest security)                     │
│  ├── Memory encryption (TME/SME)                                   │
│  ├── Physical security requirements                                │
│  └── Cloud deployment guidelines                                   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Product-Specific Requirements

```
MENARA (Mobile):
├── Side-channels: Cache timing, power analysis
├── Mitigations:
│   ├── Constant-time crypto (ARM optimized)
│   ├── TrustZone isolation
│   ├── Hardware keystore (StrongBox)
│   └── Minimal crypto in app code
└── Testing: Mobile fuzzing, timing tests

GAPURA (WAF):
├── Side-channels: Network timing, cache timing
├── Mitigations:
│   ├── Constant-time comparison for auth
│   ├── Rate limiting (blurs timing)
│   ├── Worker isolation
│   └── AES-NI for TLS
└── Testing: Remote timing analysis

ZIRAH (EDR):
├── Side-channels: Process monitoring timing
├── Mitigations:
│   ├── Async processing (decouple timing)
│   ├── Kernel-level isolation
│   ├── Random scheduling noise
│   └── Encrypted memory for forensics
└── Testing: Timing analysis of scanning

BENTENG (eKYC):
├── Side-channels: Biometric processing timing, power
├── Mitigations:
│   ├── TEE for biometrics
│   ├── Constant-time face comparison
│   ├── HSM for identity keys
│   └── Isolated processing
└── Testing: Timing attacks on verification

SANDI (Signatures):
├── Side-channels: Signing timing, power analysis
├── Mitigations:
│   ├── HSM for all signing (mandatory)
│   ├── Blinding for RSA
│   ├── Constant-time ECDSA
│   └── Protected timestamp operations
└── Testing: Full side-channel evaluation
```

## 2. Testing and Validation

### 2.1 Side-Channel Test Suite

```
TERAS Side-Channel Test Suite:

TIMING TESTS:
├── ct-verif: Static verification
├── dudect: Statistical timing test
├── Cachegrind: Cache access analysis
└── Custom timing harness

CACHE TESTS:
├── Mastik: Cache attack toolkit
├── Prime+Probe simulation
├── Flush+Reload detection
└── Cross-process cache probing

SPECULATIVE TESTS:
├── Spectre gadget detection (static)
├── Spectre PoC execution
├── MDS vulnerability check
└── Hardware feature verification

POWER/EM TESTS (Hardware labs):
├── ChipWhisperer integration
├── DPA analysis scripts
├── SPA visual inspection
└── EM probe positioning

CI INTEGRATION:
├── All timing tests in CI
├── Cache tests in nightly
├── Spectre scans on PR
└── Annual hardware lab evaluation
```

## TERAS Decision G-15

**FOR TERAS:**
1. Implement 5-layer defense framework
2. Product-specific side-channel requirements
3. Comprehensive testing in CI
4. Annual hardware security evaluation
5. Document all mitigations and residual risks

### Architecture Decision ID: `TERAS-ARCH-G15-INTEGRATE-001`

---

# Domain G Summary: Side-Channel Attacks

| Session | Topic | Decision ID |
|---------|-------|-------------|
| G-01 | Foundations | TERAS-ARCH-G01-FOUNDATION-001 |
| G-02 | Cache Timing | TERAS-ARCH-G02-CACHE-001 |
| G-03 | Branch Timing | TERAS-ARCH-G03-BRANCH-001 |
| G-04 | Power Analysis | TERAS-ARCH-G04-POWER-001 |
| G-05 | EM Analysis | TERAS-ARCH-G05-EM-001 |
| G-06 | Acoustic | TERAS-ARCH-G06-ACOUSTIC-001 |
| G-07 | Network Timing | TERAS-ARCH-G07-NETWORK-001 |
| G-08 | Spectre | TERAS-ARCH-G08-SPECTRE-001 |
| G-09 | Rowhammer | TERAS-ARCH-G09-ROWHAMMER-001 |
| G-10 | Fault Injection | TERAS-ARCH-G10-FAULT-001 |
| G-11 | Cold Boot | TERAS-ARCH-G11-COLDBOOT-001 |
| G-12 | Traffic Analysis | TERAS-ARCH-G12-TRAFFIC-001 |
| G-13 | Cloud Channels | TERAS-ARCH-G13-CLOUD-001 |
| G-14 | Constant-Time | TERAS-ARCH-G14-CONSTANT-001 |
| G-15 | Integration | TERAS-ARCH-G15-INTEGRATE-001 |

## Key Principles

1. **Constant-time is mandatory** for all security-sensitive operations
2. **Hardware features help** but are not sufficient alone
3. **Defense in depth** with multiple layers
4. **Testing is essential** - cannot assume resistance
5. **Document assumptions** for each deployment model

## DOMAIN G: COMPLETE

---

*Research Track Output — Domain G: Side-Channel Attacks*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*

---

**SHA-256**: To be computed
