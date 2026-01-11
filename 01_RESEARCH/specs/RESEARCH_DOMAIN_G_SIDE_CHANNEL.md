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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Side-Channel Attack Taxonomy                      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  TIMING CHANNELS                                                    â”‚
â”‚  â”œâ”€â”€ Cache timing (Prime+Probe, Flush+Reload, Evict+Time)          â”‚
â”‚  â”œâ”€â”€ Branch timing (branch misprediction)                          â”‚
â”‚  â”œâ”€â”€ Memory access timing (DRAM row buffer)                        â”‚
â”‚  â”œâ”€â”€ Network timing (remote timing attacks)                        â”‚
â”‚  â””â”€â”€ Instruction timing (data-dependent operations)                â”‚
â”‚                                                                     â”‚
â”‚  POWER CHANNELS                                                     â”‚
â”‚  â”œâ”€â”€ Simple Power Analysis (SPA)                                   â”‚
â”‚  â”œâ”€â”€ Differential Power Analysis (DPA)                             â”‚
â”‚  â”œâ”€â”€ Correlation Power Analysis (CPA)                              â”‚
â”‚  â”œâ”€â”€ High-Order DPA (masked implementations)                       â”‚
â”‚  â””â”€â”€ Template attacks                                              â”‚
â”‚                                                                     â”‚
â”‚  ELECTROMAGNETIC CHANNELS                                           â”‚
â”‚  â”œâ”€â”€ Simple EM Analysis (SEMA)                                     â”‚
â”‚  â”œâ”€â”€ Differential EM Analysis (DEMA)                               â”‚
â”‚  â”œâ”€â”€ Near-field probing                                            â”‚
â”‚  â””â”€â”€ Far-field analysis                                            â”‚
â”‚                                                                     â”‚
â”‚  ACOUSTIC CHANNELS                                                  â”‚
â”‚  â”œâ”€â”€ Keyboard acoustic emanations                                  â”‚
â”‚  â”œâ”€â”€ CPU acoustic emanations                                       â”‚
â”‚  â”œâ”€â”€ Printer/scanner analysis                                      â”‚
â”‚  â””â”€â”€ Hard drive analysis                                           â”‚
â”‚                                                                     â”‚
â”‚  FAULT INJECTION                                                    â”‚
â”‚  â”œâ”€â”€ Voltage glitching                                             â”‚
â”‚  â”œâ”€â”€ Clock glitching                                               â”‚
â”‚  â”œâ”€â”€ Laser fault injection                                         â”‚
â”‚  â”œâ”€â”€ EM fault injection                                            â”‚
â”‚  â””â”€â”€ Rowhammer (software-induced)                                  â”‚
â”‚                                                                     â”‚
â”‚  SPECULATIVE EXECUTION                                              â”‚
â”‚  â”œâ”€â”€ Spectre variants                                              â”‚
â”‚  â”œâ”€â”€ Meltdown variants                                             â”‚
â”‚  â”œâ”€â”€ MDS (Microarchitectural Data Sampling)                        â”‚
â”‚  â””â”€â”€ LVI (Load Value Injection)                                    â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 2. Kocher's Original Timing Attack (1996)

### 2.1 Attack Principle

```
RSA Timing Attack (Kocher 1996):

Modular Exponentiation: c^d mod n (decryption)

Square-and-Multiply Algorithm:
for each bit b in d (MSB to LSB):
    result = resultÂ² mod n           // Always square
    if b == 1:
        result = result Ã— c mod n    // Conditional multiply

Timing Difference:
â”œâ”€â”€ Bit = 1: Square + Multiply (longer)
â”œâ”€â”€ Bit = 0: Square only (shorter)
â””â”€â”€ Total time leaks exponent bits

Attack:
1. Measure decryption times for many ciphertexts
2. Correlate timing with guessed key bits
3. Recover key one bit at a time
4. Statistical analysis distinguishes bit values

Countermeasures:
â”œâ”€â”€ Montgomery multiplication (constant operations)
â”œâ”€â”€ RSA blinding: c' = c Ã— r^e, d' = (c')^d Ã— r^-1
â”œâ”€â”€ Constant-time implementation
â””â”€â”€ Time padding (noise addition)
```

## 3. Attack Surface Analysis

### 3.1 Observable Channels

```
Channel          â”‚ Bandwidth   â”‚ Distance    â”‚ Equipment
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
CPU cache timing â”‚ ~MB/s       â”‚ Same system â”‚ Software only
Power            â”‚ ~KB/s       â”‚ Contact     â”‚ Oscilloscope
EM (near-field)  â”‚ ~KB/s       â”‚ Centimeters â”‚ EM probe, SDR
EM (far-field)   â”‚ ~B/s        â”‚ Meters      â”‚ Antenna, SDR
Acoustic         â”‚ ~B/s        â”‚ Meters      â”‚ Microphone
Network timing   â”‚ Bits/query  â”‚ Global      â”‚ Network access
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Modern CPU Cache Hierarchy                        â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Core 0                           Core 1                            â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”           â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”           â”‚
â”‚  â”‚    Registers       â”‚           â”‚    Registers       â”‚           â”‚
â”‚  â”‚    ~1 cycle        â”‚           â”‚    ~1 cycle        â”‚           â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤           â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤           â”‚
â”‚  â”‚  L1 Data   L1 Inst â”‚           â”‚  L1 Data   L1 Inst â”‚           â”‚
â”‚  â”‚  32KB      32KB    â”‚           â”‚  32KB      32KB    â”‚           â”‚
â”‚  â”‚  ~4 cycles         â”‚           â”‚  ~4 cycles         â”‚           â”‚
â”‚  â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤           â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤           â”‚
â”‚  â”‚       L2 Cache     â”‚           â”‚       L2 Cache     â”‚           â”‚
â”‚  â”‚       256KB-1MB    â”‚           â”‚       256KB-1MB    â”‚           â”‚
â”‚  â”‚       ~12 cycles   â”‚           â”‚       ~12 cycles   â”‚           â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜           â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜           â”‚
â”‚            â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                      â”‚
â”‚                           â–¼                                         â”‚
â”‚            â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                            â”‚
â”‚            â”‚      L3 Cache (LLC)      â”‚                            â”‚
â”‚            â”‚      8MB-64MB            â”‚                            â”‚
â”‚            â”‚      ~40 cycles          â”‚                            â”‚
â”‚            â”‚      Shared across cores â”‚                            â”‚
â”‚            â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                            â”‚
â”‚                           â”‚                                         â”‚
â”‚                           â–¼                                         â”‚
â”‚            â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                            â”‚
â”‚            â”‚      Main Memory         â”‚                            â”‚
â”‚            â”‚      ~200 cycles         â”‚                            â”‚
â”‚            â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                            â”‚
â”‚                                                                     â”‚
â”‚  Cache Organization:                                                â”‚
â”‚  â”œâ”€â”€ Set-associative (typically 8-16 way)                          â”‚
â”‚  â”œâ”€â”€ Cache line: 64 bytes                                          â”‚
â”‚  â”œâ”€â”€ Inclusive vs exclusive (varies by CPU)                        â”‚
â”‚  â””â”€â”€ Replacement: LRU or pseudo-LRU                                â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 2. Cache Attack Techniques

### 2.1 Prime+Probe

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Prime+Probe Attack                                â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  PRIME Phase (Attacker fills cache set):                           â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  Cache Set N:  [A0][A1][A2][A3][A4][A5][A6][A7]             â”‚   â”‚
â”‚  â”‚                 â–²   â–²   â–²   â–²   â–²   â–²   â–²   â–²              â”‚   â”‚
â”‚  â”‚                 â””â”€â”€â”€â”´â”€â”€â”€â”´â”€â”€â”€â”´â”€â”€â”€â”´â”€â”€â”€â”´â”€â”€â”€â”´â”€â”€â”€â”˜              â”‚   â”‚
â”‚  â”‚                    Attacker's data                          â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  VICTIM Executes (accesses cache):                                  â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  Cache Set N:  [A0][V ][A2][A3][A4][A5][A6][A7]             â”‚   â”‚
â”‚  â”‚                      â–²                                      â”‚   â”‚
â”‚  â”‚                 Victim's data evicts A1                     â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  PROBE Phase (Attacker re-accesses):                               â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  Access A0: FAST (cache hit)                                â”‚   â”‚
â”‚  â”‚  Access A1: SLOW (cache miss) â† VICTIM ACCESSED THIS SET!   â”‚   â”‚
â”‚  â”‚  Access A2: FAST (cache hit)                                â”‚   â”‚
â”‚  â”‚  ...                                                        â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  Requirements:                                                      â”‚
â”‚  â”œâ”€â”€ Know cache geometry (sets, ways)                              â”‚
â”‚  â”œâ”€â”€ Create eviction set (addresses mapping to same set)           â”‚
â”‚  â”œâ”€â”€ No need for shared memory with victim                         â”‚
â”‚  â””â”€â”€ Works across processes, VMs, containers                       â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 2.2 Flush+Reload

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Flush+Reload Attack                               â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Prerequisite: Shared memory between attacker and victim            â”‚
â”‚  (e.g., shared libraries, deduplication)                           â”‚
â”‚                                                                     â”‚
â”‚  FLUSH Phase:                                                       â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  clflush(target_address)                                    â”‚   â”‚
â”‚  â”‚  Evicts target from ALL cache levels                        â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  WAIT for victim to execute                                        â”‚
â”‚                                                                     â”‚
â”‚  RELOAD Phase:                                                      â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  start = rdtsc()                                            â”‚   â”‚
â”‚  â”‚  access(target_address)                                     â”‚   â”‚
â”‚  â”‚  end = rdtsc()                                              â”‚   â”‚
â”‚  â”‚                                                              â”‚   â”‚
â”‚  â”‚  if (end - start < THRESHOLD):                              â”‚   â”‚
â”‚  â”‚      // FAST: Victim accessed this address                  â”‚   â”‚
â”‚  â”‚  else:                                                       â”‚   â”‚
â”‚  â”‚      // SLOW: Victim did NOT access this address            â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  Advantages:                                                        â”‚
â”‚  â”œâ”€â”€ Higher precision than Prime+Probe                             â”‚
â”‚  â”œâ”€â”€ Cache-line granularity (64 bytes)                             â”‚
â”‚  â””â”€â”€ Works across cores                                            â”‚
â”‚                                                                     â”‚
â”‚  Disadvantages:                                                     â”‚
â”‚  â”œâ”€â”€ Requires shared memory                                        â”‚
â”‚  â””â”€â”€ Requires clflush instruction                                  â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
// 5. If cache line for SBox[c ^ k] accessed â†’ deduce key byte k

// For each key byte (16 total):
// - Try all 256 possible key values
// - Measure cache access for SBox[known_ciphertext ^ guess]
// - Cache hit reveals correct key byte
```

### 3.2 RSA Cache Attack

```
RSA Square-and-Multiply with Lookup Table:
- Precomputed table of powers: g, gÂ², gÂ³, ...
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
â”œâ”€â”€ Intel CAT (Cache Allocation Technology)
â”œâ”€â”€ Separate cache partitions for security domains
â””â”€â”€ Prevents cross-tenant cache attacks

Scatter-Gather Tables:
â”œâ”€â”€ AES-NI: Lookup-free AES implementation
â”œâ”€â”€ Vectorized computation
â””â”€â”€ No memory access patterns

Address Space Layout Randomization (ASLR):
â”œâ”€â”€ Randomize memory layout
â”œâ”€â”€ Makes eviction set creation harder
â””â”€â”€ Not sufficient alone (can be defeated)
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Modern Branch Predictor                           â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                    Branch Target Buffer (BTB)                â”‚   â”‚
â”‚  â”‚  - Maps PC to predicted target                              â”‚   â”‚
â”‚  â”‚  - Indexed by PC bits                                       â”‚   â”‚
â”‚  â”‚  - Shared across processes (before mitigations)             â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                  Pattern History Table (PHT)                 â”‚   â”‚
â”‚  â”‚  - 2-bit saturating counters                                â”‚   â”‚
â”‚  â”‚  - Indexed by PC XOR branch history                         â”‚   â”‚
â”‚  â”‚  - Predicts taken/not-taken                                 â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                Branch History Buffer (BHB)                   â”‚   â”‚
â”‚  â”‚  - Records recent branch outcomes                           â”‚   â”‚
â”‚  â”‚  - Global or per-branch                                     â”‚   â”‚
â”‚  â”‚  - Used for correlated prediction                           â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚                Return Stack Buffer (RSB)                     â”‚   â”‚
â”‚  â”‚  - Predicts return addresses                                â”‚   â”‚
â”‚  â”‚  - CALL pushes, RET pops                                    â”‚   â”‚
â”‚  â”‚  - Can underflow/overflow                                   â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
â”œâ”€â”€ Retpoline: Replace indirect branch with return trampoline
â”‚   - JMP *rax becomes:
â”‚     call retpoline_call
â”‚   retpoline_call:
â”‚     mov rax, [rsp]
â”‚     lfence
â”‚     jmp *rax
â”‚     
â”œâ”€â”€ IBRS (Indirect Branch Restricted Speculation)
â”‚   - Prevent userâ†’kernel and VMâ†’hypervisor BTB injection
â”‚   
â”œâ”€â”€ IBPB (Indirect Branch Predictor Barrier)
â”‚   - Flush branch predictor on context switch
â”‚   
â””â”€â”€ eIBRS (Enhanced IBRS)
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
â”œâ”€â”€ RSB stuffing: Fill RSB on context switch
â””â”€â”€ IBRS: Prevents cross-domain RSB attacks
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    CMOS Power Consumption                            â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  P_total = P_static + P_dynamic                                    â”‚
â”‚                                                                     â”‚
â”‚  P_static = V_dd Ã— I_leak  (leakage current)                       â”‚
â”‚                                                                     â”‚
â”‚  P_dynamic = Î± Ã— C Ã— V_ddÂ² Ã— f                                     â”‚
â”‚             â†“   â†“   â†“     â†“                                        â”‚
â”‚             â”‚   â”‚   â”‚     â””â”€â”€ Frequency                            â”‚
â”‚             â”‚   â”‚   â””â”€â”€â”€â”€â”€â”€â”€â”€ Supply voltage                       â”‚
â”‚             â”‚   â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ Capacitance                          â”‚
â”‚             â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ Activity factor (0 to 1 transitions) â”‚
â”‚                                                                     â”‚
â”‚  Key insight: Activity factor depends on DATA being processed      â”‚
â”‚                                                                     â”‚
â”‚  Hamming Weight Model:                                              â”‚
â”‚  P â‰ˆ a Ã— HW(data) + b                                              â”‚
â”‚  where HW(x) = number of 1-bits in x                               â”‚
â”‚                                                                     â”‚
â”‚  Hamming Distance Model:                                            â”‚
â”‚  P â‰ˆ a Ã— HD(old_data, new_data) + b                                â”‚
â”‚  where HD(x,y) = HW(x âŠ• y) = number of differing bits             â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 SPA on RSA

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    SPA Attack on RSA                                 â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Square-and-Multiply Power Trace:                                   â”‚
â”‚                                                                     â”‚
â”‚  Key bits:    1    0    1    1    0    1    0    ...               â”‚
â”‚                                                                     â”‚
â”‚  Power:  â”Œâ”€â”€â”   â”Œâ”€â”€â”   â”Œâ”€â”€â”   â”Œâ”€â”€â”   â”Œâ”€â”€â”   â”Œâ”€â”€â”   â”Œâ”€â”€â”           â”‚
â”‚          â”‚S â”‚   â”‚S â”‚   â”‚S â”‚   â”‚S â”‚   â”‚S â”‚   â”‚S â”‚   â”‚S â”‚           â”‚
â”‚          â”‚  â”‚   â”‚  â”‚   â”‚  â”‚   â”‚  â”‚   â”‚  â”‚   â”‚  â”‚   â”‚  â”‚           â”‚
â”‚          â”‚M â”‚   â”‚  â”‚   â”‚M â”‚   â”‚M â”‚   â”‚  â”‚   â”‚M â”‚   â”‚  â”‚           â”‚
â”‚          â””â”€â”€â”˜   â””â”€â”€â”˜   â””â”€â”€â”˜   â””â”€â”€â”˜   â””â”€â”€â”˜   â””â”€â”€â”˜   â””â”€â”€â”˜           â”‚
â”‚           â–²             â–²     â–²             â–²                       â”‚
â”‚           â”‚             â”‚     â”‚             â”‚                       â”‚
â”‚         Multiply     Multiply Multiply   Multiply                   â”‚
â”‚         visible      visible  visible    visible                    â”‚
â”‚                                                                     â”‚
â”‚  Attack: Visually identify square vs square+multiply patterns       â”‚
â”‚  Key bit = 1 where multiply follows square                         â”‚
â”‚                                                                     â”‚
â”‚  Countermeasure: Always perform multiply (Montgomery ladder)        â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 2. Differential Power Analysis (DPA)

### 2.1 DPA Attack Principle

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    DPA Attack on AES                                 â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Target: First-round S-box output                                   â”‚
â”‚  S_out = SBox[plaintext[i] âŠ• key[i]]                               â”‚
â”‚                                                                     â”‚
â”‚  Attack for one key byte (key[i]):                                  â”‚
â”‚                                                                     â”‚
â”‚  1. Collect N power traces with different plaintexts               â”‚
â”‚     Traces: Tâ‚, Tâ‚‚, Tâ‚ƒ, ..., Tâ‚™                                    â”‚
â”‚     Plaintexts: Pâ‚, Pâ‚‚, Pâ‚ƒ, ..., Pâ‚™                                â”‚
â”‚                                                                     â”‚
â”‚  2. For each key guess k âˆˆ [0, 255]:                               â”‚
â”‚     - Compute hypothetical S-box outputs:                          â”‚
â”‚       H_i = SBox[P_i[byte] âŠ• k]                                    â”‚
â”‚     - Compute hypothetical power: HW(H_i)                          â”‚
â”‚     - Correlate with actual traces                                 â”‚
â”‚                                                                     â”‚
â”‚  3. Correct key guess: High correlation at S-box time              â”‚
â”‚     Wrong key guesses: Low/no correlation                          â”‚
â”‚                                                                     â”‚
â”‚  Correlation:                                                       â”‚
â”‚  Ï = Î£(T_i - TÌ„)(H_i - HÌ„) / âˆš(Î£(T_i - TÌ„)Â² Ã— Î£(H_i - HÌ„)Â²)         â”‚
â”‚                                                                     â”‚
â”‚  Correct key shows spike at operation time                         â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 2.2 Number of Traces Required

```
Traces needed vs. SNR:

SNR (Signal-to-Noise Ratio) â”‚ Traces for 99% success
â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€
         0.1                â”‚    ~10,000
         0.5                â”‚    ~400
         1.0                â”‚    ~100
         2.0                â”‚    ~25
         5.0                â”‚    ~4

Factors affecting SNR:
â”œâ”€â”€ Measurement equipment quality
â”œâ”€â”€ Device power filtering
â”œâ”€â”€ Algorithmic complexity
â”œâ”€â”€ Masking order
â””â”€â”€ Noise injection
```

## 3. Countermeasures

### 3.1 Masking

```c
// UNMASKED S-box (vulnerable):
uint8_t sbox_output = SBox[plaintext ^ key];

// FIRST-ORDER MASKED:
// Split secret into two shares: x = xâ‚ âŠ• xâ‚‚
uint8_t x1 = random();
uint8_t x2 = (plaintext ^ key) ^ x1;  // x2 = input âŠ• x1

// Masked S-box: S(x) = S(xâ‚ âŠ• xâ‚‚)
// Need pre-computed masked tables or secure computation
uint8_t y1 = MaskedSBox_part1[x1][x2];
uint8_t y2 = MaskedSBox_part2[x1][x2];
// Result: y = yâ‚ âŠ• yâ‚‚ = SBox[plaintext ^ key]

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
â”œâ”€â”€ Insert random wait cycles
â”œâ”€â”€ Desynchronizes traces
â””â”€â”€ Defeated by trace alignment

Shuffling:
â”œâ”€â”€ Randomize operation order
â”œâ”€â”€ E.g., process S-box bytes in random order
â””â”€â”€ Increases traces needed

Noise Addition:
â”œâ”€â”€ Random operations consuming power
â”œâ”€â”€ Degrades SNR
â””â”€â”€ Combined with masking

Dual-Rail Logic:
â”œâ”€â”€ Every bit has complement signal
â”œâ”€â”€ Constant Hamming weight
â”œâ”€â”€ Hardware implementation
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    EM Emission Sources                               â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Current Flow â†’ Magnetic Field (AmpÃ¨re's Law)                      â”‚
â”‚  B = Î¼â‚€I / (2Ï€r)                                                   â”‚
â”‚                                                                     â”‚
â”‚  Voltage Changes â†’ Electric Field (Faraday's Law)                  â”‚
â”‚  E = -dÎ¦/dt                                                        â”‚
â”‚                                                                     â”‚
â”‚  Emission Sources:                                                  â”‚
â”‚  â”œâ”€â”€ Power/Ground traces: Carry supply current                     â”‚
â”‚  â”œâ”€â”€ Signal traces: Data-dependent currents                        â”‚
â”‚  â”œâ”€â”€ Bond wires: Package inductance                                â”‚
â”‚  â”œâ”€â”€ On-chip interconnects: Local emissions                        â”‚
â”‚  â””â”€â”€ Decoupling capacitors: Resonance effects                      â”‚
â”‚                                                                     â”‚
â”‚  Advantages over Power Analysis:                                    â”‚
â”‚  â”œâ”€â”€ Can probe specific chip regions (near-field)                  â”‚
â”‚  â”œâ”€â”€ May bypass power filtering                                    â”‚
â”‚  â”œâ”€â”€ Can work at distance (far-field)                              â”‚
â”‚  â””â”€â”€ Multiple probe positions = multiple channels                  â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Measurement Setup

```
Near-Field EM Probe Setup:

â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                                                                     â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                                                   â”‚
â”‚  â”‚ Amplifier   â”‚â—„â”€â”€â”€ Low-noise amplifier (30-60 dB)               â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”˜                                                   â”‚
â”‚         â”‚                                                           â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â–¼â”€â”€â”€â”€â”€â”€â”                                                   â”‚
â”‚  â”‚ Oscilloscopeâ”‚â—„â”€â”€â”€ High sample rate (1+ GSa/s)                  â”‚
â”‚  â”‚ / SDR       â”‚     High bandwidth (500+ MHz)                     â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”˜                                                   â”‚
â”‚         â”‚                                                           â”‚
â”‚         â–¼                                                           â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                                                   â”‚
â”‚  â”‚ EM Probe    â”‚â—„â”€â”€â”€ Small loop or H-field probe                  â”‚
â”‚  â”‚ â—‹           â”‚     Position: 1-5mm from chip                    â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”€â”€â”˜                                                   â”‚
â”‚         â”‚                                                           â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â–¼â”€â”€â”€â”€â”€â”€â”                                                   â”‚
â”‚  â”‚ Target      â”‚â—„â”€â”€â”€ DUT (Device Under Test)                      â”‚
â”‚  â”‚ Device      â”‚                                                   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                                                   â”‚
â”‚                                                                     â”‚
â”‚  Trigger: Synchronize capture with crypto operation                 â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
- Position over crypto block â†’ better SNR
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
â”œâ”€â”€ CRT: Raster scan EM emissions
â”œâ”€â”€ LCD: LVDS cable emissions
â”œâ”€â”€ HDMI: Cable radiation
â””â”€â”€ Reconstructed at distance (10+ meters)

Keyboard/Mouse:
â”œâ”€â”€ Wireless: RF interception
â”œâ”€â”€ Wired USB: Power line radiation
â””â”€â”€ PS/2: Direct cable emission

Mitigation:
â”œâ”€â”€ TEMPEST shielding (conductive enclosure)
â”œâ”€â”€ Emission filtering
â”œâ”€â”€ Zone control (secure areas)
â””â”€â”€ Font-based defenses (for displays)
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Acoustic Side-Channel Sources                     â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  CPU/Computer:                                                      â”‚
â”‚  â”œâ”€â”€ Capacitor whine (coil whine)                                  â”‚
â”‚  â”‚   - Piezoelectric effect in ceramic capacitors                  â”‚
â”‚  â”‚   - Frequency modulated by workload                             â”‚
â”‚  â”‚   - RSA key extraction demonstrated (Genkin et al.)             â”‚
â”‚  â”‚                                                                  â”‚
â”‚  â”œâ”€â”€ Fan noise modulation                                          â”‚
â”‚  â”‚   - Speed varies with computation                               â”‚
â”‚  â”‚   - Coarse-grained information leak                             â”‚
â”‚  â”‚                                                                  â”‚
â”‚  â””â”€â”€ Hard drive noise                                              â”‚
â”‚      - Seek patterns reveal file access                            â”‚
â”‚      - Encryption key recovery possible                            â”‚
â”‚                                                                     â”‚
â”‚  Keyboards:                                                         â”‚
â”‚  â”œâ”€â”€ Each key has distinct acoustic signature                      â”‚
â”‚  â”œâ”€â”€ Keystroke recognition from audio                              â”‚
â”‚  â”œâ”€â”€ 80%+ accuracy demonstrated                                    â”‚
â”‚  â””â”€â”€ Works over VoIP, phone calls                                  â”‚
â”‚                                                                     â”‚
â”‚  Printers:                                                          â”‚
â”‚  â”œâ”€â”€ Dot-matrix: Direct character recognition                      â”‚
â”‚  â””â”€â”€ Inkjet/laser: Page content inference                          â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
â”œâ”€â”€ Constant-time implementation
â”œâ”€â”€ Acoustic shielding
â”œâ”€â”€ Noise masking
â””â”€â”€ Use acoustic-resistant algorithms
```

## 2. Ultrasonic Channels

### 2.1 Covert Communication

```
Air-Gap Exfiltration via Ultrasonics:

Transmission:
â”œâ”€â”€ Software modulates speaker output at >18kHz
â”œâ”€â”€ Inaudible to humans
â”œâ”€â”€ Detectable by nearby microphones
â””â”€â”€ Data rates: ~20 bits/second

Reception:
â”œâ”€â”€ Smartphone, laptop with mic
â”œâ”€â”€ Software demodulates signal
â””â”€â”€ No network connection required

Demonstrated Attacks:
â”œâ”€â”€ Exfiltration from air-gapped systems
â”œâ”€â”€ Tracking via ultrasonic beacons
â””â”€â”€ Cross-device communication
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Remote SSL/TLS Timing Attack                      â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Target: RSA decryption in SSL/TLS handshake                       â”‚
â”‚                                                                     â”‚
â”‚  Attack:                                                            â”‚
â”‚  1. Send crafted ciphertext to server                              â”‚
â”‚  2. Measure response time over network                             â”‚
â”‚  3. Timing reveals information about private key                   â”‚
â”‚                                                                     â”‚
â”‚  Challenges:                                                        â”‚
â”‚  â”œâ”€â”€ Network jitter adds noise                                     â”‚
â”‚  â”œâ”€â”€ Server processing variance                                    â”‚
â”‚  â””â”€â”€ Need many samples (thousands)                                 â”‚
â”‚                                                                     â”‚
â”‚  Results:                                                           â”‚
â”‚  â”œâ”€â”€ Extract RSA key over LAN: practical                           â”‚
â”‚  â”œâ”€â”€ Over WAN: more samples needed                                 â”‚
â”‚  â””â”€â”€ OpenSSL vulnerable until patched                              â”‚
â”‚                                                                     â”‚
â”‚  Mitigation: RSA blinding                                           â”‚
â”‚  c' = c Ã— r^e mod n  (random r)                                    â”‚
â”‚  m' = (c')^d mod n                                                 â”‚
â”‚  m = m' Ã— r^(-1) mod n                                             â”‚
â”‚  â†’ Timing independent of actual c                                  â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
â”œâ”€â”€ Decrypt HTTPS cookies
â”œâ”€â”€ Break authentication tokens
â””â”€â”€ Affected all TLS implementations

Mitigation:
â”œâ”€â”€ Constant-time MAC verification
â”œâ”€â”€ Encrypt-then-MAC (TLS 1.2 extension)
â””â”€â”€ AEAD modes (GCM, ChaCha20-Poly1305)
```

## 2. Microservice Timing Attacks

### 2.1 Internal Network Attacks

```
Cloud/Microservice Timing:

Attack Surface:
â”œâ”€â”€ Service-to-service calls
â”œâ”€â”€ Database query timing
â”œâ”€â”€ Cache hit vs miss
â”œâ”€â”€ Authentication timing

Example: Database Timing
- Query for user "admin": 10ms (exists, full check)
- Query for user "xyz": 5ms (not found, early exit)
â†’ User enumeration via timing

Example: Password Comparison
- Compare "password123" vs actual: fail at position 1
- Compare "passxxxxxx" vs actual: fail at position 5
â†’ Timing reveals correct prefix length

Mitigation:
â”œâ”€â”€ Constant-time comparisons
â”œâ”€â”€ Rate limiting
â”œâ”€â”€ Artificial delays (noise)
â””â”€â”€ Cache warming
```

## 3. DNS and Routing Attacks

### 3.1 Traffic Analysis

```
Traffic Analysis (not content, just metadata):

Observable:
â”œâ”€â”€ Packet sizes
â”œâ”€â”€ Packet timing
â”œâ”€â”€ Connection patterns
â”œâ”€â”€ DNS queries

Attacks:
â”œâ”€â”€ Website fingerprinting (even over Tor)
â”œâ”€â”€ User behavior inference
â”œâ”€â”€ Application identification
â””â”€â”€ Keystroke reconstruction (SSH)

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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚             Transient Execution Attack Family                        â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  SPECTRE (Speculative Execution)                                    â”‚
â”‚  â”œâ”€â”€ Spectre-V1: Bounds Check Bypass (BCB)                         â”‚
â”‚  â”‚   â””â”€â”€ Variant: Spectre-PHT (Pattern History Table)              â”‚
â”‚  â”‚                                                                  â”‚
â”‚  â”œâ”€â”€ Spectre-V2: Branch Target Injection (BTI)                     â”‚
â”‚  â”‚   â””â”€â”€ Variant: Spectre-BTB (Branch Target Buffer)               â”‚
â”‚  â”‚                                                                  â”‚
â”‚  â”œâ”€â”€ Spectre-V4: Speculative Store Bypass (SSB)                    â”‚
â”‚  â”‚                                                                  â”‚
â”‚  â”œâ”€â”€ Spectre-RSB: Return Stack Buffer                              â”‚
â”‚  â”‚   â””â”€â”€ ret2spec, SpectreRSB                                      â”‚
â”‚  â”‚                                                                  â”‚
â”‚  â”œâ”€â”€ Spectre-STL: Speculative Store-to-Load                        â”‚
â”‚  â”‚                                                                  â”‚
â”‚  â””â”€â”€ Spectre-BHB: Branch History Buffer (2022)                     â”‚
â”‚                                                                     â”‚
â”‚  MELTDOWN (Fault Handling)                                          â”‚
â”‚  â”œâ”€â”€ Meltdown-US: User-Space read of kernel                        â”‚
â”‚  â”œâ”€â”€ Meltdown-P: Kernel read of protected pages                    â”‚
â”‚  â”œâ”€â”€ Meltdown-GP: General Protection fault                         â”‚
â”‚  â”œâ”€â”€ Meltdown-NM: FP/SIMD state                                    â”‚
â”‚  â”œâ”€â”€ Meltdown-BR: Bounds Check fault                               â”‚
â”‚  â”œâ”€â”€ Meltdown-SS: Stack Segment fault                              â”‚
â”‚  â””â”€â”€ Meltdown-RW: Read-only Write                                  â”‚
â”‚                                                                     â”‚
â”‚  MDS (Microarchitectural Data Sampling)                             â”‚
â”‚  â”œâ”€â”€ RIDL: Rogue In-flight Data Load                               â”‚
â”‚  â”œâ”€â”€ Fallout: Store Buffer leak                                    â”‚
â”‚  â”œâ”€â”€ ZombieLoad: Fill Buffer leak                                  â”‚
â”‚  â””â”€â”€ TAA: TSX Asynchronous Abort                                   â”‚
â”‚                                                                     â”‚
â”‚  OTHER                                                              â”‚
â”‚  â”œâ”€â”€ LVI: Load Value Injection                                     â”‚
â”‚  â”œâ”€â”€ CacheOut: L1 Data Eviction Sampling                          â”‚
â”‚  â”œâ”€â”€ SGAxe: Enhanced SGX attack                                    â”‚
â”‚  â”œâ”€â”€ Ã†PIC Leak: APIC register disclosure                          â”‚
â”‚  â”œâ”€â”€ Downfall: AVX Gather leak                                     â”‚
â”‚  â”œâ”€â”€ Inception: Phantom speculation                                â”‚
â”‚  â””â”€â”€ Zenbleed: AMD register leak                                   â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Speculative Execution Mitigations                 â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  SOFTWARE MITIGATIONS:                                              â”‚
â”‚  â”œâ”€â”€ Serialization barriers                                        â”‚
â”‚  â”‚   â”œâ”€â”€ lfence: Load fence (Intel)                               â”‚
â”‚  â”‚   â”œâ”€â”€ csdb: Consumption of Speculative Data Barrier (ARM)      â”‚
â”‚  â”‚   â””â”€â”€ sb: Speculation Barrier (ARM)                            â”‚
â”‚  â”‚                                                                  â”‚
â”‚  â”œâ”€â”€ Index masking                                                 â”‚
â”‚  â”‚   â””â”€â”€ x &= (x < bound) - 1                                     â”‚
â”‚  â”‚                                                                  â”‚
â”‚  â”œâ”€â”€ Pointer poisoning                                             â”‚
â”‚  â”‚   â””â”€â”€ Clear speculative pointer bits                           â”‚
â”‚  â”‚                                                                  â”‚
â”‚  â””â”€â”€ Retpoline (for V2)                                            â”‚
â”‚      â””â”€â”€ Replace indirect branches with return trampoline          â”‚
â”‚                                                                     â”‚
â”‚  HARDWARE MITIGATIONS (CPU microcode/features):                     â”‚
â”‚  â”œâ”€â”€ IBRS: Indirect Branch Restricted Speculation                  â”‚
â”‚  â”œâ”€â”€ eIBRS: Enhanced IBRS (always-on)                              â”‚
â”‚  â”œâ”€â”€ IBPB: Indirect Branch Predictor Barrier                       â”‚
â”‚  â”œâ”€â”€ STIBP: Single Thread Indirect Branch Predictors               â”‚
â”‚  â”œâ”€â”€ SSBD: Speculative Store Bypass Disable                        â”‚
â”‚  â”œâ”€â”€ VERW: Clear CPU buffers (MDS)                                 â”‚
â”‚  â””â”€â”€ BHI_DIS_S: Branch History Injection disable                   â”‚
â”‚                                                                     â”‚
â”‚  OS MITIGATIONS:                                                    â”‚
â”‚  â”œâ”€â”€ KPTI: Kernel Page Table Isolation (Meltdown)                  â”‚
â”‚  â”œâ”€â”€ Process isolation improvements                                â”‚
â”‚  â””â”€â”€ Syscall hardening                                             â”‚
â”‚                                                                     â”‚
â”‚  COMPILER MITIGATIONS:                                              â”‚
â”‚  â”œâ”€â”€ Speculative Load Hardening (LLVM)                             â”‚
â”‚  â”œâ”€â”€ -mspeculative-load-hardening                                  â”‚
â”‚  â””â”€â”€ Automatic barrier insertion                                   â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

## 2. MDS Attacks

### 2.1 RIDL/ZombieLoad/Fallout

```
MDS Attack Mechanism:

Fill Buffers / Line Fill Buffers:
â”œâ”€â”€ Temporary storage for pending memory ops
â”œâ”€â”€ Shared across hyperthreads
â”œâ”€â”€ Data persists after transaction completion
â””â”€â”€ Speculative loads can access stale data

Attack:
1. Victim thread accesses secret data
2. Data temporarily in fill buffer
3. Attacker thread (same core) performs load
4. Load faults but data read speculatively
5. Cache side-channel transmits data

Impact:
â”œâ”€â”€ Cross-hyperthread data leakage
â”œâ”€â”€ Kernel data from userspace
â”œâ”€â”€ SGX enclave data
â””â”€â”€ VM-to-VM leakage

Mitigation:
â”œâ”€â”€ VERW instruction clears buffers
â”œâ”€â”€ Disable hyperthreading
â”œâ”€â”€ Flush buffers on context switch
â””â”€â”€ Hardware fixes in newer CPUs
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    DRAM Cell Structure                               â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Single DRAM Cell:                                                  â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”                               â”‚
â”‚  â”‚  Word Line (Row Select)         â”‚                               â”‚
â”‚  â”‚         â”ƒ                       â”‚                               â”‚
â”‚  â”‚    â”Œâ”€â”€â”€â”€â•‹â”€â”€â”€â”€â”                  â”‚                               â”‚
â”‚  â”‚    â”‚Transistorâ”‚                  â”‚                               â”‚
â”‚  â”‚    â””â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”˜                  â”‚                               â”‚
â”‚  â”‚         â”‚                       â”‚                               â”‚
â”‚  â”‚    â”Œâ”€â”€â”€â”€â”´â”€â”€â”€â”€â”                  â”‚                               â”‚
â”‚  â”‚    â”‚Capacitorâ”‚ â† Stores charge (0 or 1)                        â”‚
â”‚  â”‚    â””â”€â”€â”€â”€â”¬â”€â”€â”€â”€â”˜                  â”‚                               â”‚
â”‚  â”‚         â”‚                       â”‚                               â”‚
â”‚  â”‚    Bit Line (Column)            â”‚                               â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜                               â”‚
â”‚                                                                     â”‚
â”‚  Rowhammer Effect:                                                  â”‚
â”‚  â”œâ”€â”€ Capacitors are tiny (~20nm spacing)                           â”‚
â”‚  â”œâ”€â”€ Activating a row causes electromagnetic interference          â”‚
â”‚  â”œâ”€â”€ Adjacent rows lose charge faster                              â”‚
â”‚  â”œâ”€â”€ Repeated activation â†’ bit flips before refresh                â”‚
â”‚  â””â”€â”€ Refresh interval: ~64ms                                       â”‚
â”‚                                                                     â”‚
â”‚  Row Layout:                                                        â”‚
â”‚  â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”   â”‚
â”‚  â”‚  Row N-1  â”‚  Row N (aggressor)  â”‚  Row N+1  â”‚  Row N+2      â”‚   â”‚
â”‚  â”‚  (victim) â”‚  â† HAMMER THIS â†’   â”‚  (victim) â”‚               â”‚   â”‚
â”‚  â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜   â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
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
4. JNE (0x75) â†’ JMP (0x74) with single bit flip

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
â”œâ”€â”€ Track most-accessed rows
â”œâ”€â”€ Refresh their neighbors
â”œâ”€â”€ Implemented in DRAM controller
â””â”€â”€ BYPASSED by TRRespass, Half-Double

ECC Memory:
â”œâ”€â”€ Detect single-bit errors
â”œâ”€â”€ Correct single-bit errors
â”œâ”€â”€ Cannot handle multi-bit flips
â””â”€â”€ ECCploit: Timing leak reveals ECC bits

Increased Refresh Rate:
â”œâ”€â”€ Refresh more often
â”œâ”€â”€ Reduces bit flip window
â”œâ”€â”€ Performance and power cost
â””â”€â”€ Not complete mitigation

PARA (Probabilistic Adjacent Row Activation):
â”œâ”€â”€ Randomly refresh neighbors
â”œâ”€â”€ Probabilistic defense
â””â”€â”€ Increases difficulty
```

### 2.2 Software Mitigations

```
Memory Isolation:
â”œâ”€â”€ Don't share physical memory with untrusted
â”œâ”€â”€ Guard rows between security domains
â”œâ”€â”€ Reserve rows as buffers

Flush Prevention:
â”œâ”€â”€ Restrict clflush instruction
â”œâ”€â”€ Makes single-sided harder
â””â”€â”€ Doesn't prevent all variants

Address Obfuscation:
â”œâ”€â”€ Randomize physical addresses
â”œâ”€â”€ Makes targeting specific rows harder
â””â”€â”€ Not complete solution
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Voltage Glitching Attack                          â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Normal Operation:                                                  â”‚
â”‚  Vdd â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                    â”‚
â”‚                                                                     â”‚
â”‚  Glitch:                                                            â”‚
â”‚  Vdd â”€â”€â”€â”€â”€â”€â”      â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€                       â”‚
â”‚            â”‚      â”‚                                                 â”‚
â”‚            â”‚      â”‚  â† Voltage drop causes timing violation        â”‚
â”‚            â””â”€â”€â”€â”€â”€â”€â”˜                                                 â”‚
â”‚                â†‘                                                    â”‚
â”‚            Glitch window (~10-100ns)                               â”‚
â”‚                                                                     â”‚
â”‚  Effect:                                                            â”‚
â”‚  â”œâ”€â”€ Logic gates fail to switch properly                           â”‚
â”‚  â”œâ”€â”€ Register values corrupted                                     â”‚
â”‚  â”œâ”€â”€ Instructions skipped or corrupted                             â”‚
â”‚  â””â”€â”€ Security checks bypassed                                      â”‚
â”‚                                                                     â”‚
â”‚  Equipment:                                                         â”‚
â”‚  â”œâ”€â”€ FPGA-based glitcher (ChipWhisperer)                          â”‚
â”‚  â”œâ”€â”€ Custom power supply with fast switching                       â”‚
â”‚  â””â”€â”€ Precise timing (synchronized to target clock)                 â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Clock Glitching

```
Clock Glitching:

Normal:
CLK â”€â”€â”  â”Œâ”€â”€â”  â”Œâ”€â”€â”  â”Œâ”€â”€â”  â”Œâ”€â”€â”  â”Œâ”€â”€
      â””â”€â”€â”˜  â””â”€â”€â”˜  â””â”€â”€â”˜  â””â”€â”€â”˜  â””â”€â”€â”˜

Glitch (extra edge):
CLK â”€â”€â”  â”Œâ”€â”€â”  â”Œâ”â”Œâ”€â”€â”  â”Œâ”€â”€â”  â”Œâ”€â”€â”  â”Œâ”€â”€
      â””â”€â”€â”˜  â””â”€â”€â”˜â””â”˜  â””â”€â”€â”˜  â””â”€â”€â”˜  â””â”€â”€â”˜
                â†‘
            Extra clock edge

Glitch (shortened period):
CLK â”€â”€â”  â”Œâ”€â”€â”  â”Œâ”  â”Œâ”€â”€â”  â”Œâ”€â”€â”  â”Œâ”€â”€
      â””â”€â”€â”˜  â””â”€â”€â”˜â””â”€â”€â”˜  â””â”€â”€â”˜  â””â”€â”€â”˜
              â†‘
         Short period

Effect:
â”œâ”€â”€ Setup/hold time violations
â”œâ”€â”€ Incorrect data captured in registers
â”œâ”€â”€ Instruction fetch errors
â””â”€â”€ Branch misprediction forcing
```

## 2. Laser Fault Injection

### 2.1 Optical Fault Induction

```
Laser Fault Attack:

Equipment:
â”œâ”€â”€ Pulsed laser (typically 1064nm IR)
â”œâ”€â”€ XY positioning stage
â”œâ”€â”€ Microscope for targeting
â”œâ”€â”€ Synchronization with target clock
â””â”€â”€ Chip decapsulation (for frontside)

Mechanism:
â”œâ”€â”€ Photons generate electron-hole pairs
â”œâ”€â”€ Transient current in transistors
â”œâ”€â”€ Single-bit or multi-bit faults
â”œâ”€â”€ Very precise spatial targeting

Backside Attack:
â”œâ”€â”€ Target through silicon substrate
â”œâ”€â”€ No decapsulation needed (thinner silicon)
â”œâ”€â”€ Requires IR-transparent path
â””â”€â”€ Modern defense: backside shields

Applications:
â”œâ”€â”€ Skip security checks
â”œâ”€â”€ Corrupt cryptographic computations
â”œâ”€â”€ Force specific branch outcomes
â”œâ”€â”€ Read protected memory
```

### 2.2 EM Fault Injection

```
Electromagnetic Fault Injection:

Equipment:
â”œâ”€â”€ High-power EM pulse generator
â”œâ”€â”€ Small coil/antenna near chip
â”œâ”€â”€ Precise timing control
â””â”€â”€ No physical contact needed

Mechanism:
â”œâ”€â”€ Induced currents in chip traces
â”œâ”€â”€ Similar effect to voltage glitch
â”œâ”€â”€ Can target specific chip areas
â””â”€â”€ Works through packaging

Advantages:
â”œâ”€â”€ Non-invasive (no decapsulation)
â”œâ”€â”€ Can work at short distance
â”œâ”€â”€ Harder to detect
â””â”€â”€ Complements other techniques
```

## 3. Fault Attack on Cryptography

### 3.1 Differential Fault Analysis (DFA)

```
DFA on AES:

Attack:
1. Obtain correct ciphertext C
2. Inject fault in round 8 or 9
3. Obtain faulty ciphertext C'
4. Analyze difference: C âŠ• C'

Mathematics:
â”œâ”€â”€ Fault in one byte propagates through MixColumns
â”œâ”€â”€ Known propagation pattern constrains key space
â”œâ”€â”€ Multiple faults â†’ unique key recovery
â””â”€â”€ Requires ~2-8 faulty ciphertexts

Countermeasures:
â”œâ”€â”€ Redundant computation
â”œâ”€â”€ Check ciphertext against re-encryption
â”œâ”€â”€ Infection countermeasures
â””â”€â”€ Error detection codes
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
â”œâ”€â”€ s' = CRT(m_p + fault, m_q)
â”œâ”€â”€ (s')^e â‰¡ m (mod q)  [correct]
â”œâ”€â”€ (s')^e â‰¢ m (mod p)  [faulty]
â””â”€â”€ gcd reveals factor

Countermeasure:
â”œâ”€â”€ Verify signature before releasing
â”œâ”€â”€ sig^e == m? If not, abort
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    DRAM Remanence vs Temperature                     â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Temperature  â”‚  Retention Time  â”‚  Practical Window               â”‚
â”‚  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¼â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€    â”‚
â”‚  +20Â°C        â”‚  ~1-2 seconds    â”‚  Marginal for attack            â”‚
â”‚  0Â°C          â”‚  ~10 seconds     â”‚  Possible with quick reboot     â”‚
â”‚  -20Â°C        â”‚  ~1 minute       â”‚  Comfortable attack window      â”‚
â”‚  -50Â°C        â”‚  ~10 minutes     â”‚  Ample time for imaging         â”‚
â”‚  -196Â°C (LN2) â”‚  Hours+          â”‚  Remove DIMMs, analyze offline  â”‚
â”‚                                                                     â”‚
â”‚  Cooling Methods:                                                   â”‚
â”‚  â”œâ”€â”€ Compressed air (inverted can): -50Â°C briefly                  â”‚
â”‚  â”œâ”€â”€ Freeze spray: -40Â°C sustained                                 â”‚
â”‚  â”œâ”€â”€ Liquid nitrogen: -196Â°C                                       â”‚
â”‚  â””â”€â”€ Thermoelectric cooler: -30Â°C controlled                       â”‚
â”‚                                                                     â”‚
â”‚  Attack Procedure:                                                  â”‚
â”‚  1. Target system running with keys in memory                      â”‚
â”‚  2. Cool DRAM modules                                              â”‚
â”‚  3. Power cycle or cold reset                                      â”‚
â”‚  4. Boot from USB to forensic imager                               â”‚
â”‚  5. Dump physical memory                                           â”‚
â”‚  6. Search for cryptographic keys                                  â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Key Finding Techniques

```
Finding Keys in Memory:

AES Key Schedules:
â”œâ”€â”€ Characteristic expansion pattern
â”œâ”€â”€ Round keys have known relationships
â”œâ”€â”€ AESKeyFinder: Automated search tool
â””â”€â”€ Search for key schedule structure

RSA Private Keys:
â”œâ”€â”€ Look for prime factors p, q
â”œâ”€â”€ ASN.1 DER structure markers
â”œâ”€â”€ Large integers with specific properties
â””â”€â”€ RSAKeyFinder tool

Disk Encryption Keys:
â”œâ”€â”€ BitLocker: FVEK in specific structure
â”œâ”€â”€ LUKS: Master key in memory
â”œâ”€â”€ FileVault: Volume key derivation
â””â”€â”€ VeraCrypt: Key in specific location
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
â”œâ”€â”€ AES-XTS encryption of all DRAM
â”œâ”€â”€ Key generated at boot, stored in CPU
â”œâ”€â”€ Transparent to software
â””â”€â”€ Cold boot sees only ciphertext

AMD SME (Secure Memory Encryption):
â”œâ”€â”€ Similar to Intel TME
â”œâ”€â”€ Per-page encryption keys possible
â””â”€â”€ Integrated with SEV for VMs

Memory Scrubbing:
â”œâ”€â”€ BIOS/firmware option
â”œâ”€â”€ Clears memory on cold boot
â”œâ”€â”€ Does NOT help with power removal attack

Physical Countermeasures:
â”œâ”€â”€ Solder DIMMs (prevent removal)
â”œâ”€â”€ Tamper-responsive enclosure
â”œâ”€â”€ Intrusion detection â†’ key zeroization
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Website Fingerprinting Attack                     â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Scenario:                                                          â”‚
â”‚  â”œâ”€â”€ User visits website over HTTPS or Tor                         â”‚
â”‚  â”œâ”€â”€ Attacker observes encrypted traffic (ISP, network admin)      â”‚
â”‚  â”œâ”€â”€ Content is encrypted but metadata visible                     â”‚
â”‚  â””â”€â”€ Goal: Identify which website user is visiting                 â”‚
â”‚                                                                     â”‚
â”‚  Observable Features:                                               â”‚
â”‚  â”œâ”€â”€ Packet sizes                                                  â”‚
â”‚  â”œâ”€â”€ Packet timing                                                 â”‚
â”‚  â”œâ”€â”€ Packet direction (up/down)                                    â”‚
â”‚  â”œâ”€â”€ Total transfer size                                           â”‚
â”‚  â”œâ”€â”€ Burst patterns                                                â”‚
â”‚  â””â”€â”€ TCP/TLS handshake characteristics                             â”‚
â”‚                                                                     â”‚
â”‚  Machine Learning Approach:                                         â”‚
â”‚  1. Collect traffic traces for known websites                      â”‚
â”‚  2. Extract features from traces                                   â”‚
â”‚  3. Train classifier (CNN, RF, k-NN)                               â”‚
â”‚  4. Classify victim's traffic                                      â”‚
â”‚                                                                     â”‚
â”‚  Accuracy (closed-world):                                           â”‚
â”‚  â”œâ”€â”€ HTTPS: 90%+ accuracy                                          â”‚
â”‚  â”œâ”€â”€ Tor: 80-90%+ accuracy (improved attacks)                      â”‚
â”‚  â”œâ”€â”€ VPN: 85%+ accuracy                                            â”‚
â”‚  â””â”€â”€ Open-world (many sites): Lower but still significant          â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Tor Traffic Analysis

```
Tor Circuit:
User â†’ Guard â†’ Middle â†’ Exit â†’ Website

Attack Positions:
â”œâ”€â”€ Guard node: Sees user IP, can fingerprint
â”œâ”€â”€ Exit node: Sees destination, unencrypted data
â”œâ”€â”€ Both: Timing correlation â†’ deanonymize
â””â”€â”€ ISP: Fingerprint Tor traffic patterns

Defenses:
â”œâ”€â”€ Traffic padding: Add dummy packets
â”œâ”€â”€ Traffic morphing: Make all sites look similar
â”œâ”€â”€ Random delays: Disrupt timing patterns
â””â”€â”€ Pluggable transports: Disguise Tor protocol
```

## 2. Keystroke and Input Timing

### 2.1 SSH Keystroke Analysis

```
SSH Timing Attack:

Observation:
â”œâ”€â”€ Each keystroke sends separate packet
â”œâ”€â”€ Encrypted but size/timing visible
â”œâ”€â”€ Inter-keystroke timing reveals:
â”‚   â”œâ”€â”€ Typing rhythm (user identification)
â”‚   â”œâ”€â”€ Word patterns (dictionary attack)
â”‚   â””â”€â”€ Password structure

Attack:
1. Observe timing between SSH packets
2. Model keystroke timing distributions
3. Match against known words/passwords
4. Probabilistic password recovery

Song et al. Results:
â”œâ”€â”€ Reduce password search space by 50%
â”œâ”€â”€ User identification possible
â””â”€â”€ Works over Internet
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Cloud Side-Channel Attack Surface                 â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  Shared Resources (Cross-VM Attack Surface):                        â”‚
â”‚  â”œâ”€â”€ CPU cache (L3/LLC often shared)                               â”‚
â”‚  â”œâ”€â”€ Memory bus                                                    â”‚
â”‚  â”œâ”€â”€ TLB (Translation Lookaside Buffer)                            â”‚
â”‚  â”œâ”€â”€ Branch predictor state                                        â”‚
â”‚  â”œâ”€â”€ DRAM row buffer                                               â”‚
â”‚  â””â”€â”€ Network infrastructure                                        â”‚
â”‚                                                                     â”‚
â”‚  Demonstrated Attacks:                                              â”‚
â”‚  â”œâ”€â”€ Hey You, Get Off My Cloud (2009): Co-location detection       â”‚
â”‚  â”œâ”€â”€ Prime+Probe across VMs: Cache timing attack                   â”‚
â”‚  â”œâ”€â”€ Flush+Reload on KSM: Dedup enables shared memory             â”‚
â”‚  â”œâ”€â”€ Rowhammer VM escape: Memory corruption across VMs            â”‚
â”‚  â””â”€â”€ Spectre/Meltdown: Speculative execution across boundaries    â”‚
â”‚                                                                     â”‚
â”‚  Cloud Provider Mitigations:                                        â”‚
â”‚  â”œâ”€â”€ Dedicated hosts (no sharing)                                  â”‚
â”‚  â”œâ”€â”€ Core/cache isolation                                          â”‚
â”‚  â”œâ”€â”€ KSM disabled                                                  â”‚
â”‚  â”œâ”€â”€ Microcode patches (Spectre/Meltdown)                         â”‚
â”‚  â””â”€â”€ Hardware refresh cycles                                       â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Container Isolation Issues

```
Container Side Channels:

Shared Kernel:
â”œâ”€â”€ Containers share host kernel
â”œâ”€â”€ Less isolation than VMs
â”œâ”€â”€ procfs/sysfs information leakage
â””â”€â”€ Kernel vulnerabilities affect all containers

Cgroup Side Channels:
â”œâ”€â”€ CPU usage visible via cgroups
â”œâ”€â”€ Memory pressure observable
â”œâ”€â”€ I/O patterns inferrable
â””â”€â”€ Network namespace doesn't hide timing

Attack Examples:
â”œâ”€â”€ Detect crypto operations via CPU contention
â”œâ”€â”€ Infer database queries from memory/CPU
â”œâ”€â”€ Identify applications from resource patterns
â””â”€â”€ Deanonymize Tor exits via timing
```

## 2. Covert Channels in Cloud

### 2.1 Resource-Based Covert Channels

```
Cache Covert Channel:
â”œâ”€â”€ Sender: Access/don't access specific cache sets
â”œâ”€â”€ Receiver: Prime+Probe to detect access
â”œâ”€â”€ Bandwidth: ~100 Kbps demonstrated
â””â”€â”€ Cross-VM communication proven

Memory Bus Covert Channel:
â”œâ”€â”€ Sender: Cause memory bus contention
â”œâ”€â”€ Receiver: Measure memory access timing
â”œâ”€â”€ Lower bandwidth but harder to detect
â””â”€â”€ Works across VMs

Network Covert Channel:
â”œâ”€â”€ Timing modulation of legitimate traffic
â”œâ”€â”€ Storage in unused packet fields
â”œâ”€â”€ DNS tunneling
â””â”€â”€ ICMP payload encoding
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
â”œâ”€â”€ Based on LLVM
â”œâ”€â”€ Checks for secret-dependent branches/memory
â”œâ”€â”€ Used by libsodium, OpenSSL
â””â”€â”€ Some false positives

dudect:
â”œâ”€â”€ Statistical testing approach
â”œâ”€â”€ Run with random inputs
â”œâ”€â”€ Detect timing variations
â””â”€â”€ Black-box testing

timecop:
â”œâ”€â”€ Valgrind-based checker
â”œâ”€â”€ Taint tracking for secrets
â”œâ”€â”€ Detects secret-dependent operations
â””â”€â”€ Runtime checking
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
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                TERAS Side-Channel Defense Framework                  â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  LAYER 1: Constant-Time Implementation                              â”‚
â”‚  â”œâ”€â”€ All crypto operations constant-time                           â”‚
â”‚  â”œâ”€â”€ No secret-dependent branches                                  â”‚
â”‚  â”œâ”€â”€ No secret-dependent memory access                             â”‚
â”‚  â”œâ”€â”€ Verified with ct-verif                                        â”‚
â”‚  â””â”€â”€ Tested with dudect                                            â”‚
â”‚                                                                     â”‚
â”‚  LAYER 2: Hardware Feature Utilization                              â”‚
â”‚  â”œâ”€â”€ AES-NI for AES (no table lookups)                            â”‚
â”‚  â”œâ”€â”€ CLMUL for GCM multiplication                                  â”‚
â”‚  â”œâ”€â”€ SHA-NI for hashing                                            â”‚
â”‚  â”œâ”€â”€ RDRAND/RDSEED for randomness                                  â”‚
â”‚  â””â”€â”€ CET for control flow protection                               â”‚
â”‚                                                                     â”‚
â”‚  LAYER 3: Speculative Execution Mitigations                         â”‚
â”‚  â”œâ”€â”€ Enable IBRS/eIBRS                                             â”‚
â”‚  â”œâ”€â”€ Enable SSBD                                                   â”‚
â”‚  â”œâ”€â”€ Retpoline compilation                                         â”‚
â”‚  â”œâ”€â”€ Speculative Load Hardening                                    â”‚
â”‚  â””â”€â”€ KPTI enabled                                                  â”‚
â”‚                                                                     â”‚
â”‚  LAYER 4: Isolation                                                 â”‚
â”‚  â”œâ”€â”€ Process isolation for crypto                                  â”‚
â”‚  â”œâ”€â”€ Memory protection (separate pages)                            â”‚
â”‚  â”œâ”€â”€ Cache partitioning where available                            â”‚
â”‚  â””â”€â”€ Core pinning for sensitive operations                         â”‚
â”‚                                                                     â”‚
â”‚  LAYER 5: Operational Security                                      â”‚
â”‚  â”œâ”€â”€ HSM for key operations (highest security)                     â”‚
â”‚  â”œâ”€â”€ Memory encryption (TME/SME)                                   â”‚
â”‚  â”œâ”€â”€ Physical security requirements                                â”‚
â”‚  â””â”€â”€ Cloud deployment guidelines                                   â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Product-Specific Requirements

```
MENARA (Mobile):
â”œâ”€â”€ Side-channels: Cache timing, power analysis
â”œâ”€â”€ Mitigations:
â”‚   â”œâ”€â”€ Constant-time crypto (ARM optimized)
â”‚   â”œâ”€â”€ TrustZone isolation
â”‚   â”œâ”€â”€ Hardware keystore (StrongBox)
â”‚   â””â”€â”€ Minimal crypto in app code
â””â”€â”€ Testing: Mobile fuzzing, timing tests

GAPURA (WAF):
â”œâ”€â”€ Side-channels: Network timing, cache timing
â”œâ”€â”€ Mitigations:
â”‚   â”œâ”€â”€ Constant-time comparison for auth
â”‚   â”œâ”€â”€ Rate limiting (blurs timing)
â”‚   â”œâ”€â”€ Worker isolation
â”‚   â””â”€â”€ AES-NI for TLS
â””â”€â”€ Testing: Remote timing analysis

ZIRAH (EDR):
â”œâ”€â”€ Side-channels: Process monitoring timing
â”œâ”€â”€ Mitigations:
â”‚   â”œâ”€â”€ Async processing (decouple timing)
â”‚   â”œâ”€â”€ Kernel-level isolation
â”‚   â”œâ”€â”€ Random scheduling noise
â”‚   â””â”€â”€ Encrypted memory for forensics
â””â”€â”€ Testing: Timing analysis of scanning

BENTENG (eKYC):
â”œâ”€â”€ Side-channels: Biometric processing timing, power
â”œâ”€â”€ Mitigations:
â”‚   â”œâ”€â”€ TEE for biometrics
â”‚   â”œâ”€â”€ Constant-time face comparison
â”‚   â”œâ”€â”€ HSM for identity keys
â”‚   â””â”€â”€ Isolated processing
â””â”€â”€ Testing: Timing attacks on verification

SANDI (Signatures):
â”œâ”€â”€ Side-channels: Signing timing, power analysis
â”œâ”€â”€ Mitigations:
â”‚   â”œâ”€â”€ HSM for all signing (mandatory)
â”‚   â”œâ”€â”€ Blinding for RSA
â”‚   â”œâ”€â”€ Constant-time ECDSA
â”‚   â””â”€â”€ Protected timestamp operations
â””â”€â”€ Testing: Full side-channel evaluation
```

## 2. Testing and Validation

### 2.1 Side-Channel Test Suite

```
TERAS Side-Channel Test Suite:

TIMING TESTS:
â”œâ”€â”€ ct-verif: Static verification
â”œâ”€â”€ dudect: Statistical timing test
â”œâ”€â”€ Cachegrind: Cache access analysis
â””â”€â”€ Custom timing harness

CACHE TESTS:
â”œâ”€â”€ Mastik: Cache attack toolkit
â”œâ”€â”€ Prime+Probe simulation
â”œâ”€â”€ Flush+Reload detection
â””â”€â”€ Cross-process cache probing

SPECULATIVE TESTS:
â”œâ”€â”€ Spectre gadget detection (static)
â”œâ”€â”€ Spectre PoC execution
â”œâ”€â”€ MDS vulnerability check
â””â”€â”€ Hardware feature verification

POWER/EM TESTS (Hardware labs):
â”œâ”€â”€ ChipWhisperer integration
â”œâ”€â”€ DPA analysis scripts
â”œâ”€â”€ SPA visual inspection
â””â”€â”€ EM probe positioning

CI INTEGRATION:
â”œâ”€â”€ All timing tests in CI
â”œâ”€â”€ Cache tests in nightly
â”œâ”€â”€ Spectre scans on PR
â””â”€â”€ Annual hardware lab evaluation
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

*Research Track Output â€” Domain G: Side-Channel Attacks*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*

---

**SHA-256**: To be computed
