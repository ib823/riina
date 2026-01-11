# TERAS-LANG Architecture Decision C-04: Declassification

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-C04-DECISION |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | C-04 |
| Domain | C: Information Flow Control |
| Status | **APPROVED** |

---

## 1. Decision

### Decision Statement

**TERAS-LANG SHALL IMPLEMENT:**

1. **Explicit declassification** with `declassify!` macro
2. **Policy-based authorization** for downgrading
3. **Robust declassification** requiring high integrity
4. **Endorsement** with `endorse!` macro
5. **Mandatory audit logging** for all downgrades
6. **Four-dimension policy specification** (what, who, when, where)

### Architecture Decision ID: `TERAS-ARCH-C04-DCL-001`

### Status: **APPROVED**

---

## 2. Syntax

```rust
// Declassification
declassify!(value, from: Secret, to: Public, policy: P)

// Endorsement  
endorse!(value, from: Untrusted, to: Trusted, validation: V)
```

---

## 3. Robustness Requirement

All declassification requires high integrity context to prevent attacker-influenced releases.

---

*Architecture Decision Record for TERAS-LANG declassification.*

---
---
---

# TERAS-LANG Research Survey C-05: Dynamic Information Flow Control

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-C05-SURVEY |
| Version | 1.0.0 |
| Date | 2026-01-03 |
| Session | C-05 |
| Domain | C: Information Flow Control |
| Status | Complete |

---

## Executive Summary

Dynamic IFC enforces information flow policies at runtime, complementing static analysis. This survey covers floating-label systems, the LIO monad, hybrid static-dynamic approaches, and their application to TERAS.

---

## Part 1: Static vs Dynamic IFC

### 1.1 Comparison

```
Static IFC:
├── Enforced at compile time
├── No runtime overhead
├── Conservative (rejects some safe programs)
├── Full coverage guarantee
└── Cannot handle runtime-determined labels

Dynamic IFC:
├── Enforced at runtime
├── Runtime overhead
├── Precise (accepts safe executions)
├── May miss paths
└── Handles dynamic labels naturally
```

### 1.2 When Dynamic is Needed

```
Dynamic labels required for:

1. User-dependent policies
   label = user.clearance  // Known at runtime

2. Data-dependent labels
   label = database.row.classification

3. Policy changes
   label = current_policy.level  // May change

4. Interoperability
   label = external_system.classification
```

---

## Part 2: Floating Label Systems

### 2.1 Current Label

```
Floating label: Process's current security context

Operations:
    get_label() -> Label      -- Read current label
    set_label(L)              -- Raise current label
    
Constraint:
    Can only RAISE label, never lower
    (Prevents laundering attacks)
```

### 2.2 Taint Mode

```
Taint propagation:

current_label = Public

x = read_secret()       // current_label → Secret
y = x + 1               // Computation taints result
output(y)               // Check: current_label ⊑ output_label
                        // Fails: Secret ⋢ Public
```

### 2.3 Reference Monitoring

```
Reference monitor checks:

Read:  check(current_label ⊒ ref_label)
Write: check(current_label ⊑ ref_label)
       raise(ref_label)  // Current label becomes at least ref_label

Every memory access checked at runtime.
```

---

## Part 3: LIO (Labeled IO)

### 3.1 LIO Monad

```haskell
-- LIO: Labeled IO Monad (Haskell)

-- The LIO monad
newtype LIO l a = LIO { unLIO :: IORef l -> IO a }

-- Labeled values
data Labeled l a = Labeled l a

-- Core operations
label :: l -> a -> LIO l (Labeled l a)
unlabel :: Labeled l a -> LIO l a  -- Raises current label!

-- Current label operations
getLabel :: LIO l l
setLabel :: l -> LIO l ()  -- Can only raise
```

### 3.2 LIO Example

```haskell
example :: LIO SecurityLevel Int
example = do
    -- Start at Low
    secretData <- unlabel secretLabeled  
    -- Now at High (cannot go back!)
    
    -- This would fail:
    -- setLabel Low  -- Cannot lower!
    
    return (secretData + 1)
```

### 3.3 LIO Clearance

```haskell
-- Clearance: Upper bound on current label

data LIOState = LIOState {
    currentLabel :: Label,
    clearance :: Label  -- Cannot exceed this
}

-- setLabel must satisfy: new_label ⊑ clearance
-- Prevents unbounded label raising
```

---

## Part 4: Hybrid Static-Dynamic

### 4.1 Best of Both Worlds

```
Hybrid approach:

1. Static analysis for structure
   - Function boundaries
   - Known flows
   
2. Dynamic checks for flexibility
   - Runtime-determined labels
   - Policy changes

Benefits:
    - Reduced runtime overhead (static where possible)
    - Flexibility for dynamic cases
    - Sound overall guarantee
```

### 4.2 Gradual IFC

```
Gradual typing for IFC:

Static labels: L, H
Dynamic label: ?

x : int^?     -- Unknown label
y : int^H     -- Known high

z = x + y     -- z : int^(? ⊔ H) = int^?
              -- Runtime check on use of z
```

### 4.3 Selective Dynamic Checks

```rust
// Static for known labels
fn static_flow(x: int @ Secret) -> int @ Secret {
    x + 1  // No runtime check
}

// Dynamic for unknown labels
fn dynamic_flow(x: int @ ?L, target: Label) -> int @ target {
    runtime_check!(L ⊑ target);  // Runtime check
    x
}
```

---

## Part 5: Implementation Strategies

### 5.1 Label Propagation

```
Every value carries label:

struct TaggedValue<T> {
    value: T,
    label: Label,
}

Operations propagate:
    add(a: Tagged<int>, b: Tagged<int>) -> Tagged<int> {
        Tagged {
            value: a.value + b.value,
            label: a.label.join(b.label),
        }
    }
```

### 5.2 Inline Reference Monitor

```rust
// IRM: Check every security-relevant operation

fn read_ref<T>(r: &Ref<T>) -> T {
    let current = get_current_label();
    assert!(r.label.can_flow_to(&current));
    r.value.clone()
}

fn write_ref<T>(r: &mut Ref<T>, v: T) {
    let current = get_current_label();
    assert!(current.can_flow_to(&r.label));
    set_current_label(current.join(&r.label));
    r.value = v;
}
```

### 5.3 Performance Optimization

```
Reducing dynamic overhead:

1. Label caching
   - Cache label comparisons
   - Reuse for repeated checks

2. Coalescing checks
   - Batch multiple checks
   - Amortize overhead

3. Speculative execution
   - Predict likely labels
   - Fast path for common case

4. Hardware support
   - Tag bits in memory
   - Hardware label propagation
```

---

## Part 6: TERAS Dynamic IFC

### 6.1 Runtime Label Type

```rust
/// Runtime security label
#[derive(Clone, Debug)]
pub struct DynamicLabel {
    level: SecurityLevel,
    compartments: HashSet<Compartment>,
    integrity: IntegrityLevel,
}

impl DynamicLabel {
    pub fn can_flow_to(&self, target: &DynamicLabel) -> bool {
        self.level <= target.level &&
        self.compartments.is_subset(&target.compartments) &&
        self.integrity >= target.integrity
    }
    
    pub fn join(&self, other: &DynamicLabel) -> DynamicLabel {
        DynamicLabel {
            level: max(self.level, other.level),
            compartments: self.compartments.union(&other.compartments).cloned().collect(),
            integrity: min(self.integrity, other.integrity),
        }
    }
}
```

### 6.2 Labeled Values

```rust
/// Value with runtime label
pub struct Labeled<T> {
    value: T,
    label: DynamicLabel,
}

impl<T> Labeled<T> {
    pub fn new(value: T, label: DynamicLabel) -> Self {
        Labeled { value, label }
    }
    
    pub fn unlabel(self, ctx: &mut SecurityContext) -> T {
        ctx.raise_label(&self.label);
        self.value
    }
    
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Labeled<U> {
        Labeled {
            value: f(self.value),
            label: self.label,
        }
    }
}
```

### 6.3 Security Context

```rust
/// Runtime security context (like LIO)
pub struct SecurityContext {
    current_label: DynamicLabel,
    clearance: DynamicLabel,
}

impl SecurityContext {
    pub fn raise_label(&mut self, to: &DynamicLabel) {
        let new_label = self.current_label.join(to);
        assert!(new_label.can_flow_to(&self.clearance),
                "Label would exceed clearance");
        self.current_label = new_label;
    }
    
    pub fn check_write(&self, target: &DynamicLabel) -> Result<(), IFCError> {
        if self.current_label.can_flow_to(target) {
            Ok(())
        } else {
            Err(IFCError::FlowViolation {
                from: self.current_label.clone(),
                to: target.clone(),
            })
        }
    }
}
```

---

## Part 7: Bibliography

1. Stefan, D., et al. (2011). "Flexible Dynamic Information Flow Control in Haskell"
2. Buiras, P., et al. (2015). "HLIO: Mixing Static and Dynamic Typing for IFC"
3. Austin, T., Flanagan, C. (2010). "Permissive Dynamic Information Flow Analysis"
4. Hedin, D., Sabelfeld, A. (2012). "Information-Flow Security for JavaScript"

---

*Research Track Output — Domain C: Information Flow Control*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*
