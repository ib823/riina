# TERAS-LANG Research Domain X: Formal Concurrency Model

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-X-CONCURRENCY-MODEL |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Domain | X: Formal Concurrency Model |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |
| Status | FOUNDATIONAL DEFINITION |

---

# X-01: The "Concurrent Bug" Problem & The TERAS Solution

## 1. The Existential Threat

**Context:**
Concurrent programming introduces bug classes that sequential programs cannot have:
- **Data races:** Two threads access same memory, at least one writes, no synchronization
- **Deadlocks:** Circular wait on locks
- **Livelocks:** Threads make no progress despite running
- **TOCTOU:** Time-of-check to time-of-use race conditions
- **Priority inversion:** Low-priority task blocks high-priority task

**The Reality:**
Concurrency bugs are notoriously difficult to find, reproduce, and fix. They are often non-deterministic and may only manifest under specific timing conditions.

**The TERAS Reality:**
Our current semantics (`step` relation in `Semantics.v`) are **purely sequential**. The moment TERAS programs run on multi-core hardware, the formal guarantees become VOID for concurrent code.

**The Goal:**
Extend the formal semantics to cover concurrency. Prove that well-typed concurrent programs are **data-race free** and **deadlock free**.

## 2. The Solution: Session Types & Ownership for Concurrency

We combine three proven approaches:
1. **Ownership types** (Rust-style) for shared state
2. **Session types** for message-passing protocols
3. **Linear types** for channel endpoints

### 2.1 Core Principle: No Shared Mutable State

The fundamental law:
```
SHARED XOR MUTABLE
```

Data can be:
- **Shared** (multiple readers, no writers) — `&T`
- **Exclusive** (one owner, can mutate) — `&mut T`
- **Never both simultaneously**

This is enforced by the type system, making data races **impossible by construction**.

### 2.2 Session Types for Protocols

Communication channels have types that specify the protocol:

```
// Protocol type
type FileTransfer =
  !Filename.           // Send filename
  ?FileSize.           // Receive size
  !Confirmation.       // Send confirmation
  ?FileData.           // Receive data
  End                  // Protocol complete

// Type-safe implementation
fn client(ch: Chan<FileTransfer>) {
  ch.send(filename);          // Must send Filename first
  let size = ch.recv();       // Must receive FileSize second
  ch.send(Confirm);           // Must send Confirmation third
  let data = ch.recv();       // Must receive FileData fourth
  ch.close();                 // Must close at End
}
```

Protocol violations are **compile-time type errors**.

### 2.3 Linear Channel Endpoints

Channel endpoints are **linear** (must be used exactly once):

```
// Creating a channel returns two linear endpoints
let (client_end, server_end) = channel::<Protocol>();

// Each endpoint must be used exactly once
spawn(|| server(server_end));  // server_end consumed
client(client_end);             // client_end consumed

// ERROR: Cannot use endpoint twice
// client(client_end);  // Compile error: already moved
```

This prevents:
- Sending on closed channel
- Receiving from closed channel
- Protocol desynchronization

## 3. The Mathematical Standard

### 3.1 Data Race Freedom

$$
\forall t_1, t_2, l. \text{accesses}(t_1, l) \land \text{accesses}(t_2, l) \land t_1 \neq t_2 \implies \text{read\_only}(t_1, l) \lor \text{read\_only}(t_2, l)
$$

### 3.2 Deadlock Freedom

For lock-based code, we use a **lock ordering** discipline:

$$
\forall t. \text{acquires}(t, l_1) \text{ before } \text{acquires}(t, l_2) \implies \text{order}(l_1) < \text{order}(l_2)
$$

For session types, we prove **progress**:

$$
\forall P. \text{well\_typed}(P) \implies P \rightarrow^* \text{terminated} \lor P \rightarrow
$$

### 3.3 Session Fidelity

$$
\forall ch: S. \text{trace}(ch) \in \text{language}(S)
$$

The actual communication trace conforms to the session type.

## 4. Architecture of Domain X

### 4.1 Extended Syntax

```coq
(* Concurrent expressions *)
Inductive cexpr : Type :=
  | CSpawn : cexpr -> cexpr             (* spawn e *)
  | CNewChan : session_ty -> cexpr      (* channel<S>() *)
  | CSend : cexpr -> cexpr -> cexpr     (* ch.send(v) *)
  | CRecv : cexpr -> cexpr              (* ch.recv() *)
  | CClose : cexpr -> cexpr             (* ch.close() *)
  | CSelect : cexpr -> label -> cexpr   (* ch.select(L) *)
  | COffer : cexpr -> branches -> cexpr (* ch.offer { ... } *)
  | CSeq : expr -> cexpr.               (* lift sequential expr *)
```

### 4.2 Session Types

```coq
Inductive session_ty : Type :=
  | SSend : ty -> session_ty -> session_ty    (* !T.S *)
  | SRecv : ty -> session_ty -> session_ty    (* ?T.S *)
  | SSelect : list (label * session_ty) -> session_ty  (* +{L1:S1, L2:S2} *)
  | SOffer : list (label * session_ty) -> session_ty   (* &{L1:S1, L2:S2} *)
  | SEnd : session_ty                         (* end *)
  | SDual : session_ty -> session_ty.         (* dual(S) *)
```

### 4.3 Concurrent Semantics

```coq
(* Thread pool configuration *)
Definition config := list (thread_id * cexpr * store).

(* Concurrent step relation *)
Inductive cstep : config -> config -> Prop :=
  | CS_Thread : forall tid e e' st st' rest,
      step (e, st) (e', st') ->
      cstep ((tid, e, st) :: rest) ((tid, e', st') :: rest)
  | CS_Spawn : forall tid e st rest new_tid,
      cstep ((tid, CSpawn e, st) :: rest)
            ((tid, CUnit, st) :: (new_tid, e, st) :: rest)
  | CS_Comm : (* synchronous communication *)
      ...
```

### 4.4 Typing Rules for Concurrency

```coq
(* Channel typing *)
| T_NewChan : forall G S D S,
    has_ctype G S D (CNewChan S) (TChan S S) EffectPure

(* Send typing *)
| T_Send : forall G S D ch v T S',
    has_ctype G S D ch (TChan (SSend T S') _) e1 ->
    has_type G S D v T e2 ->
    has_ctype G S D (CSend ch v) (TChan S' _) (effect_join e1 e2)

(* Linear usage *)
| T_Linear : forall G S D ch S,
    linear_used ch G ->
    has_ctype G S D ch (TChan S S) EffectPure
```

## 5. Implementation Strategy (Infinite Timeline)

1. **Step 1: Define Session Type System**
   - Formalize session types in Coq
   - Prove session type duality
   - Define typing rules for send/recv/select/offer

2. **Step 2: Prove Data Race Freedom**
   - Theorem: Well-typed programs have no data races
   - Use ownership + linearity as the key invariants

3. **Step 3: Prove Deadlock Freedom**
   - For session types: prove progress
   - For locks: prove lock ordering preservation

4. **Step 4: Implement in Prototype**
   - Add concurrent primitives to parser
   - Implement session type checker
   - Add runtime support for channels

5. **Step 5: Integration**
   - Concurrent TERAS code verified against concurrent semantics
   - Track U (Guardian) monitors thread behavior

## 6. Obsolescence of Threats

- **Data Races:** OBSOLETE. Ownership types make them impossible.
- **Deadlocks:** OBSOLETE. Session types guarantee progress; lock ordering prevents circular waits.
- **TOCTOU:** OBSOLETE. Atomic operations and session protocols prevent race conditions.
- **Channel Protocol Violations:** OBSOLETE. Session types enforce protocol compliance.
- **Use-After-Close:** OBSOLETE. Linear types ensure single use.
- **Priority Inversion:** MITIGATED. Lock-free message passing reduces blocking.

## 7. Dependencies

| Dependency | Direction | Nature |
|------------|-----------|--------|
| Track A (Formal) | X extends A | Concurrent semantics |
| Track W (Memory) | X depends on W | Thread-local heaps |
| Track V (Termination) | X coordinates with V | Progress guarantees |
| Track U (Guardian) | X integrates with U | Thread monitoring |

## 8. Advanced Features

### 8.1 Multiparty Session Types

For protocols involving more than two parties:

```
global protocol Auction {
  Bidder -> Auctioneer: Bid(amount);
  Auctioneer -> All: CurrentBid(amount);
  choice at Auctioneer {
    Auctioneer -> Winner: Won;
    Auctioneer -> Others: Lost;
  }
}
```

### 8.2 Affine Types for Optional Use

Allow channels to be dropped without completing protocol (with explicit marking):

```
type CancellableTransfer =
  !Request. (?Response + Cancelled)

// Can drop channel after sending if cancelled
```

---

**"Concurrency is not chaos. Concurrency is a protocol, and protocols are TYPES."**
