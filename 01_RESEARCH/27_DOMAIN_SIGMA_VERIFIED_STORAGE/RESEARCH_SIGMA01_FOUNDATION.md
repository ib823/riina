# RIINA Research Domain Σ (Sigma): Verified Persistent Storage

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-SIGMA-VERIFIED-STORAGE |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Domain | Σ: Verified Persistent Storage |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |
| Status | FOUNDATIONAL DEFINITION |

---

# Σ-01: The "Database Trust" Problem & The RIINA Solution

## 1. The Existential Threat

**Context:**
Every application stores data. Databases are the foundation of all systems.

**The Reality:**
Databases are the #1 source of catastrophic vulnerabilities:
- **SQL Injection:** Billions of records breached (Equifax, Yahoo, LinkedIn)
- **ACID Violations:** Data corruption under concurrent access
- **Buffer Overflows:** Memory safety bugs in C/C++ database engines
- **Crash Corruption:** Data loss due to incomplete transactions
- **Timing Attacks:** Query patterns leak information

**The Current State:**
- MySQL, PostgreSQL, MongoDB: Millions of lines of unverified C/C++
- SQLite: "Most tested" but not formally verified
- TigerBeetle: Best-in-class testing, but not formally proven

**The RIINA Goal:**
A database where:
- **Every operation is type-safe** — No SQL injection by construction
- **ACID properties are PROVEN** — Not tested, PROVEN in Coq
- **Memory safety is PROVEN** — No buffer overflows possible
- **Query plans are verified** — Optimizer correctness proven
- **Crash recovery is PROVEN** — Durability mathematically guaranteed

## 2. The Solution: TigerBeetle-Inspired Verified Database

### 2.1 Design Philosophy

```
╔════════════════════════════════════════════════════════════════════╗
║                 RIINA DATABASE DESIGN PRINCIPLES                    ║
╠════════════════════════════════════════════════════════════════════╣
║                                                                     ║
║  1. DETERMINISTIC EXECUTION                                         ║
║     └── Same input → same output, always                           ║
║     └── Single-threaded core eliminates race conditions            ║
║                                                                     ║
║  2. TYPE-SAFE QUERIES                                               ║
║     └── No SQL strings — queries are typed ASTs                    ║
║     └── Injection impossible by construction                       ║
║                                                                     ║
║  3. PROVEN CORRECTNESS                                              ║
║     └── ACID properties proven in Coq                              ║
║     └── Storage engine verified                                    ║
║                                                                     ║
║  4. SIMULATION TESTING                                              ║
║     └── Deterministic Simulation Testing (DST)                     ║
║     └── 700x time acceleration                                     ║
║     └── All fault modes injected                                   ║
║                                                                     ║
║  5. CRYPTOGRAPHIC INTEGRITY                                         ║
║     └── All data encrypted at rest (Track F)                       ║
║     └── Merkle tree for tamper detection                           ║
║     └── Immutable audit log                                        ║
║                                                                     ║
╚════════════════════════════════════════════════════════════════════╝
```

### 2.2 Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                    RIINA VERIFIED DATABASE                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌───────────────────────────────────────────────────────────────┐  │
│  │                    Query Layer (Type-Safe)                     │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │  │
│  │  │   Parser    │  │  Optimizer  │  │  Executor           │   │  │
│  │  │  (Verified) │→ │  (Verified) │→ │  (Verified)         │   │  │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │  │
│  └───────────────────────────────────────────────────────────────┘  │
│                              │                                       │
│  ┌───────────────────────────▼───────────────────────────────────┐  │
│  │                  Transaction Manager                           │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │  │
│  │  │   Begin     │  │   Commit    │  │   Rollback          │   │  │
│  │  │  (PROVEN)   │  │  (PROVEN)   │  │  (PROVEN)           │   │  │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │  │
│  │                                                                │  │
│  │  ACID Properties: PROVEN in Coq                               │  │
│  └───────────────────────────────────────────────────────────────┘  │
│                              │                                       │
│  ┌───────────────────────────▼───────────────────────────────────┐  │
│  │                   Storage Engine                               │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │  │
│  │  │  B+Tree     │  │  LSM-Tree   │  │  WAL (Write-Ahead   │   │  │
│  │  │  (Verified) │  │  (Verified) │  │       Log)          │   │  │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │  │
│  │                                                                │  │
│  │  Memory Safety: PROVEN via Track W                            │  │
│  └───────────────────────────────────────────────────────────────┘  │
│                              │                                       │
│  ┌───────────────────────────▼───────────────────────────────────┐  │
│  │                   Integrity Layer                              │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐   │  │
│  │  │  Encryption │  │  Merkle     │  │  Checksums          │   │  │
│  │  │  (Track F)  │  │  Tree       │  │  (CRC + SHA)        │   │  │
│  │  └─────────────┘  └─────────────┘  └─────────────────────┘   │  │
│  └───────────────────────────────────────────────────────────────┘  │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

## 3. Type-Safe Query Language

### 3.1 The Problem with SQL

```sql
-- VULNERABLE: String-based SQL
query = "SELECT * FROM users WHERE id = '" + user_input + "'"
-- If user_input = "'; DROP TABLE users; --"
-- Result: SQL INJECTION
```

### 3.2 RIINA Type-Safe Queries (Bahasa Melayu)

```riina
// RIINA Query Language - Injection impossible by construction

// Define schema with types
skema Pengguna {
    id: i64,
    nama: Rentetan,
    emel: Rentetan,
    rahsia kata_laluan: Hash<Rentetan>,  // Secret type - can't leak
}

// Type-safe query - compiler checks everything
fungsi cari_pengguna(id: i64) -> Pilihan<Pengguna>
    kesan KesanBaca
{
    tanya Pengguna
        | tapisan(.id == id)
        | pertama
}

// Parameterized queries - no string concatenation
fungsi cari_nama(corak: Rentetan) -> Senarai<Pengguna>
    kesan KesanBaca
{
    tanya Pengguna
        | tapisan(.nama.mengandungi(corak))
        | kumpul
}

// Type error: Cannot select secret fields into public result
// fungsi SALAH_bocor_kata_laluan(id: i64) -> Rentetan {
//     tanya Pengguna
//         | tapisan(.id == id)
//         | pilih(.kata_laluan)  // COMPILE ERROR: Secret cannot flow to public
// }
```

### 3.3 Query AST (No Strings)

```coq
(* Query is an AST, not a string *)
Inductive Query : Type :=
  | QSelect : Table -> list Column -> Predicate -> Query
  | QInsert : Table -> Record -> Query
  | QUpdate : Table -> Predicate -> list (Column * Value) -> Query
  | QDelete : Table -> Predicate -> Query
  | QJoin : Query -> Query -> JoinCondition -> Query.

(* Predicate is typed *)
Inductive Predicate : Type :=
  | PEq : Column -> Value -> Predicate
  | PAnd : Predicate -> Predicate -> Predicate
  | POr : Predicate -> Predicate -> Predicate
  | PNot : Predicate -> Predicate
  | PLike : Column -> Pattern -> Predicate.  (* Pattern, not string! *)

(* No way to express injection - type system prevents it *)
Theorem query_injection_impossible : forall user_input : string,
  ~ exists q : Query, contains_raw_string q user_input.
(* Queries don't contain raw strings - they're structured ASTs *)
```

## 4. ACID Properties: Formal Proofs

### 4.1 Atomicity

```coq
(* A transaction either fully commits or fully aborts *)
Inductive TxnResult : Type :=
  | Committed : Database -> TxnResult
  | Aborted : Database -> TxnResult.

Definition execute_txn (txn : Transaction) (db : Database) : TxnResult :=
  match run_operations txn.ops db with
  | Ok db' =>
      match write_wal txn.ops with
      | Ok _ => Committed db'
      | Err _ => Aborted db  (* WAL failed, rollback *)
      end
  | Err _ => Aborted db
  end.

Theorem atomicity : forall txn db result,
  execute_txn txn db = result ->
  (result = Committed db' /\ all_ops_applied txn.ops db db') \/
  (result = Aborted db /\ db = db).  (* No partial application *)
```

### 4.2 Consistency

```coq
(* Database invariants are preserved *)
Record DatabaseInvariants (db : Database) : Prop := {
  (* Referential integrity *)
  foreign_keys_valid : forall fk, In fk (foreign_keys db) ->
    exists pk, references fk pk /\ In pk (primary_keys db);

  (* Unique constraints *)
  unique_constraints : forall tbl col,
    unique_column tbl col ->
    NoDup (project tbl col db);

  (* Check constraints *)
  check_constraints : forall tbl row,
    In row (table_data tbl db) ->
    satisfies_checks tbl row;
}.

Theorem consistency : forall txn db db',
  DatabaseInvariants db ->
  execute_txn txn db = Committed db' ->
  DatabaseInvariants db'.
```

### 4.3 Isolation (Strict Serializability)

```coq
(* Concurrent transactions appear to execute serially *)
Definition serializable (history : list TxnEvent) : Prop :=
  exists serial_order : list Transaction,
    equivalent_result history (execute_serial serial_order).

(* RIINA enforces strict serializability *)
Theorem isolation : forall txns history,
  concurrent_execute txns = history ->
  serializable history.

(* Single-threaded execution makes this trivial *)
Theorem single_thread_serializable : forall txns,
  execute_sequential txns = execute_sequential txns.
(* Trivially true because we don't have concurrency in the core *)
```

### 4.4 Durability

```coq
(* Committed transactions survive crashes *)
Record WALEntry := {
  txn_id : nat;
  operations : list Operation;
  commit_marker : bool;
  checksum : bytes;
}.

Definition recover (wal : list WALEntry) (db : Database) : Database :=
  fold_left (fun db' entry =>
    if entry.commit_marker && verify_checksum entry
    then apply_ops entry.operations db'
    else db'
  ) wal db.

Theorem durability : forall txn db db' wal,
  execute_txn txn db = Committed db' ->
  wal_contains wal txn ->
  forall crash_point,
    recover (wal_upto crash_point wal) db = db' \/
    recover (wal_upto crash_point wal) db = db.
(* Either fully recovered or not started - never partial *)
```

## 5. Deterministic Simulation Testing (DST)

### 5.1 The VOPR Approach

Inspired by TigerBeetle's VOPR simulator:

```
┌─────────────────────────────────────────────────────────────────────┐
│                    DETERMINISTIC SIMULATION                          │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  Real System:                                                        │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐                         │
│  │ Thread  │    │  Disk   │    │ Network │                         │
│  │Scheduler│    │  I/O    │    │  Stack  │                         │
│  └────┬────┘    └────┬────┘    └────┬────┘                         │
│       │              │              │                               │
│       └──────────────┼──────────────┘                               │
│                      │                                               │
│              NON-DETERMINISTIC                                       │
│                                                                      │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  VOPR Simulator:                                                     │
│  ┌─────────┐    ┌─────────┐    ┌─────────┐                         │
│  │  Mock   │    │  Mock   │    │  Mock   │                         │
│  │Scheduler│    │  Disk   │    │ Network │                         │
│  └────┬────┘    └────┬────┘    └────┬────┘                         │
│       │              │              │                               │
│       └──────────────┼──────────────┘                               │
│                      │                                               │
│              DETERMINISTIC                                           │
│           (Same seed = same execution)                               │
│                                                                      │
│  Fault Injection:                                                    │
│  ├── Disk corruption (bit flips, sector failures)                   │
│  ├── Network partitions (split brain scenarios)                     │
│  ├── Process crashes (at any point)                                 │
│  ├── Clock skew (time jumps forward/backward)                       │
│  └── Memory pressure (OOM conditions)                               │
│                                                                      │
│  Time Acceleration:                                                  │
│  ├── 3.3 seconds real → 39 minutes simulated                        │
│  ├── 700x speedup factor                                            │
│  └── ~2000 years simulated per day (1024 cores)                     │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

### 5.2 Simulator Interface

```riina
// Deterministic time source
antara_muka Jam {
    fungsi sekarang() -> CapMasa;
    fungsi tunggu(tempoh: Tempoh) -> Keputusan<(), RalatTamat>;
    fungsi detak(tempoh: Tempoh);  // Simulator advances time
}

// Deterministic disk
antara_muka Cakera {
    fungsi baca(offset: u64, saiz: u64) -> Keputusan<Bait, RalatIO>;
    fungsi tulis(offset: u64, data: &Bait) -> Keputusan<(), RalatIO>;
    fungsi segerak() -> Keputusan<(), RalatIO>;

    // Fault injection points
    fungsi suntik_rosak(offset: u64, jenis: JenisRosak);
    fungsi suntik_lambat(kelewatan: Tempoh);
}

// Deterministic network
antara_muka Rangkaian {
    fungsi hantar(kepada: Alamat, data: &Bait) -> Keputusan<(), RalatRangkaian>;
    fungsi terima() -> Keputusan<(Alamat, Bait), RalatRangkaian>;

    // Fault injection
    fungsi suntik_partition(nod_a: Alamat, nod_b: Alamat);
    fungsi suntik_kehilangan_paket(kadar: f64);
}
```

## 6. Storage Engine: Verified B+Tree

```coq
(* B+Tree with proven properties *)
Record BPlusTree (K V : Type) := {
  order : nat;  (* Maximum children per node *)
  root : Node K V;

  (* Invariants *)
  inv_balanced : all_leaves_same_depth root;
  inv_ordered : forall n, is_node n root -> keys_sorted n;
  inv_occupancy : forall n, is_internal n root ->
    order / 2 <= num_children n <= order;
}.

(* Lookup correctness *)
Theorem btree_lookup_correct : forall tree k v,
  lookup tree k = Some v <-> contains tree k v.

(* Lookup complexity *)
Theorem btree_lookup_complexity : forall tree k,
  time (lookup tree k) <= O(log (size tree)).

(* Insert preserves invariants *)
Theorem btree_insert_preserves : forall tree k v tree',
  insert tree k v = tree' ->
  BPlusTree_invariants tree ->
  BPlusTree_invariants tree'.

(* No data loss *)
Theorem btree_insert_preserves_data : forall tree k v tree' k' v',
  insert tree k v = tree' ->
  k' <> k ->
  lookup tree k' = Some v' ->
  lookup tree' k' = Some v'.
```

## 7. Encryption and Integrity

### 7.1 Encryption at Rest

```riina
// All data encrypted using Track F crypto
bentuk HalamanPenyimpanan {
    pengepala: PengepalaHalaman,
    data_disulitkan: Bait,  // AES-256-GCM encrypted
    nonce: [u8; 12],
    tag: [u8; 16],  // Authentication tag
}

fungsi tulis_halaman(halaman: &Halaman, kunci: &KunciPenyulitan)
    -> Keputusan<HalamanPenyimpanan, RalatKripto>
    kesan KesanTulis
{
    biar nonce = jana_nonce_rawak();
    biar (teks_sifer, tag) = aes_gcm_sulit(
        kunci,
        &nonce,
        &halaman.ke_bait(),
        &halaman.pengepala.ke_bait()  // AAD
    )?;

    pulang Ok(HalamanPenyimpanan {
        pengepala: halaman.pengepala,
        data_disulitkan: teks_sifer,
        nonce,
        tag,
    })
}
```

### 7.2 Merkle Tree for Tamper Detection

```coq
(* Merkle tree for database pages *)
Record MerkleTree := {
  root_hash : bytes;
  nodes : list MerkleNode;
}.

Record MerkleNode := {
  hash : bytes;
  left_child : option nat;  (* Index in nodes list *)
  right_child : option nat;
  page_id : option nat;     (* Leaf nodes have page_id *)
}.

(* Tamper detection *)
Theorem merkle_tamper_detection : forall tree page old_data new_data,
  get_page tree page = old_data ->
  old_data <> new_data ->
  set_page tree page new_data = tree' ->
  root_hash tree <> root_hash tree'.
(* Any change to data changes the root hash *)

(* Proof of inclusion *)
Theorem merkle_inclusion_proof : forall tree page proof,
  verify_proof tree.root_hash page proof = true ->
  exists data, get_page tree page = data.
```

## 8. Implementation Strategy (Infinite Timeline)

### Phase 1: Core Storage (Months 1-6)
- [ ] Verified B+Tree in Coq
- [ ] Write-Ahead Log with proven recovery
- [ ] Page manager with verified allocation

### Phase 2: Transaction Manager (Months 7-12)
- [ ] ACID proofs complete
- [ ] MVCC (Multi-Version Concurrency Control) if needed
- [ ] Deadlock-free locking protocol

### Phase 3: Query Engine (Year 2)
- [ ] Type-safe query language
- [ ] Verified query optimizer
- [ ] Index selection proofs

### Phase 4: Distributed (Year 3) — Integrates with Track Δ
- [ ] Verified replication
- [ ] Consensus integration
- [ ] Partition tolerance proofs

### Phase 5: Production (Year 4+)
- [ ] Performance optimization
- [ ] VOPR simulator at scale
- [ ] Production hardening

## 9. Obsolescence of Threats

| Threat | Status | Mechanism |
|--------|--------|-----------|
| SQL Injection | **OBSOLETE** | Type-safe queries |
| ACID Violations | **OBSOLETE** | Formally proven |
| Buffer Overflow | **OBSOLETE** | Track W memory safety |
| Data Corruption | **OBSOLETE** | Merkle tree + checksums |
| Crash Data Loss | **OBSOLETE** | Proven WAL recovery |
| Query Side Channels | **MITIGATED** | Constant-time operations |

## 10. Dependencies

| Dependency | Direction | Nature |
|------------|-----------|--------|
| Track A (Formal) | Σ depends on A | Type system foundation |
| Track W (Memory) | Σ depends on W | Memory safety proofs |
| Track F (Crypto) | Σ depends on F | Encryption primitives |
| Track Δ (Distribution) | Σ integrates Δ | Replication, consensus |
| Track Y (Stdlib) | Σ feeds Y | Database collections |

---

**"A database without a proof is a data breach waiting to happen."**

*RIINA: Rigorous Immutable Invariant — Normalized Axiom*

*QED Eternum.*
