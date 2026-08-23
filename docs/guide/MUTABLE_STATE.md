# Mutable state in RIINA

RIINA has three ways to hold a value that changes. They are not
interchangeable, and picking the wrong one is the difference between a pure
function and one that has to declare `Baca` and `Tulis`.

| Form | Written | Escapes its binder? | Effect | Coq |
|---|---|---|---|---|
| Immutable binding | `biar x = e;` | — | none | `ELet` |
| Mutable local ("slot") | `biar ubah x = e;` | no | **none** | compiler-level |
| Reference cell | `biar r = ruj e @Awam;` | yes | `Baca` / `Tulis` | `ERef`/`EDeref`/`EAssign` |

## `biar` — immutable

The default. Rebinding the same name shadows it for the rest of the block; the
old binding is untouched, and nothing outside the block sees either.

```riina
biar x = 1;
biar x = x + 1;   // a NEW binding, shadowing the first
```

## `biar ubah` — a mutable local slot

`biar ubah x = e;` binds a slot. `x = e;` writes it, and the write is visible
to every later read of `x`, **including reads outside the block that made it**:

```riina
fungsi jumlah_sehingga(n: Nombor) -> Nombor kesan Bersih {
    biar ubah jumlah = 0;
    biar ubah i = 1;
    selagi i <= n {
        jumlah = jumlah + i;   // survives the iteration
        i = i + 1;
    };
    jumlah                     // 5050 for n = 100
}
```

Note the effect: `kesan Bersih`. A slot carries **no effect**, which is what
lets an ordinary counting loop live inside a pure function.

That is sound because a slot is not first class. `SlotGet`/`SlotSet` name a
binder directly — there is no expression that yields the slot itself — so it
cannot be aliased, returned, or stored in a data structure. Its reads and
writes are unobservable outside the binding, which is the standard
encapsulated-state argument (the same reason Haskell's `runST` is pure).

An inner binding shadows an outer slot, as you would expect:

```riina
biar ubah x = 1;
biar x = 100;   // ordinary immutable binding; the slot is untouched
```

### History

Until 2026-08 `ubah` was parsed and discarded. `x = e;` re-parsed as a
shadowing `biar`, so a write inside a `kalau` or a loop body was thrown away at
the closing brace — with no diagnostic. An accumulator summed to its first
element and reported it as the total.

That defect and one-shot loops (see below) concealed each other: with a loop
body that ran once, a lost write was rarely visible. They were fixed together.

## `ruj` — a reference cell

When a mutable value genuinely has to escape — shared between closures, stored
in a structure, held at a security level other than `Awam` — use a real
reference:

```riina
fungsi guna_sel() -> Nombor kesan (Tulis | Baca) {
    biar r = ruj 42 @Awam;
    biar _ = (r := 100);
    !r
}
```

A `ruj` cell is first class, so it **does** carry effects: `ERef` and `EAssign`
join `EffectWrite`, `EDeref` joins `EffectRead`. Those rules mirror Coq
`Typing.v` T_Ref/T_Deref/T_Assign, including the Bell–LaPadula checks
(no-read-up on a dereference, no-write-down on an assignment), and are not
weakened for convenience.

`r := e;` in statement position assigns just `e`; the statements after it run
as written. (Until 2026-08 the right-hand side was parsed greedily, so
`r := 100; f();` read as `r := (100; f())`, swallowing the rest of the block
into the assigned value — the workaround was to bind it, `biar _ = (r := 100);`.
That is no longer needed.)

One sharp edge remains: assignment carries `Tulis`, not `Ubah`, despite `Ubah`
being the effect whose name means "mutate".

## Loops

`selagi` (while) and `ulang` (loop) are real loops, and `putus` (break) /
`lanjut` (continue) are real control flow.

They did not used to be. `selagi cond { body }` was rewritten by the parser
into `if cond { body; () } else { () }` and `ulang { body }` into `body; ()`, so
a loop ran its body **at most once** while reading, type-checking and
formatting exactly like a loop. `putus` and `lanjut` both desugared to `()`.
Nothing diagnosed any of it: `07_EXAMPLES/00_basics/loops_while.rii`
type-checked, was listed as a passing example, and printed `Nilai i: 0` once
where it should count 0 to 4.

`pulang` inside a loop unwinds to the enclosing **function**, not to the loop —
which is why `selagi` is an AST node rather than sugar for a self-applied
closure, since a closure would have caught the return one iteration out.

`untuk x dalam senarai { ... }` remains sugar for `senarai_peta` over a closure.
Writes to an enclosing `biar ubah` slot from inside a `untuk` body do survive
(the slot lives in the store, and the closure captures it), but `putus` and
`lanjut` are **not** accepted there — the parser rejects them with
`P0010` rather than accepting a loop-control statement it cannot honour.

### Backend support

| Backend | `selagi` / `ulang` | `untuk` |
|---|---|---|
| Interpreter (`riinac run`) | yes | yes |
| C (`riinac build`) | yes | yes |
| WASM (`riinac build --target wasm32`) | yes | **refused** |

The WASM emitter reconstructs structured control flow from the IR's CFG. A
`selagi`/`ulang` loop becomes a `block` wrapping a `loop`: the condition is
re-tested inside the `loop` so it sees the body's writes, `br_if` leaves when it
goes false, `br 0` is the back edge (and `lanjut`), and `br 1` is `putus`.

Which edges close a loop is decided by **dominance**, not block order. The
lowerer allocates a loop's exit block before the body it follows, so `putus`
branches to a lower-numbered block than the one it leaves; and it leaves an
unreachable block behind after a `putus` for whatever followed it textually.
Index order would read both as back edges and invent loops that are not there.

`untuk` is refused on WASM, but for an unrelated reason: it desugars to
`senarai_peta` over a list literal, and list literals are not supported by that
backend yet (REQ-79). As always the refusal is explicit — a backend that cannot
express a construct must fail closed rather than emit a stub (REQ-78).
