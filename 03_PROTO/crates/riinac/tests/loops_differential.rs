// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! `selagi` / `ulang` / `putus` / `lanjut` and `biar ubah`, across the backends.
//!
//! # The bugs this pins
//!
//! Loops were not loops. `selagi cond { body }` was rewritten by the parser into
//! `if cond { body; () } else { () }` and `ulang { body }` into `body; ()`, so a
//! loop ran its body AT MOST ONCE while reading, checking and formatting like a
//! loop. `putus`/`lanjut` both desugared to `()`, so loop control did nothing at
//! all. Nothing diagnosed any of it — `07_EXAMPLES/00_basics/loops_while.rii`
//! type-checked, was listed as a passing example, and printed `Nilai i: 0` once
//! where it should count 0..4.
//!
//! `biar ubah` was decorative in the same way: `x = e;` re-parsed as a shadowing
//! `biar`, so a write inside a `kalau`/loop body was discarded at the closing
//! brace. An accumulator summed to its FIRST element and reported it as the
//! total.
//!
//! The two defects hid each other. With one-shot loops a lost write was rarely
//! observable; making loops real without real writes would have turned the same
//! programs into non-termination. So they are fixed together, and tested
//! together here.
//!
//! # Why differential rather than expected-output assertions
//!
//! Agreement between backends that reach loops by different routes is evidence
//! a shared hand-written expectation cannot give. The interpreter iterates
//! directly; the C backend goes through a CFG back edge and `goto`. Each case
//! also carries an absolute expected value, because two backends can agree and
//! both be wrong — `1` for `sum 1..100` would be perfectly consistent.
//!
//! # The WASM half
//!
//! `emit_structured` used to know only FORWARD if/else regions, so a loop's
//! back edge would have walked the same blocks forever; the backend refused
//! the module instead (REQ-78 fail-closed). It now emits real structured
//! control flow — a `block` wrapping a `loop`, with `br_if` for the exit test,
//! `br 0` for the back edge and `lanjut`, and `br 1` for `putus` — so WASM is
//! a third independent implementation of loop semantics to differ against.
//!
//! Three of the four backends therefore reach a loop by different routes: the
//! interpreter iterates directly, C follows a CFG back edge through `goto`, and
//! WASM re-enters a structured `loop` by label depth. Agreement between those
//! is much stronger evidence than any hand-written expectation.

use std::path::PathBuf;
use std::process::Command;

fn tool_available(tool: &str) -> bool {
    Command::new(tool)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Guard for tests needing an external backend toolchain (`cc`, `wasmtime`).
///
/// Mirrors `wasm_c_differential.rs`: a missing tool PANICS by default, because
/// a test that cannot run must never report `ok`. Opt out deliberately with
/// `RIINA_ALLOW_MISSING_BACKEND_TOOLS=1`, which announces the lost coverage.
fn require_backend_tools(tools: &[&str]) -> bool {
    let missing: Vec<&str> = tools
        .iter()
        .copied()
        .filter(|t| !tool_available(t))
        .collect();
    if missing.is_empty() {
        return true;
    }
    if std::env::var("RIINA_ALLOW_MISSING_BACKEND_TOOLS").is_ok() {
        eprintln!(
            "!!! SKIPPED (tools missing: {}) — loop coverage NOT exercised.",
            missing.join(", ")
        );
        return false;
    }
    panic!(
        "required backend tool(s) missing: {}. This test cannot verify anything \
         without them, so it fails rather than reporting a false pass. Install \
         them, or set RIINA_ALLOW_MISSING_BACKEND_TOOLS=1 to skip deliberately.",
        missing.join(", ")
    );
}

/// A throwaway directory, unique per test name and pid.
///
/// The stem must be unique: `riinac build` derives its intermediate C path from
/// it, so a shared name makes parallel tests race on the same file.
struct Sandbox {
    dir: PathBuf,
    stem: String,
}

impl Sandbox {
    fn new(tag: &str) -> Self {
        let stem = format!("loops_{tag}");
        let dir = std::env::temp_dir().join(format!("riina_{stem}_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create sandbox");
        Self { dir, stem }
    }

    fn src(&self, source: &str) -> PathBuf {
        let p = self.dir.join(format!("{}.rii", self.stem));
        std::fs::write(&p, source).expect("write program");
        p
    }
}

impl Drop for Sandbox {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// Interpreter stdout, WITHOUT the trailing line `riinac run` adds for the
/// program's final value. Every case below ends in a `cetakln`, so the dropped
/// line is always that echoed value and never program output.
fn run_interp(src: &PathBuf) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_riinac"))
        .arg("run")
        .arg(src)
        .output()
        .expect("riinac run");
    assert!(
        out.status.success(),
        "interpreter failed: {}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let s = String::from_utf8_lossy(&out.stdout).into_owned();
    let mut lines: Vec<&str> = s.lines().collect();
    lines.pop();
    if lines.is_empty() {
        String::new()
    } else {
        format!("{}\n", lines.join("\n"))
    }
}

fn run_native(sb: &Sandbox, src: &PathBuf) -> String {
    let build = Command::new(env!("CARGO_BIN_EXE_riinac"))
        .arg("build")
        .arg(src)
        .output()
        .expect("riinac build");
    assert!(
        build.status.success(),
        "native build failed: {}{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let bin = sb.dir.join(&sb.stem);
    let run = Command::new(&bin).output().expect("run native binary");
    assert!(
        run.status.success(),
        "native binary failed (exit {:?}): {}{}",
        run.status.code(),
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    String::from_utf8_lossy(&run.stdout).into_owned()
}

/// Build `src` for `wasm32` and run the module under wasmtime.
///
/// The WASM backend is the one that has to *reconstruct* structure from the
/// CFG, so a loop shape it gets wrong shows up either as a module wasmtime
/// rejects (a bad `br` depth is a validation error, not a wrong answer) or as
/// output that disagrees with the other two backends. Both are caught here.
fn run_wasm(sb: &Sandbox, src: &PathBuf) -> String {
    let build = Command::new(env!("CARGO_BIN_EXE_riinac"))
        .args(["build", "--target", "wasm32"])
        .arg(src)
        .output()
        .expect("riinac build --target wasm32");
    assert!(
        build.status.success(),
        "wasm build failed: {}{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let wasm = sb.dir.join(format!("{}.wasm", sb.stem));
    let run = Command::new("wasmtime")
        .arg("run")
        .arg(&wasm)
        .output()
        .expect("wasmtime run");
    assert!(
        run.status.success(),
        "wasmtime rejected or trapped on the module (exit {:?}): {}{}",
        run.status.code(),
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    String::from_utf8_lossy(&run.stdout).into_owned()
}

/// `selagi` runs its body until the condition goes false, and a `biar ubah`
/// write inside the body survives the iteration that made it.
///
/// Under the old desugaring this printed `i=0` once and then `akhir i=0`.
#[test]
fn selagi_iterates_and_writes_escape_the_body() {
    let sb = Sandbox::new("selagi");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan Tulis {
    biar ubah i = 0;
    selagi i < 5 {
        cetakln("i=" + ke_teks(i));
        i = i + 1;
    };
    cetakln("akhir i=" + ke_teks(i));
    pulang 0;
}
"#,
    );
    let expected = "i=0\ni=1\ni=2\ni=3\ni=4\nakhir i=5\n";
    let interp = run_interp(&src);
    assert_eq!(interp, expected, "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
    if require_backend_tools(&["wasmtime"]) {
        assert_eq!(run_wasm(&sb, &src), interp, "WASM backend disagrees");
    }
}

/// An accumulator loop. The answer is checked absolutely: 5050 is the sum
/// 1..100, where the pre-fix compiler produced 1 (one iteration, write lost).
#[test]
fn a_mutable_accumulator_sums_across_iterations() {
    let sb = Sandbox::new("accum");
    let src = sb.src(
        r#"
fungsi jumlah_sehingga(n: Nombor) -> Nombor kesan Bersih {
    biar ubah jumlah = 0;
    biar ubah i = 1;
    selagi i <= n {
        jumlah = jumlah + i;
        i = i + 1;
    };
    jumlah
}

fungsi utama() -> Nombor kesan Tulis {
    cetakln(ke_teks(jumlah_sehingga(100)));
    cetakln(ke_teks(jumlah_sehingga(10000)));
    pulang 0;
}
"#,
    );
    let expected = "5050\n50005000\n";
    let interp = run_interp(&src);
    assert_eq!(interp, expected, "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
    if require_backend_tools(&["wasmtime"]) {
        assert_eq!(run_wasm(&sb, &src), interp, "WASM backend disagrees");
    }
}

/// A local accumulator keeps the function `kesan Bersih`.
///
/// A `biar ubah` slot is deliberately NOT a `ruj` cell: it cannot be aliased or
/// escape its binder, so reading and writing it carries no effect. Were slots
/// lowered to `Ref`/`Deref`/`Assign` this program would demand `Baca`+`Tulis`
/// and every counting loop in the corpus would need re-annotating.
#[test]
fn a_local_slot_does_not_make_a_function_effectful() {
    let sb = Sandbox::new("pure");
    let src = sb.src(
        r#"
fungsi kira() -> Nombor kesan Bersih {
    biar ubah n = 0;
    selagi n < 3 {
        n = n + 1;
    };
    n
}

fungsi utama() -> Nombor kesan Tulis {
    cetakln(ke_teks(kira()));
    pulang 0;
}
"#,
    );
    assert_eq!(run_interp(&src), "3\n");
}

/// `putus` leaves the loop and `lanjut` skips to the next iteration. Both used
/// to be `()`, so this program printed nothing and looped forever once loops
/// became real.
#[test]
fn putus_and_lanjut_control_the_loop() {
    let sb = Sandbox::new("control");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan Tulis {
    biar ubah n = 0;
    ulang {
        n = n + 1;
        kalau n % 3 == 0 { lanjut; };
        kalau n > 8 { putus; };
        cetakln("n=" + ke_teks(n));
    };
    pulang 0;
}
"#,
    );
    let expected = "n=1\nn=2\nn=4\nn=5\nn=7\nn=8\n";
    let interp = run_interp(&src);
    assert_eq!(interp, expected, "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
    if require_backend_tools(&["wasmtime"]) {
        assert_eq!(run_wasm(&sb, &src), interp, "WASM backend disagrees");
    }
}

/// `pulang` inside a loop unwinds to the enclosing FUNCTION, not to the loop.
///
/// This is why `selagi` is an AST node rather than a desugaring into a
/// self-applied closure: a closure would have caught the return one iteration
/// out and the loop would have continued with the wrong value.
#[test]
fn pulang_inside_a_loop_leaves_the_function() {
    let sb = Sandbox::new("return");
    let src = sb.src(
        r#"
fungsi cari_pertama_lebih(n: Nombor) -> Nombor kesan Bersih {
    biar ubah i = 0;
    selagi i < 100 {
        kalau i > n { pulang i; };
        i = i + 1;
    };
    0 - 1
}

fungsi utama() -> Nombor kesan Tulis {
    cetakln(ke_teks(cari_pertama_lebih(7)));
    pulang 0;
}
"#,
    );
    let interp = run_interp(&src);
    assert_eq!(interp, "8\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
    if require_backend_tools(&["wasmtime"]) {
        assert_eq!(run_wasm(&sb, &src), interp, "WASM backend disagrees");
    }
}

/// A parameter named like an enclosing `biar ubah` is an ordinary immutable
/// binding, and writing the outer slot does not disturb it.
///
/// The parser decides read-by-read whether a name is a slot, so every binder
/// that can shadow one has to push a scope. Miss one and the callee's parameter
/// would be read through the caller's cell.
#[test]
fn a_parameter_shadows_an_enclosing_slot() {
    let sb = Sandbox::new("shadow");
    let src = sb.src(
        r#"
fungsi tambah_satu(x: Nombor) -> Nombor kesan Bersih {
    x + 1
}

fungsi utama() -> Nombor kesan Tulis {
    biar ubah x = 1;
    biar dari_param = tambah_satu(100);
    x = x + 1;
    cetakln(ke_teks(x) + "," + ke_teks(dari_param));
    pulang 0;
}
"#,
    );
    let interp = run_interp(&src);
    assert_eq!(interp, "2,101\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
}

/// A closure created inside a loop body sees the slot's CURRENT value, and a
/// write made through the closure is visible after it returns. `untuk` desugars
/// to `senarai_peta` over a closure, so without this an accumulator written
/// inside a `untuk` body would be discarded at the end of each element.
#[test]
fn a_slot_written_inside_a_untuk_body_survives_the_loop() {
    let sb = Sandbox::new("untuk");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan Tulis {
    biar ubah jumlah = 0;
    untuk x dalam [1, 2, 3, 4] {
        jumlah = jumlah + x;
    };
    cetakln(ke_teks(jumlah));
    pulang 0;
}
"#,
    );
    assert_eq!(run_interp(&src), "10\n");
}

/// `untuk` compiles. It desugars to `senarai_peta`, which was registered as a
/// codegen-supported builtin — so `docs/api/STDLIB.md` published it as
/// "native-only" — while `emit.rs` emitted no body for it. Every `untuk` loop
/// therefore died at LINK time with `undefined reference to
/// riina_builtin_senarai_peta`: the most idiomatic loop in the language could
/// not be compiled, and said so only as a linker error.
#[test]
fn untuk_compiles_and_agrees_with_the_interpreter() {
    let sb = Sandbox::new("untukc");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan Tulis {
    biar ubah jumlah = 0;
    untuk x dalam [1, 2, 3, 4, 5] {
        jumlah = jumlah + x;
    };
    biar dua = senarai_peta(([1, 2, 3], fungsi(x: Nombor) -> Nombor { x * 2 }));
    biar besar = senarai_tapis(([1, 5, 2, 8], fungsi(x: Nombor) -> Benar { x > 3 }));
    cetakln(ke_teks(jumlah));
    // Element-wise rather than `ke_teks(dua)`: `ke_teks` of a LIST still
    // diverges (the interpreter prints `[2, 4, 6]`, C prints `<value>`), which
    // is a separate gap and would mask what this test is checking.
    cetakln(ke_teks(senarai_dapat((dua, 0))) + "," + ke_teks(senarai_dapat((dua, 2))));
    cetakln(ke_teks(senarai_panjang(besar)) + ":" + ke_teks(senarai_dapat((besar, 1))));
    pulang 0;
}
"#,
    );
    let interp = run_interp(&src);
    assert_eq!(interp, "15\n2,6\n2:8\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
}

/// `!` on a boolean is logical negation, in the compiled backends too.
///
/// The token is shared with dereference, so `Expr::Deref` carried the overload
/// all the way to the IR's `Load` — a memory read in every backend. The
/// typechecker accepted it, the interpreter dispatched on the runtime value and
/// got it right, and the C backend compiled silently and then aborted with
/// "load on non-ref" at runtime. Resolved at lowering now, where the operand's
/// type is known.
#[test]
fn logical_not_works_in_the_compiled_backends() {
    let sb = Sandbox::new("not");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan Tulis {
    biar sah = betul;
    biar gagal = salah;
    kalau !sah { cetakln("A: songsang") } lain { cetakln("A: betul") };
    kalau !gagal { cetakln("B: betul") } lain { cetakln("B: songsang") };
    kalau sah && !gagal { cetakln("C: betul") } lain { cetakln("C: songsang") };
    pulang 0;
}
"#,
    );
    let interp = run_interp(&src);
    assert_eq!(interp, "A: betul\nB: betul\nC: betul\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
}

/// The WASM backend compiles a loop, and gets the same answer as the other two.
///
/// This replaces `loops_are_refused_by_the_wasm_backend`. The refusal was
/// honest but temporary: `emit_structured` handled forward if/else regions
/// only, so a back edge had no structure to map onto and the backend failed
/// closed (REQ-78) rather than emit the one-shot shape loops were introduced to
/// fix. It now emits a `block` wrapping a `loop`, so the construct is expressed
/// rather than refused — and the assertion flips from "must fail" to "must
/// agree".
#[test]
fn a_loop_compiles_to_wasm_and_agrees() {
    let sb = Sandbox::new("wasmloop");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan Tulis {
    biar ubah i = 0;
    selagi i < 3 {
        i = i + 1;
    };
    cetakln(ke_teks(i));
    pulang 0;
}
"#,
    );
    let interp = run_interp(&src);
    assert_eq!(interp, "3\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
    if require_backend_tools(&["wasmtime"]) {
        assert_eq!(run_wasm(&sb, &src), interp, "WASM backend disagrees");
    }
}

/// Nested loops, `putus` and `lanjut` from inside an `if` arm, a loop inside an
/// `if` arm, and `selagi betul` left only by `putus` — all in one program.
///
/// Each of these is a distinct label-depth calculation in the WASM emitter, and
/// an off-by-one in any of them is silent: `br 1` where `br 2` was meant still
/// validates, it just leaves the wrong loop. Only the ANSWER catches that,
/// which is why this is differential rather than a byte-comparison on the
/// emitted module.
#[test]
fn nested_loops_and_loop_control_agree_across_backends() {
    let sb = Sandbox::new("wasmnest");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan Tulis {
    biar ubah i = 0;
    biar ubah jum = 0;
    selagi i < 5 {
        biar ubah j = 0;
        selagi j < 4 {
            kalau j == 2 { j = j + 1; lanjut; } lain { () };
            jum = jum + (i * 10 + j);
            j = j + 1;
        };
        i = i + 1;
    };
    cetakln(ke_teks(jum));

    biar ubah k = 0;
    kalau jum > 0 {
        selagi k < 3 { k = k + 1; };
        ()
    } lain {
        k = 99;
        ()
    };
    cetakln(ke_teks(k));

    biar ubah m = 0;
    selagi betul {
        m = m + 1;
        kalau m == 7 { putus; } lain { () };
    };
    cetakln(ke_teks(m));
    pulang 0;
}
"#,
    );
    // 320 = sum over i in 0..5, j in {0,1,3} of (i*10 + j); k = 3; m = 7.
    let interp = run_interp(&src);
    assert_eq!(interp, "320\n3\n7\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
    if require_backend_tools(&["wasmtime"]) {
        assert_eq!(run_wasm(&sb, &src), interp, "WASM backend disagrees");
    }
}

/// `pulang` from inside a loop, in a callee, on WASM.
///
/// An early return unwinds past the `block`/`loop` frames the emitter opened.
/// WASM's `return` does that correctly only if the frames were balanced in the
/// first place; an unbalanced one is a validation error, so wasmtime refusing
/// the module is the failure mode this pins.
#[test]
fn pulang_out_of_a_wasm_loop_unwinds_the_function() {
    let sb = Sandbox::new("wasmret");
    let src = sb.src(
        r#"
fungsi cari(had: Nombor) -> Nombor kesan Bersih {
    biar ubah i = 1;
    selagi i < 1000 {
        kalau i * i > had { pulang i; } lain { () };
        i = i + 1;
    };
    0 - 1
}

fungsi gcd(a: Nombor, b: Nombor) -> Nombor kesan Bersih {
    biar ubah x = a;
    biar ubah y = b;
    selagi y != 0 {
        biar t = y;
        y = x % y;
        x = t;
    };
    x
}

fungsi utama() -> Nombor kesan Tulis {
    cetakln(ke_teks(cari(50)));
    cetakln(ke_teks(cari(10000)));
    cetakln(ke_teks(gcd(1071, 462)));
    pulang 0;
}
"#,
    );
    let interp = run_interp(&src);
    assert_eq!(interp, "8\n101\n21\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
    if require_backend_tools(&["wasmtime"]) {
        assert_eq!(run_wasm(&sb, &src), interp, "WASM backend disagrees");
    }
}

/// `"..." + ke_teks(n)` prints the JOINED STRING on WASM, not a heap address.
///
/// The lowerer typed every `+` result `Int` unless an operand was in the
/// numeric tower, so a string concatenation came out `Ty::Int`. The concat
/// itself was emitted correctly — only the static type was wrong — but
/// `cetakln` dispatches on that type in the WASM backend (values are untagged
/// i32 there, unlike C's runtime tags), so it sent the result pointer through
/// the integer path and printed a small decimal number. Every `cetakln("x=" +
/// ...)` in the corpus printed an address, silently, on WASM only.
#[test]
fn string_concatenation_prints_as_a_string_on_wasm() {
    let sb = Sandbox::new("wasmconcat");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan Tulis {
    biar ubah i = 0;
    selagi i < 3 {
        cetakln("i=" + ke_teks(i) + "!");
        i = i + 1;
    };
    cetakln("akhir=" + ke_teks(i));
    pulang 0;
}
"#,
    );
    let interp = run_interp(&src);
    assert_eq!(interp, "i=0!\ni=1!\ni=2!\nakhir=3\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
    if require_backend_tools(&["wasmtime"]) {
        assert_eq!(run_wasm(&sb, &src), interp, "WASM backend disagrees");
    }
}

/// `untuk` is still refused by WASM — for the LIST reason, not a loop reason.
///
/// `untuk` is sugar for `senarai_peta` over a closure, so it never went through
/// `emit_structured`'s loop path and the loop work does not unblock it. What
/// blocks it is list literals, which the WASM backend declares unsupported
/// (REQ-79) and fails closed on. Pinning the *message* keeps the two gaps from
/// being confused: a future regression that made loops fail again would fail
/// this test with the wrong reason rather than pass by coincidence.
#[test]
fn untuk_is_refused_by_wasm_for_the_list_gap_not_the_loop_gap() {
    let sb = Sandbox::new("wasmuntuk");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan Tulis {
    biar ubah jumlah = 0;
    untuk x dalam [1, 2, 3, 4, 5] {
        jumlah = jumlah + x;
    };
    cetakln(ke_teks(jumlah));
    pulang 0;
}
"#,
    );
    assert_eq!(run_interp(&src), "15\n", "interpreter");
    let out = Command::new(env!("CARGO_BIN_EXE_riinac"))
        .args(["build", "--target", "wasm32"])
        .arg(&src)
        .output()
        .expect("riinac build wasm32");
    let msg = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        !out.status.success(),
        "WASM cannot build list literals yet, so this must fail closed: {msg}"
    );
    assert!(
        msg.contains("list"),
        "the refusal must name LISTS as the reason — a loop-shaped refusal here \
         would be a regression in the loop lowering, got: {msg}"
    );
}
