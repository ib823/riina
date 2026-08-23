// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Three cross-backend gaps that made a compiled program disagree with the
//! interpreter — or refuse to compile at all.
//!
//! # `ke_teks` / `cetak` on a compound value
//!
//! `riina_format` and `riina_builtin_ke_teks` were each a flat tag switch
//! ending in `default: "<value>"`. Scalars were covered; a list, a pair or a
//! map was not. So `cetakln(ke_teks([2, 4, 6]))` printed `[2, 4, 6]` under
//! `riinac run` and the literal text `<value>` from the compiled binary. The
//! program ran and lied — the worst failure mode this backend has.
//!
//! Both now delegate to one recursive `riina_format_alloc`, written against the
//! interpreter's `builtins::format_value` case for case.
//!
//! # Forward calls
//!
//! `Expr::LetRecGroup` — every top-level `fungsi` in a file, and every function
//! in an imported module — was lowered by expanding it into a nested `LetRec`
//! CHAIN, which scopes backwards only. A function calling one declared BELOW it
//! type-checked, interpreted correctly, and then failed `riinac build` with
//! `unbound variable: <callee>`. Across a module boundary the author does not
//! even control the order (`<module>_<callee>`). Definition-before-use is a C
//! constraint with no business in RIINA's surface language.
//!
//! # `:=` in statement position
//!
//! `parse_assignment` read its right-hand side with `parse_expr`, which parses
//! a whole statement SEQUENCE — so `r := 100; f();` became `r := (100; f())`,
//! swallowing every following statement into the assigned value. It surfaced as
//! a type error on the assignment, or not at all when the sequence happened to
//! end in the right type. `all_examples.rii`'s own `contoh_ruj` did not
//! type-check because of it.

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
            "!!! SKIPPED (tools missing: {}) — gap coverage NOT exercised.",
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
        let stem = format!("gaps_{tag}");
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

fn run_wasm(sb: &Sandbox, src: &PathBuf) -> String {
    let build = Command::new(env!("CARGO_BIN_EXE_riinac"))
        .args(["build", "--target", "wasm32"])
        .arg(src)
        .output()
        .expect("riinac build wasm32");
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
        "wasmtime rejected or trapped — \"not enough arguments on the stack for \
         i64.store\" here means a group placeholder lost its local: {}{}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    String::from_utf8_lossy(&run.stdout).into_owned()
}

/// Compound values render identically in both backends.
///
/// Nesting, empty lists, pairs and a bare `cetakln` of a list are all included:
/// the old code had no case for any of them, so each printed `<value>`.
#[test]
fn compound_values_render_the_same_in_both_backends() {
    let sb = Sandbox::new("format");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan Tulis {
    cetakln(ke_teks([2, 4, 6]));
    cetakln(ke_teks(["a", "b"]));
    cetakln(ke_teks([betul, salah]));
    cetakln(ke_teks(([1, 2], 3)));
    cetakln(ke_teks([]));
    cetakln(ke_teks([[1, 2], [3]]));
    cetakln([9, 8]);
    cetakln(ke_teks(()));
    pulang 0;
}
"#,
    );
    // Asserted absolutely as well as differentially: a list renders unquoted
    // (`[a, b]`, not `["a", "b"]`) because `ke_teks` follows `format_value`,
    // not `Display`. Two backends could agree on the quoted form and both be
    // wrong against the interpreter's own `ke_teks`.
    let expected = "[2, 4, 6]\n[a, b]\n[betul, salah]\n([1, 2], 3)\n[]\n[[1, 2], [3]]\n[9, 8]\n()\n";
    let interp = run_interp(&src);
    assert_eq!(interp, expected, "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
}

/// A function may call one declared below it.
#[test]
fn a_forward_call_compiles() {
    let sb = Sandbox::new("forward");
    let src = sb.src(
        r#"
fungsi luar(x: Nombor) -> Nombor kesan Bersih {
    kedua_kali(x) + 1
}

fungsi kedua_kali(x: Nombor) -> Nombor kesan Bersih {
    x * 2
}

fungsi utama() -> Nombor kesan Tulis {
    cetakln(ke_teks(luar(5)));
    pulang 0;
}
"#,
    );
    let interp = run_interp(&src);
    assert_eq!(interp, "11\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
    // WASM too. The group's closures capture its placeholders, and a
    // placeholder with no defining instruction gets no WASM local — the module
    // then fails validation with "not enough arguments on the stack for
    // i64.store". C tolerated it (its variable declarations walk operands), so
    // this leg is what actually pins the placeholders being real emitted values.
    if require_backend_tools(&["cc", "wasmtime"]) {
        assert_eq!(run_wasm(&sb, &src), interp, "WASM backend disagrees");
    }
}

/// Genuine mutual recursion — each function calls the other, so neither
/// ordering would have worked under the old backward-only chain.
///
/// `faktorial` rides along to pin that plain self-recursion still resolves: the
/// group patch has to cover a member capturing its OWN placeholder too, which
/// is the case the single-binding `FixClosure` used to own.
#[test]
fn mutual_recursion_compiles_in_both_directions() {
    let sb = Sandbox::new("mutual");
    let src = sb.src(
        r#"
fungsi genap(n: Nombor) -> Benar kesan Bersih {
    kalau n == 0 { betul } lain { ganjil(n - 1) }
}

fungsi ganjil(n: Nombor) -> Benar kesan Bersih {
    kalau n == 0 { salah } lain { genap(n - 1) }
}

fungsi faktorial(n: Nombor) -> Nombor kesan Bersih {
    kalau n <= 1 { 1 } lain { n * faktorial(n - 1) }
}

fungsi utama() -> Nombor kesan Tulis {
    cetakln(ke_teks(genap(10)));
    cetakln(ke_teks(ganjil(10)));
    cetakln(ke_teks(genap(7)));
    cetakln(ke_teks(faktorial(10)));
    pulang 0;
}
"#,
    );
    let interp = run_interp(&src);
    assert_eq!(interp, "betul\nsalah\nsalah\n3628800\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
    if require_backend_tools(&["cc", "wasmtime"]) {
        assert_eq!(run_wasm(&sb, &src), interp, "WASM backend disagrees");
    }
}

/// `r := e;` assigns only `e`, and the statements after it still run.
#[test]
fn assignment_in_statement_position_does_not_swallow_the_block() {
    let sb = Sandbox::new("assign");
    let src = sb.src(
        r#"
fungsi utama() -> Nombor kesan (Tulis | Baca) {
    biar r = ruj 1 @Awam;
    r := 100;
    cetakln("selepas: " + ke_teks(!r));
    r := kalau !r > 50 { 7 } lain { 9 };
    cetakln("cabang: " + ke_teks(!r));
    pulang 0;
}
"#,
    );
    let interp = run_interp(&src);
    assert_eq!(interp, "selepas: 100\ncabang: 7\n", "interpreter");
    if require_backend_tools(&["cc"]) {
        assert_eq!(run_native(&sb, &src), interp, "C backend disagrees");
    }
}
