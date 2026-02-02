# RIINA vs Rust: Information Flow Security

## The Problem

Rust guarantees memory safety. It does **not** guarantee information flow safety.

A Rust program can compile and run while silently leaking secrets to stdout, log files, error messages, or network responses. The borrow checker cannot detect this — it was never designed to.

## The Comparison

| File | Language | Compiles? | Secret leaks? |
|------|----------|-----------|---------------|
| `vulnerable.rs` | Rust | Yes | Yes — card number printed to stdout |
| `secure.rii` | RIINA | No (correctly refuses) | No — compiler proves the leak is impossible |

## How RIINA Prevents This

1. **Secret types**: `Rahsia<Teks>` marks data as secret at the type level
2. **Effect tracking**: `kesan IO` and `kesan Kripto` are distinct — secret data cannot flow to IO
3. **Non-interference theorem**: Proven in Coq (`NonInterference_v2.v`) — for any two executions with different secrets but same public inputs, public outputs are identical
4. **Compile-time enforcement**: The type checker blocks the program before it ever runs

## The Takeaway

Rust compiles. RIINA refuses. The compiler proves the attack is impossible.

This is not a linter warning. This is a mathematical guarantee backed by 4,885 machine-checked theorems in Coq.
