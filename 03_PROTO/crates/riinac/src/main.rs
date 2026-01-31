//! RIINA Compiler Driver
//!
//! Main entry point for the RIINA compiler.
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

#![forbid(unsafe_code)]

mod diagnostics;
mod repl;
mod verify;

use std::fs;
use std::path::PathBuf;
use std::process;

use riina_parser::Parser;
use riina_typechecker::{type_check, Context};

#[derive(Debug)]
enum Command {
    Check,
    Run,
    Build,
    EmitC,
    EmitIR,
    Repl,
    Fmt,
    Doc,
    Lsp,
    Verify(verify::Mode),
}

fn usage() -> ! {
    eprintln!("Usage: riinac [command] <file.rii>");
    eprintln!();
    eprintln!("Commands:");
    eprintln!("  check    Parse and typecheck only (default)");
    eprintln!("  run      Parse, typecheck, and interpret");
    eprintln!("  build    Parse, typecheck, emit C, and compile");
    eprintln!("  emit-c   Parse, typecheck, and emit C to stdout");
    eprintln!("  emit-ir  Parse, typecheck, lower, and print IR");
    eprintln!("  doc      Generate HTML documentation");
    eprintln!("  fmt      Format a .rii file");
    eprintln!("  lsp      Start LSP server (stdio)");
    eprintln!("  repl     Interactive read-eval-print loop");
    eprintln!("  verify   Run verification gate [--fast|--full]");
    process::exit(1);
}

fn parse_args() -> (Command, Option<PathBuf>) {
    let args: Vec<String> = std::env::args().collect();

    // Handle verify early — it takes flags, not a file
    if args.len() >= 2 && args[1] == "verify" {
        let mode = if args.len() >= 3 {
            match args[2].as_str() {
                "--fast" => verify::Mode::Fast,
                "--full" => verify::Mode::Full,
                other => {
                    eprintln!("Unknown verify flag: {other}");
                    usage();
                }
            }
        } else {
            verify::Mode::Fast
        };
        return (Command::Verify(mode), None);
    }

    match args.len() {
        2 => {
            if args[1] == "repl" {
                return (Command::Repl, None);
            }
            if args[1] == "lsp" {
                return (Command::Lsp, None);
            }
            // riinac <file.rii> — default to check (backwards compat)
            (Command::Check, Some(PathBuf::from(&args[1])))
        }
        3 => {
            let cmd = match args[1].as_str() {
                "check" => Command::Check,
                "run" => Command::Run,
                "build" => Command::Build,
                "emit-c" => Command::EmitC,
                "emit-ir" => Command::EmitIR,
                "doc" => Command::Doc,
                "fmt" => Command::Fmt,
                "repl" => {
                    eprintln!("repl does not take a file argument");
                    usage();
                }
                "lsp" => {
                    eprintln!("lsp does not take a file argument");
                    usage();
                }
                other => {
                    eprintln!("Unknown command: {}", other);
                    usage();
                }
            };
            (cmd, Some(PathBuf::from(&args[2])))
        }
        _ => usage(),
    }
}

fn main() {
    let (command, input) = parse_args();

    if let Command::Repl = command {
        repl::run();
        return;
    }

    if let Command::Lsp = command {
        if let Err(e) = riina_lsp::server::run() {
            eprintln!("LSP error: {e}");
            process::exit(1);
        }
        return;
    }

    if let Command::Verify(mode) = command {
        process::exit(verify::run(mode));
    }

    let input = input.expect("file path required");
    let source = match fs::read_to_string(&input) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            process::exit(1);
        }
    };

    let filename = input.display().to_string();

    // 1. Parse program (top-level declarations) and desugar to expression
    let mut parser = Parser::new(&source);
    let expr = match parser.parse_program() {
        Ok(program) => program.desugar(),
        Err(e) => {
            eprintln!("{}", diagnostics::format_diagnostic(
                &source, &e.span, &e.to_string(), &filename
            ));
            process::exit(1);
        }
    };

    // 2. Typecheck (with builtin types registered)
    let ctx = riina_typechecker::register_builtin_types(&Context::new());
    let (ty, eff) = match type_check(&ctx, &expr) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {}", e);
            process::exit(1);
        }
    };

    // 3. Dispatch by command
    match command {
        Command::Check => {
            eprintln!("RIINA Compiler v0.1.0");
            eprintln!("Compiling: {:?}", input);
            eprintln!("Success!");
            println!("Type: {:?}", ty);
            println!("Effect: {:?}", eff);
        }
        Command::Run => {
            match riina_codegen::eval_with_builtins(&expr) {
                Ok(val) => println!("{:?}", val),
                Err(e) => {
                    eprintln!("Runtime Error: {}", e);
                    process::exit(1);
                }
            }
        }
        Command::EmitC => {
            match riina_codegen::compile_to_c(&expr) {
                Ok(c_code) => print!("{}", c_code),
                Err(e) => {
                    eprintln!("Codegen Error: {}", e);
                    process::exit(1);
                }
            }
        }
        Command::EmitIR => {
            match riina_codegen::compile(&expr) {
                Ok(program) => println!("{:#?}", program),
                Err(e) => {
                    eprintln!("Codegen Error: {}", e);
                    process::exit(1);
                }
            }
        }
        Command::Build => {
            let c_code = match riina_codegen::compile_to_c(&expr) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("Codegen Error: {}", e);
                    process::exit(1);
                }
            };

            let stem = input.file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("output");
            let output_name = input.parent()
                .unwrap_or_else(|| std::path::Path::new("."))
                .join(stem);

            let tmp_c = std::env::temp_dir().join(format!("riina_{}.c", stem));
            if let Err(e) = fs::write(&tmp_c, &c_code) {
                eprintln!("Error writing temp file: {}", e);
                process::exit(1);
            }

            let status = process::Command::new("cc")
                .args([
                    "-o", &output_name.to_string_lossy(),
                    &*tmp_c.to_string_lossy(),
                ])
                .status();

            // Clean up temp file
            let _ = fs::remove_file(&tmp_c);

            match status {
                Ok(s) if s.success() => {
                    eprintln!("Built: {}", output_name.display());
                }
                Ok(s) => {
                    eprintln!("C compiler exited with: {}", s);
                    process::exit(1);
                }
                Err(e) => {
                    eprintln!("Failed to invoke cc: {}", e);
                    process::exit(1);
                }
            }
        }
        Command::Fmt => {
            match riina_fmt::format_source(&source) {
                Ok(formatted) => print!("{formatted}"),
                Err(e) => {
                    eprintln!("Format error: {e}");
                    process::exit(1);
                }
            }
        }
        Command::Doc => {
            let title = input
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("RIINA");
            match riina_doc::generate_from_source(title, &source) {
                Ok(html) => print!("{html}"),
                Err(e) => {
                    eprintln!("Doc error: {e}");
                    process::exit(1);
                }
            }
        }
        Command::Repl => unreachable!("handled above"),
        Command::Lsp => unreachable!("handled above"),
        Command::Verify(_) => unreachable!("handled above"),
    }
}
