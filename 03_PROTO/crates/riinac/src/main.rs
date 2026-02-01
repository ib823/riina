// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

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
    Pkg(Vec<String>),
    ListCompliance,
}

/// Report output format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum ReportFormat {
    #[default]
    Text,
    Json,
}

/// Parsed CLI options (beyond command + file).
#[derive(Debug, Default)]
struct Options {
    compliance: Vec<riina_compliance::ComplianceProfile>,
    report: Option<ReportFormat>,
    report_output: Option<PathBuf>,
    target: Option<riina_codegen::Target>,
}

fn usage() -> ! {
    eprintln!("Usage: riinac [command] [options] <file.rii>");
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
    eprintln!("  pkg      Package manager (init/add/remove/lock/build/...)");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --compliance <profiles>  Run compliance checks (comma-separated)");
    eprintln!("  --report                 Generate compliance report (text)");
    eprintln!("  --report-json            Generate compliance report (JSON)");
    eprintln!("  --report-output <file>   Write report to file instead of stdout");
    eprintln!("  --list-compliance        List available compliance profiles");
    eprintln!("  --target <target>        Compilation target (native, wasm32, wasm64, android-arm64, ios-arm64)");
    process::exit(1);
}

fn parse_args() -> (Command, Option<PathBuf>, Options) {
    let args: Vec<String> = std::env::args().collect();

    // Handle pkg early — it takes subcommands, not a file
    if args.len() >= 2 && args[1] == "pkg" {
        return (Command::Pkg(args[2..].to_vec()), None, Options::default());
    }

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
        return (Command::Verify(mode), None, Options::default());
    }

    if args.len() < 2 {
        usage();
    }

    // Parse command
    let (cmd, rest) = match args[1].as_str() {
        "check" => (Command::Check, &args[2..]),
        "run" => (Command::Run, &args[2..]),
        "build" => (Command::Build, &args[2..]),
        "emit-c" => (Command::EmitC, &args[2..]),
        "emit-ir" => (Command::EmitIR, &args[2..]),
        "doc" => (Command::Doc, &args[2..]),
        "fmt" => (Command::Fmt, &args[2..]),
        "repl" => return (Command::Repl, None, Options::default()),
        "lsp" => return (Command::Lsp, None, Options::default()),
        _ => {
            // No command given — default to Check, treat arg[1] as file
            (Command::Check, &args[1..])
        }
    };

    // Parse options and file from remaining args
    let mut opts = Options::default();
    let mut file: Option<PathBuf> = None;
    let mut i = 0;
    let rest_slice: Vec<&str> = rest.iter().map(|s| s.as_str()).collect();

    while i < rest_slice.len() {
        match rest_slice[i] {
            "--list-compliance" => {
                return (Command::ListCompliance, None, Options::default());
            }
            "--compliance" => {
                i += 1;
                if i >= rest_slice.len() {
                    eprintln!("--compliance requires a comma-separated list of profiles");
                    usage();
                }
                match riina_compliance::parse_profiles(rest_slice[i]) {
                    Ok(profiles) => opts.compliance = profiles,
                    Err(e) => {
                        eprintln!("{e}");
                        eprintln!("Use --list-compliance to see available profiles");
                        process::exit(1);
                    }
                }
            }
            "--report" => {
                opts.report = Some(ReportFormat::Text);
            }
            "--report-json" => {
                opts.report = Some(ReportFormat::Json);
            }
            "--report-output" => {
                i += 1;
                if i >= rest_slice.len() {
                    eprintln!("--report-output requires a file path");
                    usage();
                }
                opts.report_output = Some(PathBuf::from(rest_slice[i]));
            }
            "--target" => {
                i += 1;
                if i >= rest_slice.len() {
                    eprintln!("--target requires a target name (native, wasm32, wasm64, android-arm64, ios-arm64)");
                    usage();
                }
                match riina_codegen::Target::from_str(rest_slice[i]) {
                    Some(t) => opts.target = Some(t),
                    None => {
                        eprintln!("Unknown target: {}", rest_slice[i]);
                        eprintln!("Available targets: native, wasm32, wasm64, android-arm64, ios-arm64");
                        process::exit(1);
                    }
                }
            }
            arg if arg.starts_with('-') => {
                eprintln!("Unknown option: {arg}");
                usage();
            }
            path => {
                file = Some(PathBuf::from(path));
            }
        }
        i += 1;
    }

    (cmd, file, opts)
}

fn main() {
    let (command, input, opts) = parse_args();

    if let Command::ListCompliance = command {
        eprintln!("Available compliance profiles:");
        eprintln!();
        for p in riina_compliance::ComplianceProfile::ALL {
            eprintln!("  {:<14} {}", p.slug(), p.description());
        }
        return;
    }

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

    if let Command::Pkg(ref pkg_args) = command {
        if let Err(e) = riina_pkg::cli::run(pkg_args) {
            eprintln!("pkg error: {e}");
            process::exit(1);
        }
        return;
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

    // 3. Compliance validation (if profiles selected)
    if !opts.compliance.is_empty() {
        let violations = riina_compliance::validate(&expr, &opts.compliance);

        // Generate report if requested
        if let Some(fmt) = opts.report {
            let report = riina_compliance::report::generate(
                &filename,
                &source,
                &opts.compliance,
                &violations,
            );
            let report_text = match fmt {
                ReportFormat::Text => report.to_text(),
                ReportFormat::Json => report.to_json(),
            };
            if let Some(ref path) = opts.report_output {
                if let Err(e) = fs::write(path, &report_text) {
                    eprintln!("Error writing report: {e}");
                    process::exit(1);
                }
                eprintln!("Compliance report written to: {}", path.display());
            } else {
                println!("{report_text}");
            }
            if riina_compliance::has_errors(&violations) {
                process::exit(1);
            }
        } else if !violations.is_empty() {
            for v in &violations {
                eprintln!("{v}");
            }
            if riina_compliance::has_errors(&violations) {
                eprintln!();
                eprintln!("Compliance check failed with errors");
                process::exit(1);
            }
        }
    }

    // 4. Dispatch by command
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
            let target = opts.target.unwrap_or(riina_codegen::Target::Native);
            match riina_codegen::compile(&expr) {
                Ok(program) => {
                    let backend = riina_codegen::backend_for_target(target);
                    match backend.emit(&program) {
                        Ok(output) => {
                            // Write primary output to stdout
                            use std::io::Write;
                            std::io::stdout().write_all(&output.primary).unwrap();
                        }
                        Err(e) => {
                            eprintln!("Codegen Error: {}", e);
                            process::exit(1);
                        }
                    }
                }
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
            let target = opts.target.unwrap_or(riina_codegen::Target::Native);

            let program = match riina_codegen::compile(&expr) {
                Ok(p) => p,
                Err(e) => {
                    eprintln!("Codegen Error: {}", e);
                    process::exit(1);
                }
            };

            let backend = riina_codegen::backend_for_target(target);
            let output = match backend.emit(&program) {
                Ok(o) => o,
                Err(e) => {
                    eprintln!("Codegen Error: {}", e);
                    process::exit(1);
                }
            };

            let stem = input.file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("output");
            let output_dir = input.parent()
                .unwrap_or_else(|| std::path::Path::new("."));

            if target == riina_codegen::Target::Native {
                // Native: write C, compile with cc
                let output_name = output_dir.join(stem);
                let tmp_c = std::env::temp_dir().join(format!("riina_{}.c", stem));
                if let Err(e) = fs::write(&tmp_c, &output.primary) {
                    eprintln!("Error writing temp file: {}", e);
                    process::exit(1);
                }

                let status = process::Command::new("cc")
                    .args([
                        "-o", &output_name.to_string_lossy(),
                        &*tmp_c.to_string_lossy(),
                    ])
                    .status();

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
            } else {
                // Non-native: write primary output + auxiliary files
                let primary_name = output_dir.join(format!("{}{}", stem, output.extension));
                if let Err(e) = fs::write(&primary_name, &output.primary) {
                    eprintln!("Error writing output: {}", e);
                    process::exit(1);
                }
                eprintln!("Wrote: {}", primary_name.display());

                for aux in &output.auxiliary {
                    let aux_path = output_dir.join(&aux.name);
                    if let Err(e) = fs::write(&aux_path, &aux.content) {
                        eprintln!("Error writing auxiliary file: {}", e);
                        process::exit(1);
                    }
                    eprintln!("Wrote: {}", aux_path.display());
                }

                eprintln!("Built for target: {}", target);
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
        Command::Pkg(_) => unreachable!("handled above"),
        Command::ListCompliance => unreachable!("handled above"),
    }
}
