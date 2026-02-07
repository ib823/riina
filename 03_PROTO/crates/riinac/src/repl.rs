// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! RIINA REPL — Interactive Read-Eval-Print Loop
//!
//! Supports bilingual commands (Bahasa Melayu + English).
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom

use std::io::{self, Write, BufRead};

use riina_parser::Parser;
use riina_typechecker::{type_check, Context};

/// Run the REPL.
pub fn run() {
    eprintln!("RIINA REPL v0.1.0");
    eprintln!("Taip ':bantuan' untuk bantuan. / Type ':help' for help.");
    eprintln!();

    let stdin = io::stdin();
    let mut stdout = io::stdout();

    loop {
        print!(">>> ");
        if stdout.flush().is_err() {
            break;
        }

        let mut line = String::new();
        match stdin.lock().read_line(&mut line) {
            Ok(0) => break, // EOF
            Err(_) => break,
            Ok(_) => {}
        }

        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        // Handle special commands
        if trimmed.starts_with(':') {
            if handle_command(trimmed) {
                break;
            }
            continue;
        }

        // Parse, typecheck, and evaluate
        eval_line(trimmed);
    }
}

/// Handle a REPL command. Returns true if the REPL should exit.
fn handle_command(cmd: &str) -> bool {
    let parts: Vec<&str> = cmd.splitn(2, ' ').collect();
    let command = parts[0];
    let arg = parts.get(1).copied().unwrap_or("");

    match command {
        ":keluar" | ":quit" | ":q" => {
            eprintln!("Selamat tinggal! / Goodbye!");
            return true;
        }
        ":bantuan" | ":help" | ":h" => {
            eprintln!("Arahan / Commands:");
            eprintln!("  :bantuan / :help     Tunjuk bantuan / Show help");
            eprintln!("  :jenis  / :type <e>  Tunjuk jenis / Show type");
            eprintln!("  :kesan  / :effect <e> Tunjuk kesan / Show effect");
            eprintln!("  :ir <e>              Tunjuk IR / Show IR");
            eprintln!("  :c <e>               Tunjuk kod C / Show C code");
            eprintln!("  :set semula / :reset  Set semula / Reset");
            eprintln!("  :keluar / :quit       Keluar / Quit");
        }
        ":jenis" | ":type" | ":t" => {
            if arg.is_empty() {
                eprintln!("Penggunaan / Usage: :jenis <ungkapan> / :type <expr>");
            } else {
                show_type(arg);
            }
        }
        ":kesan" | ":effect" => {
            if arg.is_empty() {
                eprintln!("Penggunaan / Usage: :kesan <ungkapan> / :effect <expr>");
            } else {
                show_type(arg); // type and effect shown together
            }
        }
        ":ir" => {
            if arg.is_empty() {
                eprintln!("Penggunaan / Usage: :ir <ungkapan> / :ir <expr>");
            } else {
                show_ir(arg);
            }
        }
        ":c" => {
            if arg.is_empty() {
                eprintln!("Penggunaan / Usage: :c <ungkapan> / :c <expr>");
            } else {
                show_c(arg);
            }
        }
        ":set" if arg == "semula" => {
            eprintln!("Persekitaran ditetapkan semula. / Environment reset.");
        }
        ":reset" => {
            eprintln!("Persekitaran ditetapkan semula. / Environment reset.");
        }
        _ => {
            eprintln!("Arahan tidak dikenali / Unknown command: {}", command);
            eprintln!("Taip ':bantuan' / Type ':help' for commands.");
        }
    }
    false
}

fn eval_line(input: &str) {
    let mut parser = Parser::new(input);
    let expr = match parser.parse_expr() {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Ralat sintaks / Parse error: {:?}", e);
            return;
        }
    };

    let ctx = riina_typechecker::register_builtin_types(&Context::new());
    let (ty, eff) = match type_check(&ctx, &expr) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Ralat jenis / Type error: {}", e);
            return;
        }
    };

    match riina_codegen::eval_with_builtins(&expr) {
        Ok(val) => {
            println!("{:?} : {:?} [{:?}]", val, ty, eff);
        }
        Err(e) => {
            eprintln!("Ralat masa larian / Runtime error: {}", e);
        }
    }
}

fn show_type(input: &str) {
    let mut parser = Parser::new(input);
    let expr = match parser.parse_expr() {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Ralat sintaks / Parse error: {:?}", e);
            return;
        }
    };

    let ctx = riina_typechecker::register_builtin_types(&Context::new());
    match type_check(&ctx, &expr) {
        Ok((ty, eff)) => println!("{:?} [{:?}]", ty, eff),
        Err(e) => eprintln!("Ralat jenis / Type error: {}", e),
    }
}

fn show_ir(input: &str) {
    let mut parser = Parser::new(input);
    let expr = match parser.parse_expr() {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Ralat sintaks / Parse error: {:?}", e);
            return;
        }
    };

    match riina_codegen::compile(&expr) {
        Ok(program) => println!("{:#?}", program),
        Err(e) => eprintln!("Ralat codegen / Codegen error: {}", e),
    }
}

fn show_c(input: &str) {
    let mut parser = Parser::new(input);
    let expr = match parser.parse_expr() {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Ralat sintaks / Parse error: {:?}", e);
            return;
        }
    };

    match riina_codegen::compile_to_c(&expr) {
        Ok(c_code) => print!("{}", c_code),
        Err(e) => eprintln!("Ralat codegen / Codegen error: {}", e),
    }
}
