//! RIINA Compiler Driver
//!
//! Main entry point for the RIINA compiler.
//! RIINA = Rigorous Immutable Integrity No-attack Assured
//! Named for: Reena + Isaac + Imaan
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::fs;
use riina_parser::Parser;
use riina_typechecker::{type_check, Context};

struct Cli {
    /// Input file
    input: PathBuf,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: riinac <input.rii>");
        std::process::exit(1);
    }
    let cli = Cli { input: PathBuf::from(&args[1]) };

    eprintln!("RIINA Compiler v0.1.0");
    eprintln!("Compiling: {:?}", cli.input);

    let source = match fs::read_to_string(&cli.input) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            std::process::exit(1);
        }
    };

    // 1. Parse
    let mut parser = Parser::new(&source);
    let expr = match parser.parse_expr() {
        Ok(e) => e,
        Err(e) => {
            eprintln!("Parse Error: {:?}", e);
            std::process::exit(1);
        }
    };

    // 2. Typecheck
    let ctx = Context::new();
    let (ty, eff) = match type_check(&ctx, &expr) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("Type Error: {}", e);
            std::process::exit(1);
        }
    };

    eprintln!("Success!");
    println!("Type: {:?}", ty);
    println!("Effect: {:?}", eff);
}
