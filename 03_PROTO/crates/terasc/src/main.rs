//! TERAS-LANG Compiler Driver
//!
//! Main entry point for the TERAS-LANG compiler.
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

#![forbid(unsafe_code)]

use clap::Parser as ClapParser;
use std::path::PathBuf;
use std::fs;
use teras_lang_parser::Parser;
use teras_lang_typechecker::{type_check, Context};

#[derive(ClapParser)]
#[command(name = "terasc")]
#[command(about = "TERAS-LANG Compiler", long_about = None)]
struct Cli {
    /// Input file
    input: PathBuf,
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    eprintln!("TERAS-LANG Compiler v0.1.0");
    eprintln!("Compiling: {:?}", cli.input);

    let source = fs::read_to_string(&cli.input)?;
    
    // 1. Parse
    let mut parser = Parser::new(&source);
    let expr = parser.parse_expr().map_err(|e| anyhow::anyhow!("Parse Error: {:?}", e))?;
    
    // 2. Typecheck
    let ctx = Context::new();
    let (ty, eff) = type_check(&ctx, &expr).map_err(|e| anyhow::anyhow!("Type Error: {}", e))?;

    eprintln!("Success!");
    println!("Type: {:?}", ty);
    println!("Effect: {:?}", eff);
    
    Ok(())
}
