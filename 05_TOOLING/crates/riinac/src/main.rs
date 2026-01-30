//! RIINA Compiler
use clap::Parser;

#[derive(Parser)]
#[command(name = "riinac")]
#[command(about = "RIINA Compiler")]
struct Cli {
    /// Input file
    input: Option<String>,
}

fn main() {
    let _cli = Cli::parse();
    println!("RIINA Compiler v0.1.0");
    println!("Not yet implemented - Track B will provide implementation");
}
