//! TERAS-LANG Compiler
use clap::Parser;

#[derive(Parser)]
#[command(name = "terasc")]
#[command(about = "TERAS-LANG Compiler")]
struct Cli {
    /// Input file
    input: Option<String>,
}

fn main() {
    let _cli = Cli::parse();
    println!("TERAS-LANG Compiler v0.1.0");
    println!("Not yet implemented - Track B will provide implementation");
}
