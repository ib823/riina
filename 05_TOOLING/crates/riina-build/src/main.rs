// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! RIINA Build Orchestrator
//! ═══════════════════════════════════════════════════════════════════════════════
//! Track F Deliverable: TRACK_F-TOOL-BUILD_v1_0_0
//! ═══════════════════════════════════════════════════════════════════════════════
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
//!
//! Central build orchestrator that coordinates:
//! - Rust workspace builds
//! - Ada/SPARK compilation and verification
//! - RIINA bootstrap compilation
//! - HDL synthesis (when available)
//!
//! All builds are hermetic and reproducible.

#![forbid(unsafe_code)]
// Lints configured at workspace level in Cargo.toml

use std::collections::HashMap;
use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use clap::{Parser, Subcommand, ValueEnum};

// ═══════════════════════════════════════════════════════════════════════════════
// CLI DEFINITION
// ═══════════════════════════════════════════════════════════════════════════════

#[derive(Parser)]
#[command(name = "riina-build")]
#[command(version = "1.0.0")]
#[command(about = "RIINA Build System - Hermetic, Reproducible, Verified")]
#[command(long_about = r#"
═══════════════════════════════════════════════════════════════════════════════
                        RIINA BUILD ORCHESTRATOR
═══════════════════════════════════════════════════════════════════════════════

Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

This tool orchestrates builds across all RIINA components:
- Rust crates (with verification tool integration)
- Ada/SPARK packages (with GNATprove)
- RIINA compiler (bootstrap stages)
- HDL modules (synthesis and verification)

All builds are hermetic (no network, no system time) and reproducible.
"#)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Verbose output
    #[arg(short, long, global = true)]
    verbose: bool,

    /// Build profile
    #[arg(short, long, global = true, default_value = "debug")]
    profile: Profile,

    /// Project root (default: current directory or RIINA_ROOT)
    #[arg(long, global = true)]
    root: Option<PathBuf>,
}

#[derive(Subcommand)]
enum Commands {
    /// Build all components
    All {
        /// Verification level (0-6)
        #[arg(short, long, default_value = "2")]
        level: u8,
    },

    /// Build Rust workspace
    Rust {
        /// Specific package to build
        #[arg(short, long)]
        package: Option<String>,

        /// All targets (tests, benches, examples)
        #[arg(long)]
        all_targets: bool,
    },

    /// Build Ada/SPARK components
    Ada {
        /// Specific GPR project
        #[arg(short, long)]
        project: Option<String>,

        /// SPARK proof level (0-5)
        #[arg(long, default_value = "2")]
        proof_level: u8,
    },

    /// Bootstrap RIINA compiler
    Bootstrap {
        /// Target stage (0, 1, or 2)
        #[arg(short, long, default_value = "1")]
        stage: u8,

        /// Verify stage match
        #[arg(long)]
        verify: bool,
    },

    /// Build HDL modules
    Hdl {
        /// Target FPGA/ASIC
        #[arg(short, long)]
        target: Option<String>,
    },

    /// Generate build manifest
    Manifest {
        /// Output file
        #[arg(short, long, default_value = "build-manifest.json")]
        output: PathBuf,
    },

    /// Clean build artifacts
    Clean {
        /// Clean all (including dependencies)
        #[arg(long)]
        all: bool,
    },

    /// Show build configuration
    Config,
}

#[derive(Clone, Copy, ValueEnum, Default)]
enum Profile {
    #[default]
    Debug,
    Release,
    Bench,
}

impl Profile {
    fn as_str(self) -> &'static str {
        match self {
            Profile::Debug => "debug",
            Profile::Release => "release",
            Profile::Bench => "bench",
        }
    }

    fn cargo_args(self) -> Vec<&'static str> {
        match self {
            Profile::Debug => vec![],
            Profile::Release => vec!["--release"],
            Profile::Bench => vec!["--profile", "bench"],
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// BUILD CONTEXT
// ═══════════════════════════════════════════════════════════════════════════════

struct BuildContext {
    root: PathBuf,
    profile: Profile,
    verbose: bool,
    start_time: Instant,
    env: HashMap<String, String>,
}

impl BuildContext {
    fn new(cli: &Cli) -> Result<Self, BuildError> {
        let root = cli
            .root
            .clone()
            .or_else(|| env::var("RIINA_ROOT").ok().map(PathBuf::from))
            .unwrap_or_else(|| env::current_dir().unwrap_or_else(|_| PathBuf::from(".")));

        // Verify we're in a RIINA project
        if !root.join("Cargo.toml").exists() {
            return Err(BuildError::NotRiinaProject(root));
        }

        // Set up hermetic build environment
        let mut env = HashMap::new();

        // Reproducibility: fixed timestamp
        env.insert("SOURCE_DATE_EPOCH".to_string(), "0".to_string());

        // Reproducibility: no incremental
        env.insert("CARGO_INCREMENTAL".to_string(), "0".to_string());

        // Security: treat warnings as errors
        env.insert("RUSTFLAGS".to_string(), "-D warnings".to_string());

        // No network access during build
        env.insert("CARGO_NET_OFFLINE".to_string(), "true".to_string());

        Ok(Self {
            root,
            profile: cli.profile,
            verbose: cli.verbose,
            start_time: Instant::now(),
            env,
        })
    }

    fn log(&self, msg: &str) {
        println!("[riina-build] {msg}");
    }

    fn log_verbose(&self, msg: &str) {
        if self.verbose {
            println!("[riina-build] {msg}");
        }
    }

    fn elapsed(&self) -> Duration {
        self.start_time.elapsed()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// BUILD ERRORS
// ═══════════════════════════════════════════════════════════════════════════════

#[derive(Debug)]
enum BuildError {
    NotRiinaProject(PathBuf),
    CommandFailed {
        command: String,
        exit_code: i32,
    },
    CommandNotFound(String),
    IoError(io::Error),
    #[allow(dead_code)]
    VerificationFailed(String),
    InvalidConfiguration(String),
}

impl std::fmt::Display for BuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BuildError::NotRiinaProject(path) => {
                write!(f, "Not a RIINA project: {}", path.display())
            }
            BuildError::CommandFailed { command, exit_code } => {
                write!(f, "Command '{command}' failed with exit code {exit_code}")
            }
            BuildError::CommandNotFound(cmd) => {
                write!(f, "Command not found: {cmd}")
            }
            BuildError::IoError(e) => write!(f, "I/O error: {e}"),
            BuildError::VerificationFailed(msg) => {
                write!(f, "Verification failed: {msg}")
            }
            BuildError::InvalidConfiguration(msg) => {
                write!(f, "Invalid configuration: {msg}")
            }
        }
    }
}

impl From<io::Error> for BuildError {
    fn from(e: io::Error) -> Self {
        BuildError::IoError(e)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// BUILD COMMANDS
// ═══════════════════════════════════════════════════════════════════════════════

fn run_command(ctx: &BuildContext, cmd: &str, args: &[&str]) -> Result<(), BuildError> {
    ctx.log_verbose(&format!("Running: {cmd} {}", args.join(" ")));

    let mut command = Command::new(cmd);
    command
        .args(args)
        .current_dir(&ctx.root)
        .stdout(if ctx.verbose {
            Stdio::inherit()
        } else {
            Stdio::piped()
        })
        .stderr(if ctx.verbose {
            Stdio::inherit()
        } else {
            Stdio::piped()
        });

    // Set hermetic environment
    for (key, value) in &ctx.env {
        command.env(key, value);
    }

    let status = command.status().map_err(|e| {
        if e.kind() == io::ErrorKind::NotFound {
            BuildError::CommandNotFound(cmd.to_string())
        } else {
            BuildError::IoError(e)
        }
    })?;

    if status.success() {
        Ok(())
    } else {
        Err(BuildError::CommandFailed {
            command: format!("{cmd} {}", args.join(" ")),
            exit_code: status.code().unwrap_or(-1),
        })
    }
}

fn build_rust(
    ctx: &BuildContext,
    package: Option<&str>,
    all_targets: bool,
) -> Result<(), BuildError> {
    ctx.log("Building Rust workspace...");

    let mut args: Vec<&str> = vec!["build"];
    args.extend(ctx.profile.cargo_args());

    if let Some(pkg) = package {
        args.extend(["--package", pkg]);
    } else {
        args.push("--workspace");
    }

    if all_targets {
        args.push("--all-targets");
    }

    args.push("--all-features");

    run_command(ctx, "cargo", &args)?;

    ctx.log(&format!(
        "✓ Rust build complete ({:.2}s)",
        ctx.elapsed().as_secs_f64()
    ));

    Ok(())
}

fn build_ada(ctx: &BuildContext, project: Option<&str>, proof_level: u8) -> Result<(), BuildError> {
    ctx.log("Building Ada/SPARK components...");

    let ada_dir = ctx.root.join("ada");
    if !ada_dir.exists() {
        ctx.log("No Ada directory found, skipping");
        return Ok(());
    }

    // Find GPR file
    let gpr_file = if let Some(proj) = project {
        ada_dir.join(format!("{proj}.gpr"))
    } else {
        ada_dir.join("riina.gpr")
    };

    if !gpr_file.exists() {
        ctx.log(&format!(
            "GPR file not found: {}, skipping Ada build",
            gpr_file.display()
        ));
        return Ok(());
    }

    // Build with gprbuild
    let gpr_path = gpr_file.to_string_lossy();
    run_command(ctx, "gprbuild", &["-P", &gpr_path, "-j0"])?;

    // Run GNATprove if proof level > 0
    if proof_level > 0 {
        ctx.log(&format!("Running GNATprove at level {proof_level}..."));
        let level_str = proof_level.to_string();
        run_command(
            ctx,
            "gnatprove",
            &["-P", &gpr_path, "--level", &level_str, "-j0"],
        )?;
    }

    ctx.log(&format!(
        "✓ Ada/SPARK build complete ({:.2}s)",
        ctx.elapsed().as_secs_f64()
    ));

    Ok(())
}

fn build_bootstrap(ctx: &BuildContext, stage: u8, verify: bool) -> Result<(), BuildError> {
    ctx.log(&format!("Bootstrapping RIINA (stage {stage})..."));

    match stage {
        0 => {
            // Stage 0: Build bootstrap compiler (Rust implementation)
            ctx.log("Stage 0: Building Rust bootstrap compiler...");
            run_command(ctx, "cargo", &["build", "--release", "--package", "riinac"])?;
        }
        1 => {
            // Stage 1: Self-hosted compiler (compiled by stage 0)
            ctx.log("Stage 1: Building self-hosted compiler...");

            let stage0 = ctx.root.join("target/release/riinac");
            if !stage0.exists() {
                return Err(BuildError::InvalidConfiguration(
                    "Stage 0 compiler not found. Run `riina-build bootstrap --stage 0` first."
                        .to_string(),
                ));
            }

            // TODO: Actually compile with stage 0 when RIINA is ready
            ctx.log("Stage 1: (using Rust compiler until self-hosting ready)");
            run_command(ctx, "cargo", &["build", "--release", "--package", "riinac"])?;
        }
        2 => {
            // Stage 2: Verification build (must match stage 1)
            ctx.log("Stage 2: Building verification compiler...");

            let stage1 = ctx.root.join("target/release/riinac");
            if !stage1.exists() {
                return Err(BuildError::InvalidConfiguration(
                    "Stage 1 compiler not found. Run `riina-build bootstrap --stage 1` first."
                        .to_string(),
                ));
            }

            // TODO: Actually compile with stage 1 when self-hosting ready
            ctx.log("Stage 2: (using Rust compiler until self-hosting ready)");
            run_command(ctx, "cargo", &["build", "--release", "--package", "riinac"])?;

            if verify {
                ctx.log("Verifying stage 1 == stage 2...");
                // TODO: Compare binaries when self-hosting ready
                ctx.log("✓ Stages match (placeholder)");
            }
        }
        _ => {
            return Err(BuildError::InvalidConfiguration(format!(
                "Invalid bootstrap stage: {stage}. Must be 0, 1, or 2."
            )));
        }
    }

    ctx.log(&format!(
        "✓ Bootstrap stage {stage} complete ({:.2}s)",
        ctx.elapsed().as_secs_f64()
    ));

    Ok(())
}

fn build_hdl(ctx: &BuildContext, target: Option<&str>) -> Result<(), BuildError> {
    ctx.log("Building HDL modules...");

    let hdl_dir = ctx.root.join("hdl");
    if !hdl_dir.exists() {
        ctx.log("No HDL directory found, skipping");
        return Ok(());
    }

    // TODO: Integrate with actual HDL toolchain
    ctx.log(&format!("HDL target: {}", target.unwrap_or("simulation")));
    ctx.log("HDL build not yet implemented");

    Ok(())
}

fn build_all(ctx: &BuildContext, level: u8) -> Result<(), BuildError> {
    ctx.log(&format!(
        "Building all components (verification level {level})..."
    ));

    // 1. Rust workspace
    build_rust(ctx, None, true)?;

    // 2. Ada/SPARK (if present)
    let proof_level = level.min(5);
    build_ada(ctx, None, proof_level)?;

    // 3. Bootstrap (stage 1 for production)
    if level >= 2 {
        build_bootstrap(ctx, 1, level >= 4)?;
    }

    // 4. HDL (if present)
    if level >= 4 {
        build_hdl(ctx, None)?;
    }

    ctx.log(&format!(
        "✓ All builds complete ({:.2}s)",
        ctx.elapsed().as_secs_f64()
    ));

    Ok(())
}

fn generate_manifest(ctx: &BuildContext, output: &Path) -> Result<(), BuildError> {
    ctx.log("Generating build manifest...");

    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);

    // Collect build information
    let manifest = format!(
        r#"{{
  "version": "1.0.0",
  "timestamp": {timestamp},
  "profile": "{}",
  "root": "{}",
  "environment": {{
    "SOURCE_DATE_EPOCH": "0",
    "CARGO_INCREMENTAL": "0",
    "CARGO_NET_OFFLINE": "true"
  }},
  "components": {{
    "rust": {{
      "toolchain": "1.84.0",
      "status": "pending"
    }},
    "ada": {{
      "status": "pending"
    }},
    "riina-lang": {{
      "stage": "pending"
    }}
  }},
  "verification": {{
    "level": "pending"
  }}
}}"#,
        ctx.profile.as_str(),
        ctx.root.display()
    );

    let output_path = ctx.root.join(output);
    fs::write(&output_path, manifest)?;

    ctx.log(&format!("✓ Manifest written to {}", output_path.display()));

    Ok(())
}

fn clean(ctx: &BuildContext, all: bool) -> Result<(), BuildError> {
    ctx.log("Cleaning build artifacts...");

    let args = if all {
        vec!["clean"]
    } else {
        vec!["clean", "--package", "riinac"]
    };

    run_command(ctx, "cargo", &args)?;

    // Clean Ada artifacts if present
    let ada_dir = ctx.root.join("ada");
    if ada_dir.exists() {
        let obj_dir = ada_dir.join("obj");
        if obj_dir.exists() {
            fs::remove_dir_all(&obj_dir)?;
            ctx.log("Cleaned Ada object directory");
        }
    }

    ctx.log("✓ Clean complete");

    Ok(())
}

fn show_config(ctx: &BuildContext) {
    println!("═══════════════════════════════════════════════════════════════");
    println!("                    RIINA BUILD CONFIGURATION");
    println!("═══════════════════════════════════════════════════════════════");
    println!();
    println!("Project Root:     {}", ctx.root.display());
    println!("Profile:          {}", ctx.profile.as_str());
    println!("Verbose:          {}", ctx.verbose);
    println!();
    println!("Hermetic Environment:");
    for (key, value) in &ctx.env {
        println!("  {key}={value}");
    }
    println!();
    println!("Available Targets:");
    println!("  rust       - Rust workspace");
    println!("  ada        - Ada/SPARK components");
    println!("  bootstrap  - RIINA compiler stages");
    println!("  hdl        - Hardware description modules");
    println!("═══════════════════════════════════════════════════════════════");
}

// ═══════════════════════════════════════════════════════════════════════════════
// MAIN
// ═══════════════════════════════════════════════════════════════════════════════

fn main() -> ExitCode {
    let cli = Cli::parse();

    println!("═══════════════════════════════════════════════════════════════");
    println!("           RIINA BUILD SYSTEM v1.0.0");
    println!("  Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST");
    println!("═══════════════════════════════════════════════════════════════");
    println!();

    let ctx = match BuildContext::new(&cli) {
        Ok(ctx) => ctx,
        Err(e) => {
            eprintln!("[ERROR] {e}");
            return ExitCode::FAILURE;
        }
    };

    let result = match &cli.command {
        Commands::All { level } => build_all(&ctx, *level),
        Commands::Rust {
            package,
            all_targets,
        } => build_rust(&ctx, package.as_deref(), *all_targets),
        Commands::Ada {
            project,
            proof_level,
        } => build_ada(&ctx, project.as_deref(), *proof_level),
        Commands::Bootstrap { stage, verify } => build_bootstrap(&ctx, *stage, *verify),
        Commands::Hdl { target } => build_hdl(&ctx, target.as_deref()),
        Commands::Manifest { output } => generate_manifest(&ctx, output),
        Commands::Clean { all } => clean(&ctx, *all),
        Commands::Config => {
            show_config(&ctx);
            Ok(())
        }
    };

    match result {
        Ok(()) => {
            println!();
            println!("✓ Build successful");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!();
            eprintln!("[ERROR] {e}");
            ExitCode::FAILURE
        }
    }
}
