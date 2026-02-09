// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! RIINA Hash Chain Tool
//!
//! Maintains cryptographic integrity chain for all RIINA documents.
//! This tool is critical for inter-track coordination and document
//! integrity verification.
//!
//! # Usage
//!
//! ```bash
//! # Initialize a new hash chain
//! riina-hash-chain init --chain-name riina-main
//!
//! # Add a document to the chain
//! riina-hash-chain add --file TRACK_F-TOOL-BUILD_v1_0_0.md
//!
//! # Verify chain integrity
//! riina-hash-chain verify --deep
//!
//! # Show chain status
//! riina-hash-chain show --format json
//! ```

use clap::{Parser, Subcommand};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;

/// RIINA Hash Chain Tool - Document integrity management
#[derive(Parser)]
#[command(name = "riina-hash-chain")]
#[command(version = "1.0.0")]
#[command(about = "RIINA document hash chain management")]
#[command(author = "RIINA Team <security@riina.my>")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Initialize a new hash chain
    Init {
        /// Name of the hash chain
        #[arg(long)]
        chain_name: String,

        /// Output file path
        #[arg(long, default_value = "riina-hash-chain.json")]
        output: PathBuf,
    },

    /// Add a document to the chain
    Add {
        /// Path to the document file
        #[arg(long)]
        file: PathBuf,

        /// Hash of the predecessor document (optional)
        #[arg(long)]
        predecessor: Option<String>,

        /// Author/track name
        #[arg(long, default_value = "Unknown")]
        author: String,

        /// Hash chain file
        #[arg(long, default_value = "riina-hash-chain.json")]
        chain: PathBuf,
    },

    /// Verify chain integrity
    Verify {
        /// Perform deep verification (check file hashes)
        #[arg(long)]
        deep: bool,

        /// Base directory for document files
        #[arg(long)]
        base_dir: Option<PathBuf>,

        /// Hash chain file
        #[arg(long, default_value = "riina-hash-chain.json")]
        chain: PathBuf,
    },

    /// Show chain status
    Show {
        /// Output format (text, json)
        #[arg(long, default_value = "text")]
        format: String,

        /// Hash chain file
        #[arg(long, default_value = "riina-hash-chain.json")]
        chain: PathBuf,
    },

    /// Export chain to file
    Export {
        /// Output file path
        #[arg(long)]
        output: PathBuf,

        /// Hash chain file
        #[arg(long, default_value = "riina-hash-chain.json")]
        chain: PathBuf,
    },

    /// Import chain from file
    Import {
        /// Input file path
        #[arg(long)]
        input: PathBuf,

        /// Output hash chain file
        #[arg(long, default_value = "riina-hash-chain.json")]
        output: PathBuf,
    },

    /// Compute hash of a file
    Hash {
        /// Path to the file
        #[arg(long)]
        file: PathBuf,
    },
}

/// A single entry in the hash chain
#[derive(Serialize, Deserialize, Clone, Debug)]
struct ChainEntry {
    /// Document identifier (filename)
    document_id: String,

    /// SHA-256 hash of the document
    sha256: String,

    /// Hash of the predecessor document
    predecessor: Option<String>,

    /// ISO 8601 timestamp
    timestamp: String,

    /// Author or track name
    author: String,

    /// Optional cryptographic signature
    signature: Option<String>,
}

/// The complete hash chain
#[derive(Serialize, Deserialize, Debug)]
struct HashChain {
    /// Name of this hash chain
    name: String,

    /// Version of the chain format
    version: String,

    /// Creation timestamp
    created: String,

    /// Last modification timestamp
    modified: String,

    /// Chain entries
    entries: Vec<ChainEntry>,
}

impl HashChain {
    /// Create a new hash chain
    fn new(name: String) -> Self {
        let now = chrono::Utc::now().to_rfc3339();
        Self {
            name,
            version: "1.0.0".to_string(),
            created: now.clone(),
            modified: now,
            entries: Vec::new(),
        }
    }

    /// Add an entry to the chain
    fn add_entry(&mut self, entry: ChainEntry) {
        self.entries.push(entry);
        self.modified = chrono::Utc::now().to_rfc3339();
    }

    /// Get the latest entry's hash
    fn latest_hash(&self) -> Option<String> {
        self.entries.last().map(|e| e.sha256.clone())
    }

    /// Verify chain integrity
    fn verify(&self, deep: bool, base_dir: Option<&PathBuf>) -> VerificationResult {
        let mut result = VerificationResult::default();

        // Check predecessor chain
        for (i, entry) in self.entries.iter().enumerate() {
            if i > 0 {
                let expected_pred = self.entries[i - 1].sha256.clone();
                if let Some(ref pred) = entry.predecessor {
                    if pred != &expected_pred {
                        result.predecessor_errors.push(format!(
                            "Entry {} has wrong predecessor: expected {}, got {}",
                            entry.document_id, expected_pred, pred
                        ));
                    }
                }
            }

            // Deep verification: check file hashes
            if deep {
                let file_path = if let Some(ref base) = base_dir {
                    base.join(&entry.document_id)
                } else {
                    PathBuf::from(&entry.document_id)
                };

                if file_path.exists() {
                    match compute_sha256(&file_path) {
                        Ok(hash) => {
                            if hash != entry.sha256 {
                                result.hash_mismatches.push(format!(
                                    "{}: expected {}, got {}",
                                    entry.document_id, entry.sha256, hash
                                ));
                            } else {
                                result.verified_files.push(entry.document_id.clone());
                            }
                        }
                        Err(e) => {
                            result
                                .read_errors
                                .push(format!("{}: {}", entry.document_id, e));
                        }
                    }
                } else {
                    result.missing_files.push(entry.document_id.clone());
                }
            }
        }

        result
    }
}

/// Result of chain verification
#[derive(Default, Debug)]
struct VerificationResult {
    /// Files that were successfully verified
    verified_files: Vec<String>,
    /// Files that are missing
    missing_files: Vec<String>,
    /// Files with hash mismatches
    hash_mismatches: Vec<String>,
    /// Files that could not be read
    read_errors: Vec<String>,
    /// Predecessor chain errors
    predecessor_errors: Vec<String>,
}

impl VerificationResult {
    fn is_success(&self) -> bool {
        self.hash_mismatches.is_empty() && self.predecessor_errors.is_empty()
    }

    fn print(&self) {
        if !self.verified_files.is_empty() {
            println!("\n✓ Verified files:");
            for f in &self.verified_files {
                println!("  ✓ {}", f);
            }
        }

        if !self.missing_files.is_empty() {
            println!("\n⚠ Missing files:");
            for f in &self.missing_files {
                println!("  ⚠ {}", f);
            }
        }

        if !self.hash_mismatches.is_empty() {
            println!("\n✗ Hash mismatches:");
            for e in &self.hash_mismatches {
                println!("  ✗ {}", e);
            }
        }

        if !self.read_errors.is_empty() {
            println!("\n✗ Read errors:");
            for e in &self.read_errors {
                println!("  ✗ {}", e);
            }
        }

        if !self.predecessor_errors.is_empty() {
            println!("\n✗ Predecessor chain errors:");
            for e in &self.predecessor_errors {
                println!("  ✗ {}", e);
            }
        }
    }
}

/// Compute SHA-256 hash of a file
fn compute_sha256(path: &PathBuf) -> io::Result<String> {
    let mut file = fs::File::open(path)?;
    let mut contents = Vec::new();
    file.read_to_end(&mut contents)?;

    let mut hasher = Sha256::new();
    hasher.update(&contents);
    let result = hasher.finalize();

    Ok(format!("{:x}", result))
}

/// Load hash chain from file
fn load_chain(path: &PathBuf) -> io::Result<HashChain> {
    let contents = fs::read_to_string(path)?;
    let chain: HashChain = serde_json::from_str(&contents)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
    Ok(chain)
}

/// Save hash chain to file
fn save_chain(chain: &HashChain, path: &PathBuf) -> io::Result<()> {
    let json = serde_json::to_string_pretty(chain)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
    fs::write(path, json)?;
    Ok(())
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Init { chain_name, output } => {
            println!("=== RIINA Hash Chain Initialization ===");
            println!("Chain name: {}", chain_name);
            println!("Output file: {:?}", output);

            let chain = HashChain::new(chain_name);

            match save_chain(&chain, &output) {
                Ok(()) => {
                    println!("\n✓ Hash chain initialized successfully.");
                    println!("  Created: {}", chain.created);
                }
                Err(e) => {
                    eprintln!("\n✗ Failed to create hash chain: {}", e);
                    std::process::exit(1);
                }
            }
        }

        Commands::Add {
            file,
            predecessor,
            author,
            chain: chain_path,
        } => {
            println!("=== RIINA Hash Chain Add ===");
            println!("File: {:?}", file);
            println!("Author: {}", author);

            // Load existing chain
            let mut chain = match load_chain(&chain_path) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("✗ Failed to load hash chain: {}", e);
                    std::process::exit(1);
                }
            };

            // Compute hash
            let hash = match compute_sha256(&file) {
                Ok(h) => h,
                Err(e) => {
                    eprintln!("✗ Failed to compute hash: {}", e);
                    std::process::exit(1);
                }
            };

            // Determine predecessor
            let pred = predecessor.or_else(|| chain.latest_hash());

            // Create entry
            let entry = ChainEntry {
                document_id: file
                    .file_name()
                    .map(|n| n.to_string_lossy().to_string())
                    .unwrap_or_else(|| "unknown".to_string()),
                sha256: hash.clone(),
                predecessor: pred,
                timestamp: chrono::Utc::now().to_rfc3339(),
                author,
                signature: None,
            };

            chain.add_entry(entry);

            match save_chain(&chain, &chain_path) {
                Ok(()) => {
                    println!("\n✓ Document added successfully.");
                    println!("  Hash: {}", hash);
                }
                Err(e) => {
                    eprintln!("\n✗ Failed to save hash chain: {}", e);
                    std::process::exit(1);
                }
            }
        }

        Commands::Verify {
            deep,
            base_dir,
            chain: chain_path,
        } => {
            println!("=== RIINA Hash Chain Verification ===");
            println!("Deep verification: {}", deep);

            let chain = match load_chain(&chain_path) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("✗ Failed to load hash chain: {}", e);
                    std::process::exit(1);
                }
            };

            let result = chain.verify(deep, base_dir.as_ref());
            result.print();

            if result.is_success() {
                println!("\n✓ Hash chain verification PASSED");
            } else {
                println!("\n✗ Hash chain verification FAILED");
                std::process::exit(1);
            }
        }

        Commands::Show {
            format,
            chain: chain_path,
        } => {
            let chain = match load_chain(&chain_path) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("✗ Failed to load hash chain: {}", e);
                    std::process::exit(1);
                }
            };

            if format == "json" {
                match serde_json::to_string_pretty(&chain) {
                    Ok(json) => println!("{}", json),
                    Err(e) => {
                        eprintln!("✗ Failed to serialize: {}", e);
                        std::process::exit(1);
                    }
                }
            } else {
                println!("=== RIINA Hash Chain ===");
                println!("Name: {}", chain.name);
                println!("Version: {}", chain.version);
                println!("Created: {}", chain.created);
                println!("Modified: {}", chain.modified);
                println!("Entries: {}", chain.entries.len());
                println!();

                for (i, entry) in chain.entries.iter().enumerate() {
                    println!("{}. {} ", i + 1, entry.document_id);
                    println!("   Hash: {}...", &entry.sha256[..16]);
                    println!("   Author: {}", entry.author);
                    println!("   Time: {}", entry.timestamp);
                    if let Some(ref pred) = entry.predecessor {
                        println!("   Predecessor: {}...", &pred[..16]);
                    }
                    println!();
                }
            }
        }

        Commands::Export {
            output,
            chain: chain_path,
        } => {
            let chain = match load_chain(&chain_path) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("✗ Failed to load hash chain: {}", e);
                    std::process::exit(1);
                }
            };

            match save_chain(&chain, &output) {
                Ok(()) => println!("✓ Exported to {:?}", output),
                Err(e) => {
                    eprintln!("✗ Failed to export: {}", e);
                    std::process::exit(1);
                }
            }
        }

        Commands::Import { input, output } => {
            let chain = match load_chain(&input) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("✗ Failed to load chain from {:?}: {}", input, e);
                    std::process::exit(1);
                }
            };

            match save_chain(&chain, &output) {
                Ok(()) => println!("✓ Imported to {:?}", output),
                Err(e) => {
                    eprintln!("✗ Failed to save: {}", e);
                    std::process::exit(1);
                }
            }
        }

        Commands::Hash { file } => match compute_sha256(&file) {
            Ok(hash) => {
                println!("{}", hash);
            }
            Err(e) => {
                eprintln!("✗ Failed to compute hash: {}", e);
                std::process::exit(1);
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_hash_computation() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.txt");
        fs::write(&file_path, "hello world").unwrap();

        let hash = compute_sha256(&file_path).unwrap();

        // SHA-256 of "hello world"
        assert_eq!(
            hash,
            "b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"
        );
    }

    #[test]
    fn test_chain_creation() {
        let chain = HashChain::new("test-chain".to_string());

        assert_eq!(chain.name, "test-chain");
        assert_eq!(chain.version, "1.0.0");
        assert!(chain.entries.is_empty());
    }

    #[test]
    fn test_add_entry() {
        let mut chain = HashChain::new("test-chain".to_string());

        let entry = ChainEntry {
            document_id: "test.md".to_string(),
            sha256: "abc123".to_string(),
            predecessor: None,
            timestamp: chrono::Utc::now().to_rfc3339(),
            author: "test".to_string(),
            signature: None,
        };

        chain.add_entry(entry);

        assert_eq!(chain.entries.len(), 1);
        assert_eq!(chain.latest_hash(), Some("abc123".to_string()));
    }
}
