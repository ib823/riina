//! Error types for riina-pkg.

use std::fmt;
use std::path::PathBuf;

/// All errors produced by the package manager.
#[derive(Debug)]
pub enum PkgError {
    /// I/O error with context path.
    Io { path: PathBuf, source: std::io::Error },
    /// TOML parse error.
    ManifestParse { file: PathBuf, line: usize, message: String },
    /// Missing required field in manifest.
    ManifestMissing { file: PathBuf, field: String },
    /// Invalid semver string.
    InvalidVersion(String),
    /// Invalid version requirement string.
    InvalidVersionReq(String),
    /// Dependency not found in registry.
    DependencyNotFound { name: String, req: String },
    /// Version conflict: no version satisfies all constraints.
    VersionConflict { name: String, constraints: Vec<String> },
    /// Dependency cycle detected.
    CycleDetected(Vec<String>),
    /// Effect escalation: dependency requires forbidden effect.
    EffectEscalation { dep: String, effect: String },
    /// Integrity check failed.
    IntegrityMismatch { name: String, expected: String, actual: String },
    /// Package already exists in registry.
    AlreadyPublished { name: String, version: String },
    /// Workspace error.
    Workspace(String),
    /// Generic error.
    Other(String),
}

impl fmt::Display for PkgError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, source } => write!(f, "I/O error at {}: {}", path.display(), source),
            Self::ManifestParse { file, line, message } => {
                write!(f, "{}:{}: {}", file.display(), line, message)
            }
            Self::ManifestMissing { file, field } => {
                write!(f, "{}: missing required field '{}'", file.display(), field)
            }
            Self::InvalidVersion(s) => write!(f, "invalid version: {s}"),
            Self::InvalidVersionReq(s) => write!(f, "invalid version requirement: {s}"),
            Self::DependencyNotFound { name, req } => {
                write!(f, "dependency '{name}' not found matching {req}")
            }
            Self::VersionConflict { name, constraints } => {
                write!(f, "version conflict for '{name}': {}", constraints.join(", "))
            }
            Self::CycleDetected(cycle) => {
                write!(f, "dependency cycle: {}", cycle.join(" -> "))
            }
            Self::EffectEscalation { dep, effect } => {
                write!(f, "effect escalation: '{dep}' requires forbidden effect '{effect}'")
            }
            Self::IntegrityMismatch { name, expected, actual } => {
                write!(f, "integrity mismatch for '{name}': expected {expected}, got {actual}")
            }
            Self::AlreadyPublished { name, version } => {
                write!(f, "'{name}' v{version} already published")
            }
            Self::Workspace(msg) => write!(f, "workspace error: {msg}"),
            Self::Other(msg) => write!(f, "{msg}"),
        }
    }
}

impl std::error::Error for PkgError {}

impl PkgError {
    pub fn io(path: impl Into<PathBuf>, source: std::io::Error) -> Self {
        Self::Io { path: path.into(), source }
    }
}

pub type Result<T> = std::result::Result<T, PkgError>;
