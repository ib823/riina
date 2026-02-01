// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! Backend Trait Architecture
//!
//! Defines the `Backend` trait for modular code emission and the `Target` enum
//! for platform selection. All backends (C, WASM, mobile) implement this trait.
//!
//! # Architecture
//!
//! ```text
//!   ir::Program
//!       │
//!       ▼
//!   ┌────────────────────┐
//!   │  Backend::emit()   │  Trait dispatch based on Target
//!   └────────────────────┘
//!       │
//!       ├── CBackend        → C99 source code (default)
//!       ├── WasmBackend     → .wasm binary
//!       ├── AndroidBackend  → C + JNI bridge → NDK .so
//!       └── IosBackend      → C + Swift bridge → Xcode .a
//! ```
//!
//! # Correspondence with Coq
//!
//! All backends must preserve the security invariants proven in
//! `02_FORMAL/coq/properties/NonInterference_v2.v`:
//! - Non-interference (secrets cannot flow to public outputs)
//! - Effect safety (functions cannot perform undeclared side effects)
//! - Type safety (no runtime type errors)
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST

use crate::ir::Program;
use crate::Result;

/// Compilation target platform.
///
/// Determines which backend emitter is used and what platform-specific
/// code is generated.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Target {
    /// Native compilation via C backend (default).
    /// `riinac build file.rii` → C → cc → native binary
    Native,

    /// WebAssembly 32-bit.
    /// `riinac build --target=wasm32 file.rii` → .wasm binary
    Wasm32,

    /// WebAssembly 64-bit (memory64 proposal).
    /// `riinac build --target=wasm64 file.rii` → .wasm binary
    Wasm64,

    /// Android ARM64 via NDK.
    /// `riinac build --target=android-arm64 file.rii` → C + JNI → .so
    AndroidArm64,

    /// iOS ARM64 via Xcode toolchain.
    /// `riinac build --target=ios-arm64 file.rii` → C + Swift bridge → .a
    IosArm64,
}

impl Target {
    /// Parse a target string from the CLI `--target` flag.
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "native" => Some(Self::Native),
            "wasm32" => Some(Self::Wasm32),
            "wasm64" => Some(Self::Wasm64),
            "android-arm64" => Some(Self::AndroidArm64),
            "ios-arm64" => Some(Self::IosArm64),
            _ => None,
        }
    }

    /// Returns the human-readable name for this target.
    pub fn name(&self) -> &'static str {
        match self {
            Self::Native => "native",
            Self::Wasm32 => "wasm32",
            Self::Wasm64 => "wasm64",
            Self::AndroidArm64 => "android-arm64",
            Self::IosArm64 => "ios-arm64",
        }
    }

    /// Returns true if this target is a WebAssembly target.
    pub fn is_wasm(&self) -> bool {
        matches!(self, Self::Wasm32 | Self::Wasm64)
    }

    /// Returns true if this target is a mobile target.
    pub fn is_mobile(&self) -> bool {
        matches!(self, Self::AndroidArm64 | Self::IosArm64)
    }
}

impl std::fmt::Display for Target {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Output from a backend compilation.
#[derive(Debug)]
pub struct BackendOutput {
    /// Primary output bytes (C source, WASM binary, etc.)
    pub primary: Vec<u8>,
    /// File extension for the primary output (e.g., ".c", ".wasm")
    pub extension: String,
    /// Optional auxiliary files (e.g., JS glue for WASM, JNI bridge for Android)
    pub auxiliary: Vec<AuxFile>,
}

/// An auxiliary file produced by a backend.
#[derive(Debug)]
pub struct AuxFile {
    /// Filename (e.g., "bridge.js", "Bridge.java")
    pub name: String,
    /// File contents
    pub content: Vec<u8>,
}

/// Backend trait for code emission.
///
/// All platform backends implement this trait. The trait provides a uniform
/// interface for emitting code from RIINA IR, regardless of target platform.
///
/// # Invariants
///
/// Implementations MUST preserve RIINA's security properties:
/// - Non-interference: secret data cannot flow to public outputs
/// - Effect safety: declared effects match actual capabilities used
/// - Type safety: type errors are caught at compile time
pub trait Backend {
    /// Emit code for the given program.
    ///
    /// Returns the compiled output (bytes) and metadata about the output format.
    fn emit(&self, program: &Program) -> Result<BackendOutput>;

    /// Returns the target this backend compiles for.
    fn target(&self) -> Target;
}

/// Select the appropriate backend for a given target.
pub fn backend_for_target(target: Target) -> Box<dyn Backend> {
    match target {
        Target::Native => Box::new(CBackend),
        Target::Wasm32 => Box::new(crate::wasm::WasmBackend::new(Target::Wasm32)),
        Target::Wasm64 => Box::new(crate::wasm::WasmBackend::new(Target::Wasm64)),
        Target::AndroidArm64 => Box::new(crate::mobile::MobileBackend::new(Target::AndroidArm64)),
        Target::IosArm64 => Box::new(crate::mobile::MobileBackend::new(Target::IosArm64)),
    }
}

/// C backend — delegates to the existing CEmitter.
pub struct CBackend;

impl Backend for CBackend {
    fn emit(&self, program: &Program) -> Result<BackendOutput> {
        let mut emitter = crate::emit::CEmitter::new();
        let c_code = emitter.emit(program)?;
        Ok(BackendOutput {
            primary: c_code.into_bytes(),
            extension: ".c".to_string(),
            auxiliary: Vec::new(),
        })
    }

    fn target(&self) -> Target {
        Target::Native
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_target_from_str() {
        assert_eq!(Target::from_str("native"), Some(Target::Native));
        assert_eq!(Target::from_str("wasm32"), Some(Target::Wasm32));
        assert_eq!(Target::from_str("wasm64"), Some(Target::Wasm64));
        assert_eq!(Target::from_str("android-arm64"), Some(Target::AndroidArm64));
        assert_eq!(Target::from_str("ios-arm64"), Some(Target::IosArm64));
        assert_eq!(Target::from_str("unknown"), None);
    }

    #[test]
    fn test_target_name() {
        assert_eq!(Target::Native.name(), "native");
        assert_eq!(Target::Wasm32.name(), "wasm32");
        assert_eq!(Target::AndroidArm64.name(), "android-arm64");
    }

    #[test]
    fn test_target_is_wasm() {
        assert!(!Target::Native.is_wasm());
        assert!(Target::Wasm32.is_wasm());
        assert!(Target::Wasm64.is_wasm());
        assert!(!Target::AndroidArm64.is_wasm());
    }

    #[test]
    fn test_target_is_mobile() {
        assert!(!Target::Native.is_mobile());
        assert!(!Target::Wasm32.is_mobile());
        assert!(Target::AndroidArm64.is_mobile());
        assert!(Target::IosArm64.is_mobile());
    }

    #[test]
    fn test_target_display() {
        assert_eq!(format!("{}", Target::Native), "native");
        assert_eq!(format!("{}", Target::Wasm32), "wasm32");
    }

    #[test]
    fn test_c_backend_target() {
        let backend = CBackend;
        assert_eq!(backend.target(), Target::Native);
    }

    #[test]
    fn test_c_backend_emit() {
        let backend = CBackend;
        let program = crate::ir::Program::new();
        let output = backend.emit(&program).unwrap();
        assert_eq!(output.extension, ".c");
        assert!(output.auxiliary.is_empty());
        // C output should contain a main function
        let c_code = String::from_utf8(output.primary).unwrap();
        assert!(c_code.contains("main"));
    }

    #[test]
    fn test_backend_for_target() {
        let backend = backend_for_target(Target::Native);
        assert_eq!(backend.target(), Target::Native);
    }
}
