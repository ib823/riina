// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! iOS build pipeline for RIINA.
//!
//! Compiles generated Swift bridge code into XCFrameworks using
//! the Xcode toolchain.
//!
//! # Architecture
//!
//! ```text
//! IR (riina_codegen::Program)
//!     │
//!     ▼
//! ┌──────────────────┐
//! │ Swift Bridge Gen │  (swift_bridge.rs)
//! │ C + Swift bridge │
//! └──────────────────┘
//!     │
//!     ▼
//! ┌──────────────────┐
//! │ IosBuilder       │  (this module)
//! │ swift build/     │
//! │ xcodebuild       │
//! └──────────────────┘
//!     │
//!     ▼
//! RiinaBridge.xcframework
//! ```
//!
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom

use std::fs;
use std::path::{Path, PathBuf};
#[cfg(target_os = "macos")]
use std::process::Command;

use crate::toolchain::{IosToolchain, ToolchainError};

// Note: IosArch is available in toolchain module for arch-specific builds
#[allow(unused_imports)]
use crate::toolchain::IosArch;

use crate::swift_bridge::{
    generate_swift_bridge, generate_swift_c_bridge, generate_spm_package,
};

// Note: Program is not used in current API but kept for future IR-driven codegen
#[allow(unused_imports)]
use crate::ir::Program;

/// iOS build configuration.
#[derive(Debug, Clone)]
pub struct IosConfig {
    /// Framework name
    pub framework_name: String,
    /// Target architectures
    pub archs: Vec<IosArch>,
    /// Minimum deployment target
    pub deployment_target: String,
    /// Enable debug symbols
    pub debug: bool,
    /// Enable bitcode (deprecated in Xcode 14+)
    pub enable_bitcode: bool,
    /// Build as static library instead of framework
    pub static_lib: bool,
    /// Additional Swift compiler flags
    pub swiftflags: Vec<String>,
    /// Additional linker flags
    pub ldflags: Vec<String>,
}

impl Default for IosConfig {
    fn default() -> Self {
        Self {
            framework_name: "RiinaBridge".to_string(),
            archs: vec![IosArch::Arm64],
            deployment_target: "15.0".to_string(),
            debug: false,
            enable_bitcode: false,
            static_lib: false,
            swiftflags: vec![],
            ldflags: vec![],
        }
    }
}

/// Result of iOS build.
#[derive(Debug, Clone)]
pub struct IosArtifact {
    /// Path to built XCFramework (if built)
    pub framework_path: Option<PathBuf>,
    /// Swift bridge source
    pub swift_bridge: String,
    /// C bridge source
    pub c_bridge: String,
    /// Bridging header content
    pub bridging_header: String,
    /// Package.swift content
    pub package_swift: String,
    /// Info.plist keys
    pub info_plist_keys: String,
}

/// iOS build pipeline.
#[allow(dead_code)]
pub struct IosBuilder {
    toolchain: IosToolchain,
    output_dir: PathBuf,
}

/// Errors from iOS build.
#[derive(Debug)]
pub enum IosBuildError {
    Toolchain(ToolchainError),
    Io(std::io::Error),
    BuildFailed(String),
    InvalidConfig(String),
    UnsupportedPlatform,
}

impl std::fmt::Display for IosBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Toolchain(e) => write!(f, "Toolchain error: {}", e),
            Self::Io(e) => write!(f, "I/O error: {}", e),
            Self::BuildFailed(msg) => write!(f, "Build failed: {}", msg),
            Self::InvalidConfig(msg) => write!(f, "Invalid configuration: {}", msg),
            Self::UnsupportedPlatform => write!(f, "iOS builds require macOS"),
        }
    }
}

impl std::error::Error for IosBuildError {}

impl From<ToolchainError> for IosBuildError {
    fn from(e: ToolchainError) -> Self {
        Self::Toolchain(e)
    }
}

impl From<std::io::Error> for IosBuildError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

impl IosBuilder {
    /// Create a new iOS builder with detected toolchain.
    #[cfg(target_os = "macos")]
    pub fn new(output_dir: impl AsRef<Path>) -> Result<Self, IosBuildError> {
        let toolchain = IosToolchain::detect()?;
        Ok(Self {
            toolchain,
            output_dir: output_dir.as_ref().to_path_buf(),
        })
    }

    /// Platform check for non-macOS
    #[cfg(not(target_os = "macos"))]
    pub fn new(_output_dir: impl AsRef<Path>) -> Result<Self, IosBuildError> {
        Err(IosBuildError::UnsupportedPlatform)
    }

    /// Create builder with custom toolchain.
    #[cfg(target_os = "macos")]
    pub fn with_toolchain(
        toolchain: IosToolchain,
        output_dir: impl AsRef<Path>,
    ) -> Self {
        Self {
            toolchain,
            output_dir: output_dir.as_ref().to_path_buf(),
        }
    }

    /// Build the IR program for iOS.
    #[cfg(target_os = "macos")]
    pub fn build(
        &self,
        program: &Program,
        config: &IosConfig,
    ) -> Result<IosArtifact, IosBuildError> {
        // Create output directory structure
        let src_dir = self.output_dir.join("Sources").join(&config.framework_name);
        fs::create_dir_all(&src_dir)?;

        // Generate Swift bridge code
        let swift_bridge = generate_swift_bridge(&config.framework_name);
        let c_bridge = generate_swift_c_bridge();
        let bridging_header = generate_bridging_header(&config.framework_name);
        let package_swift = generate_spm_package(&config.framework_name);

        // Write source files
        fs::write(
            src_dir.join(&format!("{}.swift", config.framework_name)),
            &swift_bridge,
        )?;
        fs::write(src_dir.join("riina_bridge.c"), &c_bridge)?;
        fs::write(
            src_dir.join(&format!("{}-Bridging-Header.h", config.framework_name)),
            &bridging_header,
        )?;
        fs::write(self.output_dir.join("Package.swift"), &package_swift)?;

        // Build with swift build
        let framework_path = self.run_swift_build(config)?;

        // Generate Info.plist keys
        let info_plist_keys = self.generate_info_plist_keys(config);

        Ok(IosArtifact {
            framework_path: Some(framework_path),
            swift_bridge,
            c_bridge,
            bridging_header,
            package_swift,
            info_plist_keys,
        })
    }

    /// Run swift build.
    #[cfg(target_os = "macos")]
    fn run_swift_build(&self, config: &IosConfig) -> Result<PathBuf, IosBuildError> {
        let mut args = vec!["build"];

        if config.debug {
            args.push("-c");
            args.push("debug");
        } else {
            args.push("-c");
            args.push("release");
        }

        let output = Command::new(&self.toolchain.swift_path)
            .current_dir(&self.output_dir)
            .args(&args)
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(IosBuildError::BuildFailed(stderr.to_string()));
        }

        // Find the built framework
        let build_dir = if config.debug {
            self.output_dir.join(".build/debug")
        } else {
            self.output_dir.join(".build/release")
        };

        Ok(build_dir)
    }

    /// Generate Info.plist keys for the framework.
    #[cfg(target_os = "macos")]
    fn generate_info_plist_keys(&self, config: &IosConfig) -> String {
        format!(
            r#"<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>CFBundleName</key>
    <string>{}</string>
    <key>CFBundleIdentifier</key>
    <string>com.riina.{}</string>
    <key>CFBundleVersion</key>
    <string>1.0.0</string>
    <key>CFBundleShortVersionString</key>
    <string>1.0.0</string>
    <key>MinimumOSVersion</key>
    <string>{}</string>
</dict>
</plist>
"#,
            config.framework_name,
            config.framework_name.to_lowercase(),
            config.deployment_target
        )
    }
}

/// Build for iOS without toolchain detection (scaffolding mode).
///
/// This function generates all the source files needed for an iOS build
/// but does not invoke Xcode. Use this when Xcode is not available.
pub fn build_scaffolding(
    _program: &Program,
    config: &IosConfig,
    output_dir: impl AsRef<Path>,
) -> Result<IosArtifact, std::io::Error> {
    let output_dir = output_dir.as_ref();
    let src_dir = output_dir.join("Sources").join(&config.framework_name);
    fs::create_dir_all(&src_dir)?;

    // Generate Swift bridge code
    let swift_bridge = generate_swift_bridge(&config.framework_name);
    let c_bridge = generate_swift_c_bridge();
    let bridging_header = generate_bridging_header(&config.framework_name);
    let package_swift = generate_spm_package(&config.framework_name);

    // Write source files
    fs::write(
        src_dir.join(&format!("{}.swift", config.framework_name)),
        &swift_bridge,
    )?;
    fs::write(src_dir.join("riina_bridge.c"), &c_bridge)?;
    fs::write(
        src_dir.join(&format!("{}-Bridging-Header.h", config.framework_name)),
        &bridging_header,
    )?;
    fs::write(output_dir.join("Package.swift"), &package_swift)?;

    // Generate Info.plist keys
    let info_plist_keys = generate_info_plist_scaffolding(config);
    fs::write(output_dir.join("Info.plist"), &info_plist_keys)?;

    Ok(IosArtifact {
        framework_path: None, // No actual build in scaffolding mode
        swift_bridge,
        c_bridge,
        bridging_header,
        package_swift,
        info_plist_keys,
    })
}

/// Generate Objective-C bridging header for Swift.
fn generate_bridging_header(module_name: &str) -> String {
    format!(
        r#"//
// {module_name}-Bridging-Header.h
// RIINA Generated Bridging Header
//
// SPDX-License-Identifier: MPL-2.0
//

#ifndef {module_name}_Bridging_Header_h
#define {module_name}_Bridging_Header_h

// Include C bridge functions
#include "riina_bridge.h"

// RIINA C runtime declarations
extern int riina_main(void);
extern int riina_verify(void);

// Platform callbacks (implemented in Swift)
void riina_ios_log(const char *message);
void riina_ios_panic(const char *message);

#endif /* {module_name}_Bridging_Header_h */
"#,
        module_name = module_name
    )
}

fn generate_info_plist_scaffolding(config: &IosConfig) -> String {
    format!(
        r#"<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>CFBundleName</key>
    <string>{}</string>
    <key>CFBundleIdentifier</key>
    <string>com.riina.{}</string>
    <key>CFBundleVersion</key>
    <string>1.0.0</string>
    <key>CFBundleShortVersionString</key>
    <string>1.0.0</string>
    <key>MinimumOSVersion</key>
    <string>{}</string>
</dict>
</plist>
"#,
        config.framework_name,
        config.framework_name.to_lowercase(),
        config.deployment_target
    )
}

/// Create an XCFramework from multiple platform builds.
#[cfg(target_os = "macos")]
pub fn create_xcframework(
    device_path: impl AsRef<Path>,
    simulator_path: impl AsRef<Path>,
    output_path: impl AsRef<Path>,
    framework_name: &str,
) -> Result<(), IosBuildError> {
    let output = Command::new("xcodebuild")
        .arg("-create-xcframework")
        .arg("-framework")
        .arg(device_path.as_ref().join(format!("{}.framework", framework_name)))
        .arg("-framework")
        .arg(simulator_path.as_ref().join(format!("{}.framework", framework_name)))
        .arg("-output")
        .arg(output_path.as_ref().join(format!("{}.xcframework", framework_name)))
        .output()
        .map_err(|e| IosBuildError::Io(e))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(IosBuildError::BuildFailed(stderr.to_string()));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Program;

    #[test]
    fn test_ios_config_default() {
        let config = IosConfig::default();
        assert_eq!(config.framework_name, "RiinaBridge");
        assert_eq!(config.deployment_target, "15.0");
        assert!(!config.debug);
        assert!(!config.enable_bitcode);
    }

    #[test]
    fn test_generate_info_plist_scaffolding() {
        let config = IosConfig::default();
        let plist = generate_info_plist_scaffolding(&config);
        assert!(plist.contains("RiinaBridge"));
        assert!(plist.contains("15.0"));
        assert!(plist.contains("com.riina.riinabridge"));
    }

    #[test]
    fn test_build_scaffolding() {
        let program = Program::new();
        let config = IosConfig::default();
        let temp_dir = std::env::temp_dir().join("riina_ios_test");
        let _ = fs::remove_dir_all(&temp_dir);
        fs::create_dir_all(&temp_dir).unwrap();

        let result = build_scaffolding(&program, &config, &temp_dir);
        assert!(result.is_ok());

        let artifact = result.unwrap();
        assert!(!artifact.swift_bridge.is_empty());
        assert!(!artifact.c_bridge.is_empty());
        assert!(!artifact.bridging_header.is_empty());
        assert!(!artifact.package_swift.is_empty());
        assert!(artifact.framework_path.is_none()); // Scaffolding doesn't build

        // Check files were created
        let src_dir = temp_dir.join("Sources/RiinaBridge");
        assert!(src_dir.join("RiinaBridge.swift").exists());
        assert!(src_dir.join("riina_bridge.c").exists());
        assert!(src_dir.join("RiinaBridge-Bridging-Header.h").exists());
        assert!(temp_dir.join("Package.swift").exists());
        assert!(temp_dir.join("Info.plist").exists());

        // Cleanup
        let _ = fs::remove_dir_all(&temp_dir);
    }

    #[test]
    fn test_ios_build_error_display() {
        let errors = vec![
            IosBuildError::UnsupportedPlatform,
            IosBuildError::BuildFailed("test".to_string()),
            IosBuildError::InvalidConfig("test".to_string()),
        ];

        for error in errors {
            let display = format!("{}", error);
            assert!(!display.is_empty());
            let _: &dyn std::error::Error = &error;
        }
    }
}
