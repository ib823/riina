// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Android build pipeline for RIINA.
//!
//! Compiles generated JNI bridge code into native .so libraries using
//! the Android NDK toolchain.
//!
//! # Architecture
//!
//! ```text
//! IR (riina_codegen::Program)
//!     │
//!     ▼
//! ┌──────────────────┐
//! │ JNI Code Gen     │  (jni.rs)
//! │ C + Java bridge  │
//! └──────────────────┘
//!     │
//!     ▼
//! ┌──────────────────┐
//! │ AndroidBuilder   │  (this module)
//! │ ndk-build/cmake  │
//! └──────────────────┘
//!     │
//!     ▼
//! libriina.so (per ABI)
//! ```
//!
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::toolchain::{AndroidToolchain, AndroidAbi, ToolchainError};
use crate::jni::{generate_jni_bridge, generate_jni_header, generate_jni_impl};

// Note: Program is not used in current API but kept for future IR-driven codegen
#[allow(unused_imports)]
use crate::ir::Program;

/// Android build configuration.
#[derive(Debug, Clone)]
pub struct AndroidConfig {
    /// Library name (without lib prefix and .so suffix)
    pub lib_name: String,
    /// Target ABIs to build
    pub abis: Vec<AndroidAbi>,
    /// Minimum API level
    pub api_level: u32,
    /// Enable debug symbols
    pub debug: bool,
    /// Optimization level (0-3)
    pub opt_level: u32,
    /// Additional compiler flags
    pub cflags: Vec<String>,
    /// Additional linker flags
    pub ldflags: Vec<String>,
}

impl Default for AndroidConfig {
    fn default() -> Self {
        Self {
            lib_name: "riina".to_string(),
            abis: vec![AndroidAbi::Arm64V8a, AndroidAbi::ArmeabiV7a],
            api_level: 21,
            debug: false,
            opt_level: 2,
            cflags: vec![],
            ldflags: vec![],
        }
    }
}

/// Result of Android build.
#[derive(Debug, Clone)]
pub struct AndroidArtifact {
    /// Map of ABI to library path
    pub libs: Vec<(AndroidAbi, PathBuf)>,
    /// Java bridge class file content
    pub java_bridge: String,
    /// C header file content
    pub c_header: String,
    /// AndroidManifest.xml snippet
    pub manifest_snippet: String,
}

/// Android build pipeline.
pub struct AndroidBuilder {
    toolchain: AndroidToolchain,
    output_dir: PathBuf,
}

/// Errors from Android build.
#[derive(Debug)]
pub enum AndroidBuildError {
    Toolchain(ToolchainError),
    Io(std::io::Error),
    BuildFailed(String),
    InvalidConfig(String),
}

impl std::fmt::Display for AndroidBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Toolchain(e) => write!(f, "Toolchain error: {}", e),
            Self::Io(e) => write!(f, "I/O error: {}", e),
            Self::BuildFailed(msg) => write!(f, "Build failed: {}", msg),
            Self::InvalidConfig(msg) => write!(f, "Invalid configuration: {}", msg),
        }
    }
}

impl std::error::Error for AndroidBuildError {}

impl From<ToolchainError> for AndroidBuildError {
    fn from(e: ToolchainError) -> Self {
        Self::Toolchain(e)
    }
}

impl From<std::io::Error> for AndroidBuildError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

impl AndroidBuilder {
    /// Create a new Android builder with detected toolchain.
    pub fn new(output_dir: impl AsRef<Path>) -> Result<Self, AndroidBuildError> {
        let toolchain = AndroidToolchain::detect()?;
        Ok(Self {
            toolchain,
            output_dir: output_dir.as_ref().to_path_buf(),
        })
    }

    /// Create builder with custom toolchain.
    pub fn with_toolchain(
        toolchain: AndroidToolchain,
        output_dir: impl AsRef<Path>,
    ) -> Self {
        Self {
            toolchain,
            output_dir: output_dir.as_ref().to_path_buf(),
        }
    }

    /// Build the IR program for Android.
    pub fn build(
        &self,
        _program: &Program,
        config: &AndroidConfig,
    ) -> Result<AndroidArtifact, AndroidBuildError> {
        // Create output directory structure
        let jni_dir = self.output_dir.join("jni");
        let libs_dir = self.output_dir.join("libs");
        fs::create_dir_all(&jni_dir)?;
        fs::create_dir_all(&libs_dir)?;

        // Generate JNI bridge code
        // Package name format: com.riina.{lib_name}
        let package = format!("com.riina.{}", config.lib_name);
        let java_bridge = generate_jni_bridge(&package, &config.lib_name);
        let c_header = generate_jni_header(&package, &config.lib_name);
        let c_impl = generate_jni_impl(&package, &config.lib_name);

        // Write source files
        fs::write(jni_dir.join("riina_jni.h"), &c_header)?;
        fs::write(jni_dir.join("riina_jni.c"), &c_impl)?;

        // Generate Android.mk
        let android_mk = self.generate_android_mk(config);
        fs::write(jni_dir.join("Android.mk"), &android_mk)?;

        // Generate Application.mk
        let app_mk = self.generate_application_mk(config);
        fs::write(jni_dir.join("Application.mk"), &app_mk)?;

        // Run ndk-build
        let _build_output = self.run_ndk_build(config)?;

        // Collect built libraries
        let libs = self.collect_libs(config, &libs_dir)?;

        // Generate manifest snippet
        let manifest_snippet = self.generate_manifest_snippet(config);

        Ok(AndroidArtifact {
            libs,
            java_bridge,
            c_header,
            manifest_snippet,
        })
    }

    /// Generate Android.mk build file.
    fn generate_android_mk(&self, config: &AndroidConfig) -> String {
        let mut mk = String::new();

        mk.push_str("LOCAL_PATH := $(call my-dir)\n\n");
        mk.push_str("include $(CLEAR_VARS)\n\n");
        mk.push_str(&format!("LOCAL_MODULE := {}\n", config.lib_name));
        mk.push_str("LOCAL_SRC_FILES := riina_jni.c\n");
        mk.push_str("LOCAL_C_INCLUDES := $(LOCAL_PATH)\n");

        // Compiler flags
        mk.push_str("LOCAL_CFLAGS := -std=c99 -Wall -Werror");
        if config.debug {
            mk.push_str(" -g -O0");
        } else {
            mk.push_str(&format!(" -O{}", config.opt_level));
        }
        for flag in &config.cflags {
            mk.push_str(&format!(" {}", flag));
        }
        mk.push('\n');

        // Linker flags
        if !config.ldflags.is_empty() {
            mk.push_str("LOCAL_LDFLAGS :=");
            for flag in &config.ldflags {
                mk.push_str(&format!(" {}", flag));
            }
            mk.push('\n');
        }

        mk.push_str("LOCAL_LDLIBS := -llog -landroid\n\n");
        mk.push_str("include $(BUILD_SHARED_LIBRARY)\n");

        mk
    }

    /// Generate Application.mk for NDK.
    fn generate_application_mk(&self, config: &AndroidConfig) -> String {
        let mut mk = String::new();

        // ABI filter
        let abis: Vec<&str> = config.abis.iter().map(|a| a.ndk_abi()).collect();
        mk.push_str(&format!("APP_ABI := {}\n", abis.join(" ")));

        // Platform
        mk.push_str(&format!("APP_PLATFORM := android-{}\n", config.api_level));

        // STL
        mk.push_str("APP_STL := c++_static\n");

        // Optimization
        if config.debug {
            mk.push_str("APP_OPTIM := debug\n");
        } else {
            mk.push_str("APP_OPTIM := release\n");
        }

        mk
    }

    /// Run ndk-build.
    fn run_ndk_build(&self, _config: &AndroidConfig) -> Result<String, AndroidBuildError> {
        let status = Command::new(&self.toolchain.ndk_build_path)
            .current_dir(&self.output_dir)
            .arg("NDK_PROJECT_PATH=.")
            .arg("APP_BUILD_SCRIPT=jni/Android.mk")
            .arg("NDK_APPLICATION_MK=jni/Application.mk")
            .arg("NDK_LIBS_OUT=libs")
            .arg("NDK_OUT=obj")
            .output()?;

        if !status.status.success() {
            let stderr = String::from_utf8_lossy(&status.stderr);
            return Err(AndroidBuildError::BuildFailed(stderr.to_string()));
        }

        let stdout = String::from_utf8_lossy(&status.stdout);
        Ok(stdout.to_string())
    }

    /// Collect built library files.
    fn collect_libs(
        &self,
        config: &AndroidConfig,
        libs_dir: &Path,
    ) -> Result<Vec<(AndroidAbi, PathBuf)>, AndroidBuildError> {
        let mut libs = Vec::new();

        for abi in &config.abis {
            let lib_path = libs_dir
                .join(abi.ndk_abi())
                .join(format!("lib{}.so", config.lib_name));

            if lib_path.exists() {
                libs.push((*abi, lib_path));
            }
        }

        if libs.is_empty() {
            return Err(AndroidBuildError::BuildFailed(
                "No libraries were built".to_string()
            ));
        }

        Ok(libs)
    }

    /// Generate AndroidManifest.xml snippet with permissions.
    fn generate_manifest_snippet(&self, _config: &AndroidConfig) -> String {
        // Basic manifest snippet - effects would be analyzed at a higher level
        r#"<!-- RIINA native library permissions -->
<uses-permission android:name="android.permission.INTERNET" />
"#.to_string()
    }
}

/// Build for Android without toolchain detection (scaffolding mode).
///
/// This function generates all the source files needed for an Android build
/// but does not invoke the NDK. Use this when the NDK is not available.
pub fn build_scaffolding(
    _program: &Program,
    config: &AndroidConfig,
    output_dir: impl AsRef<Path>,
) -> Result<AndroidArtifact, std::io::Error> {
    let output_dir = output_dir.as_ref();
    let jni_dir = output_dir.join("jni");
    fs::create_dir_all(&jni_dir)?;

    // Generate JNI bridge code
    let package = format!("com.riina.{}", config.lib_name);
    let java_bridge = generate_jni_bridge(&package, &config.lib_name);
    let c_header = generate_jni_header(&package, &config.lib_name);
    let c_impl = generate_jni_impl(&package, &config.lib_name);

    // Write source files
    fs::write(jni_dir.join("riina_jni.h"), &c_header)?;
    fs::write(jni_dir.join("riina_jni.c"), &c_impl)?;

    // Generate build files
    let android_mk = generate_android_mk_scaffolding(config);
    let app_mk = generate_application_mk_scaffolding(config);
    fs::write(jni_dir.join("Android.mk"), &android_mk)?;
    fs::write(jni_dir.join("Application.mk"), &app_mk)?;

    // Generate manifest snippet
    let manifest_snippet = r#"<!-- RIINA native library -->
<uses-permission android:name="android.permission.INTERNET" />
"#.to_string();

    Ok(AndroidArtifact {
        libs: vec![], // No actual build in scaffolding mode
        java_bridge,
        c_header,
        manifest_snippet,
    })
}

fn generate_android_mk_scaffolding(config: &AndroidConfig) -> String {
    format!(
        r#"LOCAL_PATH := $(call my-dir)

include $(CLEAR_VARS)

LOCAL_MODULE := {}
LOCAL_SRC_FILES := riina_jni.c
LOCAL_C_INCLUDES := $(LOCAL_PATH)
LOCAL_CFLAGS := -std=c99 -Wall -Werror -O{}
LOCAL_LDLIBS := -llog -landroid

include $(BUILD_SHARED_LIBRARY)
"#,
        config.lib_name,
        config.opt_level
    )
}

fn generate_application_mk_scaffolding(config: &AndroidConfig) -> String {
    let abis: Vec<&str> = config.abis.iter().map(|a| a.ndk_abi()).collect();
    format!(
        r#"APP_ABI := {}
APP_PLATFORM := android-{}
APP_STL := c++_static
APP_OPTIM := release
"#,
        abis.join(" "),
        config.api_level
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Program;

    #[test]
    fn test_android_config_default() {
        let config = AndroidConfig::default();
        assert_eq!(config.lib_name, "riina");
        assert_eq!(config.api_level, 21);
        assert!(!config.debug);
        assert_eq!(config.opt_level, 2);
    }

    #[test]
    fn test_generate_android_mk_scaffolding() {
        let config = AndroidConfig::default();
        let mk = generate_android_mk_scaffolding(&config);
        assert!(mk.contains("LOCAL_MODULE := riina"));
        assert!(mk.contains("-std=c99"));
        assert!(mk.contains("-Wall"));
        assert!(mk.contains("-O2"));
    }

    #[test]
    fn test_generate_application_mk_scaffolding() {
        let config = AndroidConfig {
            abis: vec![AndroidAbi::Arm64V8a],
            api_level: 24,
            ..Default::default()
        };
        let mk = generate_application_mk_scaffolding(&config);
        assert!(mk.contains("APP_ABI := arm64-v8a"));
        assert!(mk.contains("APP_PLATFORM := android-24"));
    }

    #[test]
    fn test_build_scaffolding() {
        let program = Program::new();
        let config = AndroidConfig::default();
        let temp_dir = std::env::temp_dir().join("riina_android_test");
        let _ = fs::remove_dir_all(&temp_dir);
        fs::create_dir_all(&temp_dir).unwrap();

        let result = build_scaffolding(&program, &config, &temp_dir);
        assert!(result.is_ok());

        let artifact = result.unwrap();
        assert!(!artifact.java_bridge.is_empty());
        assert!(!artifact.c_header.is_empty());
        assert!(artifact.libs.is_empty()); // Scaffolding doesn't build

        // Check files were created
        assert!(temp_dir.join("jni/riina_jni.c").exists());
        assert!(temp_dir.join("jni/riina_jni.h").exists());
        assert!(temp_dir.join("jni/Android.mk").exists());
        assert!(temp_dir.join("jni/Application.mk").exists());

        // Cleanup
        let _ = fs::remove_dir_all(&temp_dir);
    }
}
