// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Toolchain detection for mobile backends.
//!
//! This module detects and validates the presence of Android NDK and iOS
//! toolchains for compiling RIINA mobile backends.
//!
//! # Android
//!
//! Detects NDK via environment variables:
//! - `ANDROID_NDK_HOME`
//! - `ANDROID_NDK_ROOT`
//! - `NDK_HOME`
//!
//! # iOS
//!
//! Detects Xcode via `xcrun` commands.
//!
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom

use std::env;
use std::path::PathBuf;

/// Errors that can occur during toolchain detection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ToolchainError {
    /// Android NDK not found
    NdkNotFound,
    /// Android SDK not found
    SdkNotFound,
    /// Xcode not found
    XcodeNotFound,
    /// xcodebuild not available
    XcodeBuildNotFound,
    /// clang not found in toolchain
    ClangNotFound,
    /// Invalid toolchain path
    InvalidPath(String),
    /// Command execution failed
    CommandFailed(String),
    /// Unsupported platform
    UnsupportedPlatform,
    /// NDK build tool not found
    NdkBuildNotFound,
    /// cmake not found
    CmakeNotFound,
    /// Swift not found
    SwiftNotFound,
}

impl std::fmt::Display for ToolchainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NdkNotFound => write!(f, "Android NDK not found. Set ANDROID_NDK_HOME or ANDROID_NDK_ROOT."),
            Self::SdkNotFound => write!(f, "Android SDK not found. Set ANDROID_HOME or ANDROID_SDK_ROOT."),
            Self::XcodeNotFound => write!(f, "Xcode not found. Install Xcode from the App Store."),
            Self::XcodeBuildNotFound => write!(f, "xcodebuild not found. Install Xcode Command Line Tools."),
            Self::ClangNotFound => write!(f, "clang not found in toolchain."),
            Self::InvalidPath(path) => write!(f, "Invalid toolchain path: {}", path),
            Self::CommandFailed(msg) => write!(f, "Command failed: {}", msg),
            Self::UnsupportedPlatform => write!(f, "Mobile build not supported on this platform."),
            Self::NdkBuildNotFound => write!(f, "ndk-build not found in NDK."),
            Self::CmakeNotFound => write!(f, "cmake not found. Install CMake for Android builds."),
            Self::SwiftNotFound => write!(f, "swift not found. Install Xcode for iOS builds."),
        }
    }
}

impl std::error::Error for ToolchainError {}

/// Android ABI target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AndroidAbi {
    /// ARM 64-bit
    Arm64V8a,
    /// ARM 32-bit v7a
    ArmeabiV7a,
    /// x86 64-bit
    X86_64,
    /// x86 32-bit
    X86,
}

impl AndroidAbi {
    /// NDK ABI string
    pub fn ndk_abi(&self) -> &'static str {
        match self {
            Self::Arm64V8a => "arm64-v8a",
            Self::ArmeabiV7a => "armeabi-v7a",
            Self::X86_64 => "x86_64",
            Self::X86 => "x86",
        }
    }

    /// LLVM triple
    pub fn triple(&self) -> &'static str {
        match self {
            Self::Arm64V8a => "aarch64-linux-android",
            Self::ArmeabiV7a => "armv7a-linux-androideabi",
            Self::X86_64 => "x86_64-linux-android",
            Self::X86 => "i686-linux-android",
        }
    }

    /// All supported ABIs
    pub fn all() -> &'static [AndroidAbi] {
        &[Self::Arm64V8a, Self::ArmeabiV7a, Self::X86_64, Self::X86]
    }
}

impl std::fmt::Display for AndroidAbi {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.ndk_abi())
    }
}

/// iOS architecture target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IosArch {
    /// ARM 64-bit (device)
    Arm64,
    /// ARM 64-bit (simulator on Apple Silicon)
    Arm64Simulator,
    /// x86 64-bit (simulator on Intel)
    X86_64Simulator,
}

impl IosArch {
    /// Clang target triple
    pub fn triple(&self) -> &'static str {
        match self {
            Self::Arm64 => "arm64-apple-ios",
            Self::Arm64Simulator => "arm64-apple-ios-simulator",
            Self::X86_64Simulator => "x86_64-apple-ios-simulator",
        }
    }

    /// SDK name for xcrun
    pub fn sdk_name(&self) -> &'static str {
        match self {
            Self::Arm64 => "iphoneos",
            Self::Arm64Simulator | Self::X86_64Simulator => "iphonesimulator",
        }
    }
}

impl std::fmt::Display for IosArch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.triple())
    }
}

/// Detected Android toolchain configuration.
#[derive(Debug, Clone)]
pub struct AndroidToolchain {
    /// Path to NDK root directory
    pub ndk_path: PathBuf,
    /// Path to SDK root directory (optional)
    pub sdk_path: Option<PathBuf>,
    /// NDK version string (e.g., "25.2.9519653")
    pub ndk_version: String,
    /// Minimum API level to target
    pub api_level: u32,
    /// Available ABIs
    pub abis: Vec<AndroidAbi>,
    /// Path to ndk-build
    pub ndk_build_path: PathBuf,
    /// Path to CMake (optional)
    pub cmake_path: Option<PathBuf>,
}

impl AndroidToolchain {
    /// Detect Android toolchain from environment.
    pub fn detect() -> Result<Self, ToolchainError> {
        // Find NDK path
        let ndk_path = Self::find_ndk_path()?;

        // Validate NDK structure
        if !ndk_path.join("toolchains").exists() {
            return Err(ToolchainError::InvalidPath(
                format!("{} does not contain toolchains/", ndk_path.display())
            ));
        }

        // Get NDK version
        let ndk_version = Self::read_ndk_version(&ndk_path)?;

        // Find SDK path (optional)
        let sdk_path = Self::find_sdk_path();

        // Find ndk-build
        let ndk_build_path = Self::find_ndk_build(&ndk_path)?;

        // Find cmake (optional)
        let cmake_path = Self::find_cmake();

        // Default ABIs and API level
        let abis = vec![AndroidAbi::Arm64V8a, AndroidAbi::ArmeabiV7a];
        let api_level = 21; // Default minimum

        Ok(Self {
            ndk_path,
            sdk_path,
            ndk_version,
            api_level,
            abis,
            ndk_build_path,
            cmake_path,
        })
    }

    /// Find NDK path from environment variables.
    fn find_ndk_path() -> Result<PathBuf, ToolchainError> {
        // Try environment variables in order of preference
        for var in &["ANDROID_NDK_HOME", "ANDROID_NDK_ROOT", "NDK_HOME"] {
            if let Ok(path) = env::var(var) {
                let path = PathBuf::from(path);
                if path.exists() {
                    return Ok(path);
                }
            }
        }

        // Try common locations
        let home = env::var("HOME").unwrap_or_default();
        let common_paths = [
            format!("{}/Android/Sdk/ndk-bundle", home),
            format!("{}/Library/Android/sdk/ndk-bundle", home),
            "/opt/android-ndk".to_string(),
            "/usr/local/android-ndk".to_string(),
        ];

        for path in common_paths {
            let path = PathBuf::from(path);
            if path.exists() {
                return Ok(path);
            }
        }

        Err(ToolchainError::NdkNotFound)
    }

    /// Find SDK path from environment variables.
    fn find_sdk_path() -> Option<PathBuf> {
        for var in &["ANDROID_HOME", "ANDROID_SDK_ROOT"] {
            if let Ok(path) = env::var(var) {
                let path = PathBuf::from(path);
                if path.exists() {
                    return Some(path);
                }
            }
        }
        None
    }

    /// Read NDK version from source.properties.
    fn read_ndk_version(ndk_path: &PathBuf) -> Result<String, ToolchainError> {
        let props_file = ndk_path.join("source.properties");
        if props_file.exists() {
            if let Ok(content) = std::fs::read_to_string(&props_file) {
                for line in content.lines() {
                    if line.starts_with("Pkg.Revision") {
                        if let Some(version) = line.split('=').nth(1) {
                            return Ok(version.trim().to_string());
                        }
                    }
                }
            }
        }
        // Fallback: extract from path if possible
        Ok("unknown".to_string())
    }

    /// Find ndk-build executable.
    fn find_ndk_build(ndk_path: &PathBuf) -> Result<PathBuf, ToolchainError> {
        #[cfg(windows)]
        let ndk_build = ndk_path.join("ndk-build.cmd");
        #[cfg(not(windows))]
        let ndk_build = ndk_path.join("ndk-build");

        if ndk_build.exists() {
            Ok(ndk_build)
        } else {
            Err(ToolchainError::NdkBuildNotFound)
        }
    }

    /// Find cmake in system PATH.
    fn find_cmake() -> Option<PathBuf> {
        // Try to find cmake using `which` command
        #[cfg(unix)]
        {
            use std::process::Command;
            let output = Command::new("which")
                .arg("cmake")
                .output()
                .ok()?;
            if output.status.success() {
                let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
                return Some(PathBuf::from(path));
            }
        }
        #[cfg(windows)]
        {
            use std::process::Command;
            let output = Command::new("where")
                .arg("cmake")
                .output()
                .ok()?;
            if output.status.success() {
                let path = String::from_utf8_lossy(&output.stdout)
                    .lines()
                    .next()?
                    .trim()
                    .to_string();
                return Some(PathBuf::from(path));
            }
        }
        None
    }

    /// Get path to clang for a specific ABI.
    pub fn clang_path(&self, abi: AndroidAbi) -> PathBuf {
        let host_tag = Self::host_tag();
        self.ndk_path
            .join("toolchains")
            .join("llvm")
            .join("prebuilt")
            .join(host_tag)
            .join("bin")
            .join(format!("{}{}-clang", abi.triple(), self.api_level))
    }

    /// Get host tag for current platform.
    fn host_tag() -> &'static str {
        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        { "linux-x86_64" }
        #[cfg(all(target_os = "macos", target_arch = "x86_64"))]
        { "darwin-x86_64" }
        #[cfg(all(target_os = "macos", target_arch = "aarch64"))]
        { "darwin-x86_64" } // NDK uses x86_64 even on ARM Mac (Rosetta)
        #[cfg(windows)]
        { "windows-x86_64" }
        #[cfg(not(any(
            all(target_os = "linux", target_arch = "x86_64"),
            all(target_os = "macos", target_arch = "x86_64"),
            all(target_os = "macos", target_arch = "aarch64"),
            windows
        )))]
        { "unknown" }
    }
}

/// Detected iOS toolchain configuration.
#[derive(Debug, Clone)]
pub struct IosToolchain {
    /// Path to Xcode.app
    pub xcode_path: PathBuf,
    /// iOS SDK version (e.g., "17.0")
    pub sdk_version: String,
    /// Minimum deployment target
    pub deployment_target: String,
    /// Path to clang
    pub clang_path: PathBuf,
    /// Path to swift
    pub swift_path: PathBuf,
}

impl IosToolchain {
    /// Detect iOS toolchain using xcrun.
    pub fn detect() -> Result<Self, ToolchainError> {
        // Check if we're on macOS
        #[cfg(not(target_os = "macos"))]
        return Err(ToolchainError::UnsupportedPlatform);

        #[cfg(target_os = "macos")]
        {
            // Find Xcode path
            let xcode_path = Self::find_xcode_path()?;

            // Find clang
            let clang_path = Self::find_clang()?;

            // Find swift
            let swift_path = Self::find_swift()?;

            // Get SDK version
            let sdk_version = Self::get_sdk_version()?;

            // Default deployment target
            let deployment_target = "15.0".to_string();

            Ok(Self {
                xcode_path,
                sdk_version,
                deployment_target,
                clang_path,
                swift_path,
            })
        }
    }

    /// Find Xcode path via xcode-select.
    #[cfg(target_os = "macos")]
    fn find_xcode_path() -> Result<PathBuf, ToolchainError> {
        let output = Command::new("xcode-select")
            .arg("-p")
            .output()
            .map_err(|e| ToolchainError::CommandFailed(e.to_string()))?;

        if !output.status.success() {
            return Err(ToolchainError::XcodeNotFound);
        }

        let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
        Ok(PathBuf::from(path))
    }

    /// Find clang via xcrun.
    #[cfg(target_os = "macos")]
    fn find_clang() -> Result<PathBuf, ToolchainError> {
        let output = Command::new("xcrun")
            .args(["--find", "clang"])
            .output()
            .map_err(|e| ToolchainError::CommandFailed(e.to_string()))?;

        if !output.status.success() {
            return Err(ToolchainError::ClangNotFound);
        }

        let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
        Ok(PathBuf::from(path))
    }

    /// Find swift via xcrun.
    #[cfg(target_os = "macos")]
    fn find_swift() -> Result<PathBuf, ToolchainError> {
        let output = Command::new("xcrun")
            .args(["--find", "swift"])
            .output()
            .map_err(|e| ToolchainError::CommandFailed(e.to_string()))?;

        if !output.status.success() {
            return Err(ToolchainError::SwiftNotFound);
        }

        let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
        Ok(PathBuf::from(path))
    }

    /// Get iOS SDK version.
    #[cfg(target_os = "macos")]
    fn get_sdk_version() -> Result<String, ToolchainError> {
        let output = Command::new("xcrun")
            .args(["--sdk", "iphoneos", "--show-sdk-version"])
            .output()
            .map_err(|e| ToolchainError::CommandFailed(e.to_string()))?;

        if !output.status.success() {
            return Ok("unknown".to_string());
        }

        let version = String::from_utf8_lossy(&output.stdout).trim().to_string();
        Ok(version)
    }

    /// Get SDK path for a specific architecture.
    #[cfg(target_os = "macos")]
    pub fn sdk_path(&self, arch: IosArch) -> Result<PathBuf, ToolchainError> {
        let output = Command::new("xcrun")
            .args(["--sdk", arch.sdk_name(), "--show-sdk-path"])
            .output()
            .map_err(|e| ToolchainError::CommandFailed(e.to_string()))?;

        if !output.status.success() {
            return Err(ToolchainError::XcodeNotFound);
        }

        let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
        Ok(PathBuf::from(path))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_android_abi_strings() {
        assert_eq!(AndroidAbi::Arm64V8a.ndk_abi(), "arm64-v8a");
        assert_eq!(AndroidAbi::ArmeabiV7a.ndk_abi(), "armeabi-v7a");
        assert_eq!(AndroidAbi::X86_64.ndk_abi(), "x86_64");
        assert_eq!(AndroidAbi::X86.ndk_abi(), "x86");
    }

    #[test]
    fn test_android_abi_triples() {
        assert_eq!(AndroidAbi::Arm64V8a.triple(), "aarch64-linux-android");
        assert_eq!(AndroidAbi::ArmeabiV7a.triple(), "armv7a-linux-androideabi");
    }

    #[test]
    fn test_ios_arch_triples() {
        assert_eq!(IosArch::Arm64.triple(), "arm64-apple-ios");
        assert_eq!(IosArch::Arm64Simulator.triple(), "arm64-apple-ios-simulator");
        assert_eq!(IosArch::X86_64Simulator.triple(), "x86_64-apple-ios-simulator");
    }

    #[test]
    fn test_ios_arch_sdk_names() {
        assert_eq!(IosArch::Arm64.sdk_name(), "iphoneos");
        assert_eq!(IosArch::Arm64Simulator.sdk_name(), "iphonesimulator");
        assert_eq!(IosArch::X86_64Simulator.sdk_name(), "iphonesimulator");
    }

    #[test]
    fn test_toolchain_error_display() {
        let errors = vec![
            ToolchainError::NdkNotFound,
            ToolchainError::SdkNotFound,
            ToolchainError::XcodeNotFound,
            ToolchainError::ClangNotFound,
            ToolchainError::InvalidPath("test".to_string()),
            ToolchainError::CommandFailed("test".to_string()),
            ToolchainError::UnsupportedPlatform,
        ];

        for error in errors {
            let display = format!("{}", error);
            assert!(!display.is_empty());
            let _: &dyn std::error::Error = &error;
        }
    }

    #[test]
    fn test_android_abi_all() {
        let all = AndroidAbi::all();
        assert_eq!(all.len(), 4);
        assert!(all.contains(&AndroidAbi::Arm64V8a));
        assert!(all.contains(&AndroidAbi::ArmeabiV7a));
    }
}
