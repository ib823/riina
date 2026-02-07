// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Platform-Conditional Standard Library
//!
//! Abstracts POSIX assumptions so the standard library works on all targets.
//! Each platform provides a different set of capabilities, and the codegen
//! layer emits platform-appropriate code based on the target.
//!
//! # Platform Mapping
//!
//! | RIINA Capability | Native (POSIX) | WASM | Android | iOS |
//! |------------------|----------------|------|---------|-----|
//! | File I/O         | stdio/POSIX    | OPFS/IndexedDB | ContentProvider | FileManager |
//! | Network          | sockets        | fetch API | OkHttp | URLSession |
//! | Console          | stdout/stderr  | console.log | Logcat | NSLog |
//! | Crypto           | OpenSSL/native | Web Crypto | Android Keystore | Security.framework |
//! | Time             | clock_gettime  | performance.now | SystemClock | CFAbsoluteTimeGetCurrent |
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST

use crate::backend::Target;

/// Platform capability — what a target platform can do.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlatformCapability {
    /// File I/O (read/write files)
    FileIO,
    /// Network I/O (HTTP, sockets)
    Network,
    /// Console output (print/log)
    Console,
    /// Cryptographic operations
    Crypto,
    /// System clock / timers
    Time,
    /// Process spawning
    Process,
    /// Shared memory / threading
    Threading,
    /// Camera / sensors (mobile)
    Sensors,
    /// Biometric authentication (mobile)
    Biometrics,
    /// Push notifications (mobile)
    PushNotifications,
}

/// Platform-specific implementation strategy for a capability.
#[derive(Debug, Clone)]
pub enum PlatformImpl {
    /// Native POSIX implementation (C standard library)
    Posix(&'static str),
    /// WASM import (JavaScript API binding)
    WasmImport(&'static str),
    /// Android JNI call
    AndroidJni(&'static str),
    /// iOS Objective-C / Swift bridge
    IosBridge(&'static str),
    /// Not available on this platform
    Unavailable,
}

/// Get the implementation strategy for a capability on a given target.
pub fn platform_impl(target: Target, cap: PlatformCapability) -> PlatformImpl {
    match (target, cap) {
        // === Native (POSIX) ===
        (Target::Native, PlatformCapability::FileIO) => PlatformImpl::Posix("stdio.h"),
        (Target::Native, PlatformCapability::Network) => PlatformImpl::Posix("sys/socket.h"),
        (Target::Native, PlatformCapability::Console) => PlatformImpl::Posix("stdio.h"),
        (Target::Native, PlatformCapability::Crypto) => PlatformImpl::Posix("riina_crypto.h"),
        (Target::Native, PlatformCapability::Time) => PlatformImpl::Posix("time.h"),
        (Target::Native, PlatformCapability::Process) => PlatformImpl::Posix("unistd.h"),
        (Target::Native, PlatformCapability::Threading) => PlatformImpl::Posix("pthread.h"),
        (Target::Native, PlatformCapability::Sensors) => PlatformImpl::Unavailable,
        (Target::Native, PlatformCapability::Biometrics) => PlatformImpl::Unavailable,
        (Target::Native, PlatformCapability::PushNotifications) => PlatformImpl::Unavailable,

        // === WASM ===
        (Target::Wasm32 | Target::Wasm64, PlatformCapability::FileIO) => {
            PlatformImpl::WasmImport("riina_fs_read / riina_fs_write (OPFS)")
        }
        (Target::Wasm32 | Target::Wasm64, PlatformCapability::Network) => {
            PlatformImpl::WasmImport("riina_fetch (fetch API)")
        }
        (Target::Wasm32 | Target::Wasm64, PlatformCapability::Console) => {
            PlatformImpl::WasmImport("riina_cetak (console.log)")
        }
        (Target::Wasm32 | Target::Wasm64, PlatformCapability::Crypto) => {
            PlatformImpl::WasmImport("riina_crypto (Web Crypto API)")
        }
        (Target::Wasm32 | Target::Wasm64, PlatformCapability::Time) => {
            PlatformImpl::WasmImport("riina_masa (performance.now)")
        }
        (Target::Wasm32 | Target::Wasm64, PlatformCapability::Process) => PlatformImpl::Unavailable,
        (Target::Wasm32 | Target::Wasm64, PlatformCapability::Threading) => {
            PlatformImpl::WasmImport("SharedArrayBuffer + Atomics")
        }
        (Target::Wasm32 | Target::Wasm64, PlatformCapability::Sensors) => PlatformImpl::Unavailable,
        (Target::Wasm32 | Target::Wasm64, PlatformCapability::Biometrics) => {
            PlatformImpl::WasmImport("WebAuthn API")
        }
        (Target::Wasm32 | Target::Wasm64, PlatformCapability::PushNotifications) => {
            PlatformImpl::WasmImport("Push API + Service Worker")
        }

        // === Android ===
        (Target::AndroidArm64, PlatformCapability::FileIO) => {
            PlatformImpl::AndroidJni("android.content.ContentResolver")
        }
        (Target::AndroidArm64, PlatformCapability::Network) => {
            PlatformImpl::AndroidJni("java.net.HttpURLConnection")
        }
        (Target::AndroidArm64, PlatformCapability::Console) => {
            PlatformImpl::AndroidJni("android.util.Log")
        }
        (Target::AndroidArm64, PlatformCapability::Crypto) => {
            PlatformImpl::AndroidJni("android.security.keystore.KeyGenParameterSpec")
        }
        (Target::AndroidArm64, PlatformCapability::Time) => {
            PlatformImpl::AndroidJni("android.os.SystemClock")
        }
        (Target::AndroidArm64, PlatformCapability::Process) => PlatformImpl::Unavailable,
        (Target::AndroidArm64, PlatformCapability::Threading) => {
            PlatformImpl::AndroidJni("java.lang.Thread")
        }
        (Target::AndroidArm64, PlatformCapability::Sensors) => {
            PlatformImpl::AndroidJni("android.hardware.SensorManager")
        }
        (Target::AndroidArm64, PlatformCapability::Biometrics) => {
            PlatformImpl::AndroidJni("androidx.biometric.BiometricPrompt")
        }
        (Target::AndroidArm64, PlatformCapability::PushNotifications) => {
            PlatformImpl::AndroidJni("com.google.firebase.messaging.FirebaseMessaging")
        }

        // === iOS ===
        (Target::IosArm64, PlatformCapability::FileIO) => {
            PlatformImpl::IosBridge("FileManager")
        }
        (Target::IosArm64, PlatformCapability::Network) => {
            PlatformImpl::IosBridge("URLSession")
        }
        (Target::IosArm64, PlatformCapability::Console) => {
            PlatformImpl::IosBridge("os_log")
        }
        (Target::IosArm64, PlatformCapability::Crypto) => {
            PlatformImpl::IosBridge("Security.framework / CryptoKit")
        }
        (Target::IosArm64, PlatformCapability::Time) => {
            PlatformImpl::IosBridge("CFAbsoluteTimeGetCurrent")
        }
        (Target::IosArm64, PlatformCapability::Process) => PlatformImpl::Unavailable,
        (Target::IosArm64, PlatformCapability::Threading) => {
            PlatformImpl::IosBridge("DispatchQueue")
        }
        (Target::IosArm64, PlatformCapability::Sensors) => {
            PlatformImpl::IosBridge("CoreMotion")
        }
        (Target::IosArm64, PlatformCapability::Biometrics) => {
            PlatformImpl::IosBridge("LocalAuthentication / LAContext")
        }
        (Target::IosArm64, PlatformCapability::PushNotifications) => {
            PlatformImpl::IosBridge("UserNotifications.framework")
        }
    }
}

/// Check if a capability is available on the given target.
pub fn is_available(target: Target, cap: PlatformCapability) -> bool {
    !matches!(platform_impl(target, cap), PlatformImpl::Unavailable)
}

/// Get all capabilities available on a given target.
pub fn available_capabilities(target: Target) -> Vec<PlatformCapability> {
    use PlatformCapability::*;
    let all = [
        FileIO, Network, Console, Crypto, Time, Process,
        Threading, Sensors, Biometrics, PushNotifications,
    ];
    all.into_iter().filter(|cap| is_available(target, *cap)).collect()
}

/// C preprocessor conditional for platform-specific code emission.
///
/// Used by the C backend when emitting platform-specific stdlib functions.
pub fn c_platform_guard(target: Target) -> &'static str {
    match target {
        Target::Native => "",
        Target::Wasm32 | Target::Wasm64 => "#ifdef __EMSCRIPTEN__",
        Target::AndroidArm64 => "#ifdef __ANDROID__",
        Target::IosArm64 => "#if defined(__APPLE__) && defined(TARGET_OS_IOS)",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_native_has_file_io() {
        assert!(is_available(Target::Native, PlatformCapability::FileIO));
    }

    #[test]
    fn test_native_no_sensors() {
        assert!(!is_available(Target::Native, PlatformCapability::Sensors));
    }

    #[test]
    fn test_wasm_has_console() {
        assert!(is_available(Target::Wasm32, PlatformCapability::Console));
    }

    #[test]
    fn test_wasm_no_process() {
        assert!(!is_available(Target::Wasm32, PlatformCapability::Process));
    }

    #[test]
    fn test_android_has_sensors() {
        assert!(is_available(Target::AndroidArm64, PlatformCapability::Sensors));
    }

    #[test]
    fn test_ios_has_biometrics() {
        assert!(is_available(Target::IosArm64, PlatformCapability::Biometrics));
    }

    #[test]
    fn test_available_capabilities_count() {
        let native_caps = available_capabilities(Target::Native);
        assert!(native_caps.len() >= 6);
        let wasm_caps = available_capabilities(Target::Wasm32);
        assert!(wasm_caps.len() >= 5);
        let android_caps = available_capabilities(Target::AndroidArm64);
        assert!(android_caps.len() >= 8);
    }

    #[test]
    fn test_platform_impl_variant() {
        let impl_ = platform_impl(Target::Native, PlatformCapability::FileIO);
        assert!(matches!(impl_, PlatformImpl::Posix(_)));

        let impl_ = platform_impl(Target::Wasm32, PlatformCapability::Console);
        assert!(matches!(impl_, PlatformImpl::WasmImport(_)));

        let impl_ = platform_impl(Target::AndroidArm64, PlatformCapability::Sensors);
        assert!(matches!(impl_, PlatformImpl::AndroidJni(_)));

        let impl_ = platform_impl(Target::IosArm64, PlatformCapability::Crypto);
        assert!(matches!(impl_, PlatformImpl::IosBridge(_)));
    }

    #[test]
    fn test_c_platform_guard() {
        assert_eq!(c_platform_guard(Target::Native), "");
        assert!(c_platform_guard(Target::AndroidArm64).contains("__ANDROID__"));
    }
}
