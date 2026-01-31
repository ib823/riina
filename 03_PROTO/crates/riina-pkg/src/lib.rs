// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! riina-pkg — RIINA Package Manager
//!
//! Provides dependency resolution, integrity checking, effect escalation
//! validation, and build orchestration for RIINA packages.
//!
//! # Bahasa Melayu terminology
//!
//! | Bahasa | English | Context |
//! |--------|---------|---------|
//! | pakej | package | Manifest section |
//! | kebergantungan | dependency | Dependencies section |
//! | kesan-dibenarkan | allowed effects | Effect permissions |
//! | nama | name | Package name |
//! | versi | version | Package version |
//! | pengarang | author | Package author |
//! | sasaran | target | Build output dir |
//! | ujian | test | Test directory |
//! | contoh | example | Examples directory |

#![forbid(unsafe_code)]

pub mod build;
pub mod cache;
pub mod cli;
pub mod effects;
pub mod error;
pub mod integrity;
pub mod layout;
pub mod lockfile;
pub mod manifest;
pub mod registry;
pub mod resolve;
pub mod version;
pub mod workspace;

pub use error::{PkgError, Result};
pub use manifest::Manifest;
pub use version::{Version, VersionReq};
