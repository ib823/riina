// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! Package directory layout conventions.

use std::path::{Path, PathBuf};

/// Standard RIINA package directory layout.
pub struct Layout {
    root: PathBuf,
}

impl Layout {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    /// riina.toml
    pub fn manifest(&self) -> PathBuf {
        self.root.join("riina.toml")
    }

    /// riina.lock
    pub fn lockfile(&self) -> PathBuf {
        self.root.join("riina.lock")
    }

    /// src/ directory
    pub fn src_dir(&self) -> PathBuf {
        self.root.join("src")
    }

    /// src/lib.rii (library entry point)
    pub fn lib_entry(&self) -> PathBuf {
        self.root.join("src").join("lib.rii")
    }

    /// src/utama.rii (binary entry point — "utama" = main)
    pub fn bin_entry(&self) -> PathBuf {
        self.root.join("src").join("utama.rii")
    }

    /// ujian/ (test directory — "ujian" = test)
    pub fn test_dir(&self) -> PathBuf {
        self.root.join("ujian")
    }

    /// contoh/ (examples directory — "contoh" = example)
    pub fn examples_dir(&self) -> PathBuf {
        self.root.join("contoh")
    }

    /// sasaran/ (build output directory — "sasaran" = target)
    pub fn target_dir(&self) -> PathBuf {
        self.root.join("sasaran")
    }

    /// Root directory.
    pub fn root(&self) -> &Path {
        &self.root
    }
}

/// Create scaffold for a new package.
pub fn create_scaffold(root: &Path, name: &str) -> crate::error::Result<()> {
    use crate::error::PkgError;
    let layout = Layout::new(root);

    std::fs::create_dir_all(layout.src_dir())
        .map_err(|e| PkgError::io(layout.src_dir(), e))?;

    // Write riina.toml
    let manifest = format!(
        r#"[pakej]
nama = "{name}"
versi = "0.1.0"
pengarang = []
lesen = "MIT"
keterangan = ""

[kebergantungan]

[dev-kebergantungan]

[kesan-dibenarkan]
IO = false
Crypto = false
Network = false
System = false
Product = false
"#
    );
    std::fs::write(layout.manifest(), manifest)
        .map_err(|e| PkgError::io(layout.manifest(), e))?;

    // Write src/lib.rii
    let lib_content = format!(
        "// {name} — RIINA package\n\nfungsi utama() -> Nombor {{\n    pulang 0;\n}}\n"
    );
    std::fs::write(layout.lib_entry(), lib_content)
        .map_err(|e| PkgError::io(layout.lib_entry(), e))?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn layout_paths() {
        let l = Layout::new("/project");
        assert_eq!(l.manifest(), PathBuf::from("/project/riina.toml"));
        assert_eq!(l.lockfile(), PathBuf::from("/project/riina.lock"));
        assert_eq!(l.lib_entry(), PathBuf::from("/project/src/lib.rii"));
        assert_eq!(l.bin_entry(), PathBuf::from("/project/src/utama.rii"));
        assert_eq!(l.test_dir(), PathBuf::from("/project/ujian"));
        assert_eq!(l.examples_dir(), PathBuf::from("/project/contoh"));
        assert_eq!(l.target_dir(), PathBuf::from("/project/sasaran"));
    }
}
