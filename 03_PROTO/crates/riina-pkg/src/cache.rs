// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Package cache: ~/.riina/cache/<name>/<version>/

use crate::error::{PkgError, Result};
use crate::version::Version;
use std::path::{Path, PathBuf};

/// Cache directory manager.
pub struct Cache {
    root: PathBuf,
}

impl Cache {
    /// Create with explicit root.
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    /// Create with default location (~/.riina/cache).
    pub fn default_location() -> Result<Self> {
        let home = std::env::var("HOME")
            .or_else(|_| std::env::var("USERPROFILE"))
            .map_err(|_| PkgError::Other("cannot determine home directory".into()))?;
        Ok(Self::new(PathBuf::from(home).join(".riina").join("cache")))
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Path for a cached package.
    pub fn package_path(&self, name: &str, version: &Version) -> PathBuf {
        self.root.join(name).join(version.to_string())
    }

    /// Check if a package is cached.
    pub fn has(&self, name: &str, version: &Version) -> bool {
        self.package_path(name, version).is_dir()
    }

    /// Store a package directory in cache.
    pub fn put(&self, name: &str, version: &Version, source: &Path) -> Result<()> {
        let dest = self.package_path(name, version);
        if dest.exists() {
            return Ok(()); // already cached
        }
        copy_dir(source, &dest)
    }

    /// Remove a specific cached version.
    pub fn remove(&self, name: &str, version: &Version) -> Result<()> {
        let path = self.package_path(name, version);
        if path.exists() {
            std::fs::remove_dir_all(&path).map_err(|e| PkgError::io(&path, e))?;
        }
        Ok(())
    }

    /// Clean entire cache.
    pub fn clean(&self) -> Result<()> {
        if self.root.exists() {
            std::fs::remove_dir_all(&self.root).map_err(|e| PkgError::io(&self.root, e))?;
        }
        Ok(())
    }

    /// List all cached packages.
    pub fn list(&self) -> Result<Vec<(String, Version)>> {
        let mut result = Vec::new();
        if !self.root.is_dir() {
            return Ok(result);
        }
        let entries = std::fs::read_dir(&self.root)
            .map_err(|e| PkgError::io(&self.root, e))?;
        for entry in entries {
            let entry = entry.map_err(|e| PkgError::io(&self.root, e))?;
            if !entry.path().is_dir() {
                continue;
            }
            let pkg_name = entry.file_name().to_string_lossy().to_string();
            let versions = std::fs::read_dir(entry.path())
                .map_err(|e| PkgError::io(entry.path(), e))?;
            for ver_entry in versions {
                let ver_entry = ver_entry.map_err(|e| PkgError::io(entry.path(), e))?;
                if ver_entry.path().is_dir() {
                    if let Some(ver_str) = ver_entry.file_name().to_str() {
                        if let Ok(v) = Version::parse(ver_str) {
                            result.push((pkg_name.clone(), v));
                        }
                    }
                }
            }
        }
        result.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
        Ok(result)
    }
}

fn copy_dir(src: &Path, dst: &Path) -> Result<()> {
    std::fs::create_dir_all(dst).map_err(|e| PkgError::io(dst, e))?;
    let entries = std::fs::read_dir(src).map_err(|e| PkgError::io(src, e))?;
    for entry in entries {
        let entry = entry.map_err(|e| PkgError::io(src, e))?;
        let ty = entry.file_type().map_err(|e| PkgError::io(entry.path(), e))?;
        let dest_path = dst.join(entry.file_name());
        if ty.is_dir() {
            copy_dir(&entry.path(), &dest_path)?;
        } else {
            std::fs::copy(entry.path(), &dest_path)
                .map_err(|e| PkgError::io(&dest_path, e))?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cache_operations() {
        let tmp = std::env::temp_dir().join("riina-pkg-cache-test");
        let _ = std::fs::remove_dir_all(&tmp);

        let cache = Cache::new(&tmp);
        let v = Version::new(1, 0, 0);

        assert!(!cache.has("foo", &v));

        // Create a source dir
        let src = tmp.join("_src");
        std::fs::create_dir_all(&src).unwrap();
        std::fs::write(src.join("lib.rii"), "// test").unwrap();

        cache.put("foo", &v, &src).unwrap();
        assert!(cache.has("foo", &v));

        let list = cache.list().unwrap();
        assert_eq!(list.len(), 1);
        assert_eq!(list[0].0, "foo");

        cache.remove("foo", &v).unwrap();
        assert!(!cache.has("foo", &v));

        let _ = std::fs::remove_dir_all(&tmp);
    }
}
