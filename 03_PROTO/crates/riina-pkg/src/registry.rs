//! Package registry: trait + filesystem-based implementation.

use crate::error::{PkgError, Result};
use crate::manifest::Manifest;
use crate::version::Version;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// A package registry that can list versions and retrieve packages.
pub trait Registry {
    /// List all available versions of a package, sorted ascending.
    fn list_versions(&self, name: &str) -> Result<Vec<Version>>;

    /// Get the manifest for a specific package version.
    fn get_manifest(&self, name: &str, version: &Version) -> Result<Manifest>;

    /// Get the root path for an installed package version.
    fn package_path(&self, name: &str, version: &Version) -> PathBuf;

    /// Check if a package version exists.
    fn exists(&self, name: &str, version: &Version) -> bool;
}

/// Filesystem-based registry.
///
/// Layout: `<root>/<name>/<version>/riina.toml`
pub struct FsRegistry {
    root: PathBuf,
}

impl FsRegistry {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Self { root: root.into() }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Publish a package directory to the registry.
    pub fn publish(&self, name: &str, version: &Version, source_dir: &Path) -> Result<()> {
        let dest = self.package_path(name, version);
        if dest.exists() {
            return Err(PkgError::AlreadyPublished {
                name: name.to_string(),
                version: version.to_string(),
            });
        }
        copy_dir_recursive(source_dir, &dest)?;
        Ok(())
    }
}

impl Registry for FsRegistry {
    fn list_versions(&self, name: &str) -> Result<Vec<Version>> {
        let pkg_dir = self.root.join(name);
        if !pkg_dir.is_dir() {
            return Ok(Vec::new());
        }
        let mut versions = Vec::new();
        let entries = std::fs::read_dir(&pkg_dir)
            .map_err(|e| PkgError::io(&pkg_dir, e))?;
        for entry in entries {
            let entry = entry.map_err(|e| PkgError::io(&pkg_dir, e))?;
            if entry.path().is_dir() {
                if let Some(name) = entry.file_name().to_str() {
                    if let Ok(v) = Version::parse(name) {
                        versions.push(v);
                    }
                }
            }
        }
        versions.sort();
        Ok(versions)
    }

    fn get_manifest(&self, name: &str, version: &Version) -> Result<Manifest> {
        let path = self.package_path(name, version).join("riina.toml");
        Manifest::from_file(&path)
    }

    fn package_path(&self, name: &str, version: &Version) -> PathBuf {
        self.root.join(name).join(version.to_string())
    }

    fn exists(&self, name: &str, version: &Version) -> bool {
        self.package_path(name, version).join("riina.toml").is_file()
    }
}

fn copy_dir_recursive(src: &Path, dst: &Path) -> Result<()> {
    std::fs::create_dir_all(dst).map_err(|e| PkgError::io(dst, e))?;
    let entries = std::fs::read_dir(src).map_err(|e| PkgError::io(src, e))?;
    for entry in entries {
        let entry = entry.map_err(|e| PkgError::io(src, e))?;
        let ty = entry.file_type().map_err(|e| PkgError::io(entry.path(), e))?;
        let dest_path = dst.join(entry.file_name());
        if ty.is_dir() {
            copy_dir_recursive(&entry.path(), &dest_path)?;
        } else {
            std::fs::copy(entry.path(), &dest_path)
                .map_err(|e| PkgError::io(&dest_path, e))?;
        }
    }
    Ok(())
}

/// In-memory registry for testing.
#[derive(Default)]
pub struct MemRegistry {
    packages: BTreeMap<String, BTreeMap<Version, Manifest>>,
}

impl MemRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add(&mut self, manifest: Manifest) {
        let name = manifest.package.name.clone();
        let version = manifest.package.version.clone();
        self.packages.entry(name).or_default().insert(version, manifest);
    }
}

impl Registry for MemRegistry {
    fn list_versions(&self, name: &str) -> Result<Vec<Version>> {
        Ok(self.packages.get(name)
            .map(|m| m.keys().cloned().collect())
            .unwrap_or_default())
    }

    fn get_manifest(&self, name: &str, version: &Version) -> Result<Manifest> {
        self.packages.get(name)
            .and_then(|m| m.get(version))
            .cloned()
            .ok_or_else(|| PkgError::DependencyNotFound {
                name: name.to_string(),
                req: version.to_string(),
            })
    }

    fn package_path(&self, name: &str, version: &Version) -> PathBuf {
        PathBuf::from(format!("/mem/{name}/{version}"))
    }

    fn exists(&self, name: &str, version: &Version) -> bool {
        self.packages.get(name).is_some_and(|m| m.contains_key(version))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifest::{PackageMeta, AllowedEffects};

    fn dummy_manifest(name: &str, ver: &str) -> Manifest {
        Manifest {
            package: PackageMeta {
                name: name.to_string(),
                version: Version::parse(ver).unwrap(),
                authors: vec![],
                license: None,
                description: None,
                homepage: None,
                repository: None,
            },
            dependencies: BTreeMap::new(),
            dev_dependencies: BTreeMap::new(),
            allowed_effects: AllowedEffects::default(),
            workspace: None,
        }
    }

    #[test]
    fn mem_registry() {
        let mut reg = MemRegistry::new();
        reg.add(dummy_manifest("foo", "1.0.0"));
        reg.add(dummy_manifest("foo", "1.1.0"));
        reg.add(dummy_manifest("bar", "0.1.0"));

        let vers = reg.list_versions("foo").unwrap();
        assert_eq!(vers.len(), 2);
        assert!(reg.exists("foo", &Version::parse("1.0.0").unwrap()));
        assert!(!reg.exists("baz", &Version::parse("1.0.0").unwrap()));
    }
}
