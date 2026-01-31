// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! Workspace (monorepo) support.
//!
//! A workspace root has `[workspace]` in its riina.toml with `members = [...]`.
//! Members are subdirectories, each with their own riina.toml.

use crate::error::{PkgError, Result};
use crate::manifest::Manifest;
use crate::version::VersionReq;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// A resolved workspace.
#[derive(Debug)]
pub struct Workspace {
    pub root: PathBuf,
    pub root_manifest: Manifest,
    pub members: Vec<WorkspaceMember>,
}

#[derive(Debug)]
pub struct WorkspaceMember {
    pub path: PathBuf,
    pub manifest: Manifest,
}

impl Workspace {
    /// Discover workspace from a directory (walks up to find workspace root).
    pub fn discover(start: &Path) -> Result<Option<Self>> {
        let manifest_path = start.join("riina.toml");
        if !manifest_path.is_file() {
            return Ok(None);
        }
        let manifest = Manifest::from_file(&manifest_path)?;
        if manifest.workspace.is_none() {
            return Ok(None);
        }
        Self::load(start)
    }

    /// Load a workspace from its root directory.
    pub fn load(root: &Path) -> Result<Option<Self>> {
        let manifest_path = root.join("riina.toml");
        let root_manifest = Manifest::from_file(&manifest_path)?;

        let ws_config = match &root_manifest.workspace {
            Some(ws) => ws,
            None => return Ok(None),
        };

        let mut members = Vec::new();
        for member_path in &ws_config.members {
            let member_dir = root.join(member_path);
            let member_manifest_path = member_dir.join("riina.toml");
            if !member_manifest_path.is_file() {
                return Err(PkgError::Workspace(
                    format!("member '{}' has no riina.toml", member_path)
                ));
            }
            let manifest = Manifest::from_file(&member_manifest_path)?;
            members.push(WorkspaceMember {
                path: member_dir,
                manifest,
            });
        }

        Ok(Some(Self {
            root: root.to_path_buf(),
            root_manifest,
            members,
        }))
    }

    /// Collect all unique dependencies across all members.
    pub fn all_dependencies(&self) -> Result<BTreeMap<String, VersionReq>> {
        let mut deps: BTreeMap<String, VersionReq> = BTreeMap::new();

        // Root deps
        for (name, req_str) in &self.root_manifest.dependencies {
            deps.insert(name.clone(), VersionReq::parse(req_str)?);
        }

        // Member deps (intersect if shared)
        for member in &self.members {
            for (name, req_str) in &member.manifest.dependencies {
                let req = VersionReq::parse(req_str)?;
                if let Some(existing) = deps.get(name) {
                    deps.insert(name.clone(), existing.intersect(&req));
                } else {
                    deps.insert(name.clone(), req);
                }
            }
        }

        Ok(deps)
    }

    /// List member names.
    pub fn member_names(&self) -> Vec<String> {
        self.members.iter()
            .map(|m| m.manifest.package.name.clone())
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn discover_no_workspace() {
        let tmp = std::env::temp_dir().join("riina-ws-test-none");
        let _ = std::fs::remove_dir_all(&tmp);
        std::fs::create_dir_all(&tmp).unwrap();
        std::fs::write(tmp.join("riina.toml"), "[pakej]\nnama = \"x\"\nversi = \"0.1.0\"\n").unwrap();
        let ws = Workspace::discover(&tmp).unwrap();
        assert!(ws.is_none());
        let _ = std::fs::remove_dir_all(&tmp);
    }

    #[test]
    fn load_workspace() {
        let tmp = std::env::temp_dir().join("riina-ws-test-load");
        let _ = std::fs::remove_dir_all(&tmp);
        std::fs::create_dir_all(tmp.join("pkg-a")).unwrap();

        std::fs::write(tmp.join("riina.toml"), r#"
[pakej]
nama = "root"
versi = "0.1.0"

[workspace]
members = ["pkg-a"]
"#).unwrap();

        std::fs::write(tmp.join("pkg-a").join("riina.toml"), r#"
[pakej]
nama = "pkg-a"
versi = "0.2.0"
"#).unwrap();

        let ws = Workspace::load(&tmp).unwrap().unwrap();
        assert_eq!(ws.members.len(), 1);
        assert_eq!(ws.member_names(), vec!["pkg-a"]);

        let _ = std::fs::remove_dir_all(&tmp);
    }
}
