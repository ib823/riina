//! Build orchestration: topological order build of resolved packages.

use crate::error::{PkgError, Result};
use crate::resolve::ResolvedGraph;
use std::path::{Path, PathBuf};

/// Build plan entry.
#[derive(Debug, Clone)]
pub struct BuildStep {
    pub name: String,
    pub source_dir: PathBuf,
    pub output_dir: PathBuf,
}

/// Build configuration.
#[derive(Debug, Clone)]
pub struct BuildConfig {
    pub project_root: PathBuf,
    pub target_dir: PathBuf,
    pub registry_root: PathBuf,
}

impl BuildConfig {
    pub fn new(project_root: impl Into<PathBuf>) -> Self {
        let root: PathBuf = project_root.into();
        let target_dir = root.join("sasaran");
        Self {
            project_root: root,
            target_dir,
            registry_root: PathBuf::new(),
        }
    }

    pub fn with_registry(mut self, root: impl Into<PathBuf>) -> Self {
        self.registry_root = root.into();
        self
    }
}

/// Generate a build plan from a resolved graph.
pub fn build_plan(
    graph: &ResolvedGraph,
    config: &BuildConfig,
    root_package: &str,
) -> Result<Vec<BuildStep>> {
    let order = graph.topological_order()?;
    let mut steps = Vec::new();

    for name in &order {
        let pkg = graph.packages.get(name).ok_or_else(|| {
            PkgError::Other(format!("package '{name}' not in graph"))
        })?;

        let source_dir = if name == root_package {
            config.project_root.clone()
        } else {
            config.registry_root
                .join(&pkg.name)
                .join(pkg.version.to_string())
        };

        let output_dir = config.target_dir.join(&pkg.name);

        steps.push(BuildStep {
            name: pkg.name.clone(),
            source_dir,
            output_dir,
        });
    }

    Ok(steps)
}

/// Execute a build plan (compile each step).
pub fn execute_build(steps: &[BuildStep]) -> Result<()> {
    for step in steps {
        // Create output directory
        std::fs::create_dir_all(&step.output_dir)
            .map_err(|e| PkgError::io(&step.output_dir, e))?;

        // Find .rii source files
        let src_dir = step.source_dir.join("src");
        if !src_dir.is_dir() {
            continue;
        }

        let entries = std::fs::read_dir(&src_dir)
            .map_err(|e| PkgError::io(&src_dir, e))?;

        let mut has_sources = false;
        for entry in entries {
            let entry = entry.map_err(|e| PkgError::io(&src_dir, e))?;
            let path = entry.path();
            if path.extension().and_then(|e| e.to_str()) == Some("rii") {
                has_sources = true;
                // Copy source to output (placeholder for actual compilation)
                let dest = step.output_dir.join(entry.file_name());
                std::fs::copy(&path, &dest)
                    .map_err(|e| PkgError::io(&dest, e))?;
            }
        }

        if has_sources {
            eprintln!("  Built: {}", step.name);
        }
    }
    Ok(())
}

/// Clean build artifacts.
pub fn clean(target_dir: &Path) -> Result<()> {
    if target_dir.is_dir() {
        std::fs::remove_dir_all(target_dir)
            .map_err(|e| PkgError::io(target_dir, e))?;
        eprintln!("Cleaned: {}", target_dir.display());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resolve::{ResolvedGraph, ResolvedPackage};
    use crate::version::Version;
    use std::collections::BTreeMap;

    #[test]
    fn build_plan_order() {
        let mut packages = BTreeMap::new();
        packages.insert("leaf".to_string(), ResolvedPackage {
            name: "leaf".to_string(),
            version: Version::new(1, 0, 0),
            deps: vec![],
        });
        packages.insert("root".to_string(), ResolvedPackage {
            name: "root".to_string(),
            version: Version::new(0, 1, 0),
            deps: vec!["leaf".to_string()],
        });

        let graph = ResolvedGraph { packages };
        let config = BuildConfig::new("/project").with_registry("/reg");
        let steps = build_plan(&graph, &config, "root").unwrap();

        assert_eq!(steps.len(), 2);
        assert_eq!(steps[0].name, "leaf");
        assert_eq!(steps[1].name, "root");
        assert_eq!(steps[1].source_dir, PathBuf::from("/project"));
    }
}
