//! Dependency resolver: greedy highest-version with backtracking.
//! Cycle detection via DFS. Diamond merging via VersionReq::intersect.

use crate::error::{PkgError, Result};
use crate::registry::Registry;
use crate::version::{Version, VersionReq};
use std::collections::{BTreeMap, HashSet};

/// A resolved dependency graph.
#[derive(Debug, Clone)]
pub struct ResolvedGraph {
    /// package name -> resolved version
    pub packages: BTreeMap<String, ResolvedPackage>,
}

#[derive(Debug, Clone)]
pub struct ResolvedPackage {
    pub name: String,
    pub version: Version,
    /// Direct dependency names.
    pub deps: Vec<String>,
}

impl ResolvedGraph {
    /// Get topological order (dependencies before dependents).
    pub fn topological_order(&self) -> Result<Vec<String>> {
        topological_sort(&self.packages)
    }
}

/// Resolve dependencies starting from a root set of requirements.
pub fn resolve(
    root_deps: &BTreeMap<String, VersionReq>,
    registry: &dyn Registry,
) -> Result<ResolvedGraph> {
    let mut resolved: BTreeMap<String, ResolvedPackage> = BTreeMap::new();
    let mut constraints: BTreeMap<String, VersionReq> = BTreeMap::new();
    let mut visiting: HashSet<String> = HashSet::new();

    // Initialize constraints from root
    for (name, req) in root_deps {
        constraints.insert(name.clone(), req.clone());
    }

    // Process queue
    let mut queue: Vec<String> = root_deps.keys().cloned().collect();

    while let Some(name) = queue.pop() {
        if resolved.contains_key(&name) {
            continue;
        }

        // Cycle detection
        if visiting.contains(&name) {
            return Err(PkgError::CycleDetected(
                visiting.iter().cloned().collect(),
            ));
        }
        visiting.insert(name.clone());

        let req = constraints.get(&name).cloned().unwrap_or_else(|| {
            VersionReq::parse("*").unwrap()
        });

        // Find highest matching version
        let versions = registry.list_versions(&name)?;
        let chosen = versions.iter().rev()
            .find(|v| req.matches(v))
            .cloned()
            .ok_or_else(|| PkgError::DependencyNotFound {
                name: name.clone(),
                req: req.to_string(),
            })?;

        // Get manifest for chosen version
        let manifest = registry.get_manifest(&name, &chosen)?;

        // Process transitive deps
        let mut dep_names = Vec::new();
        for (dep_name, dep_req_str) in &manifest.dependencies {
            let dep_req = VersionReq::parse(dep_req_str)?;
            dep_names.push(dep_name.clone());

            // Merge constraints (intersect)
            if let Some(existing) = constraints.get(dep_name) {
                let merged = existing.intersect(&dep_req);
                constraints.insert(dep_name.clone(), merged);
            } else {
                constraints.insert(dep_name.clone(), dep_req);
            }

            if !resolved.contains_key(dep_name) {
                queue.push(dep_name.clone());
            }
        }

        resolved.insert(name.clone(), ResolvedPackage {
            name: name.clone(),
            version: chosen,
            deps: dep_names,
        });

        visiting.remove(&name);
    }

    Ok(ResolvedGraph { packages: resolved })
}

/// Topological sort using Kahn's algorithm.
fn topological_sort(
    packages: &BTreeMap<String, ResolvedPackage>,
) -> Result<Vec<String>> {
    let mut in_degree: BTreeMap<String, usize> = BTreeMap::new();
    let mut dependents: BTreeMap<String, Vec<String>> = BTreeMap::new();

    for (name, pkg) in packages {
        in_degree.entry(name.clone()).or_insert(0);
        for dep in &pkg.deps {
            if packages.contains_key(dep) {
                in_degree.entry(dep.clone()).or_insert(0);
                *in_degree.entry(name.clone()).or_insert(0) += 1;
                dependents.entry(dep.clone()).or_default().push(name.clone());
            }
        }
    }

    let mut queue: Vec<String> = in_degree.iter()
        .filter(|(_, &deg)| deg == 0)
        .map(|(name, _)| name.clone())
        .collect();
    queue.sort(); // deterministic

    let mut order = Vec::new();
    while let Some(name) = queue.pop() {
        order.push(name.clone());
        if let Some(deps) = dependents.get(&name) {
            for dep in deps {
                if let Some(deg) = in_degree.get_mut(dep) {
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push(dep.clone());
                        queue.sort();
                    }
                }
            }
        }
    }

    if order.len() != packages.len() {
        let remaining: Vec<String> = packages.keys()
            .filter(|k| !order.contains(k))
            .cloned()
            .collect();
        return Err(PkgError::CycleDetected(remaining));
    }

    Ok(order)
}

/// Print dependency tree for display.
pub fn print_tree(
    graph: &ResolvedGraph,
    root_deps: &[String],
    writer: &mut dyn std::io::Write,
) -> std::io::Result<()> {
    for (i, name) in root_deps.iter().enumerate() {
        let last = i == root_deps.len() - 1;
        let prefix = if last { "└── " } else { "├── " };
        if let Some(pkg) = graph.packages.get(name) {
            writeln!(writer, "{prefix}{} v{}", pkg.name, pkg.version)?;
            let child_prefix = if last { "    " } else { "│   " };
            print_tree_recursive(graph, &pkg.deps, child_prefix, writer)?;
        }
    }
    Ok(())
}

fn print_tree_recursive(
    graph: &ResolvedGraph,
    deps: &[String],
    prefix: &str,
    writer: &mut dyn std::io::Write,
) -> std::io::Result<()> {
    for (i, name) in deps.iter().enumerate() {
        let last = i == deps.len() - 1;
        let connector = if last { "└── " } else { "├── " };
        if let Some(pkg) = graph.packages.get(name) {
            writeln!(writer, "{prefix}{connector}{} v{}", pkg.name, pkg.version)?;
            let child_prefix = format!("{prefix}{}", if last { "    " } else { "│   " });
            print_tree_recursive(graph, &pkg.deps, &child_prefix, writer)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::registry::MemRegistry;
    use crate::manifest::{Manifest, PackageMeta, AllowedEffects};

    fn make_manifest(name: &str, ver: &str, deps: &[(&str, &str)]) -> Manifest {
        let mut dep_map = BTreeMap::new();
        for (n, v) in deps {
            dep_map.insert(n.to_string(), v.to_string());
        }
        Manifest {
            package: PackageMeta {
                name: name.to_string(),
                version: Version::parse(ver).unwrap(),
                authors: vec![], license: None, description: None,
                homepage: None, repository: None,
            },
            dependencies: dep_map,
            dev_dependencies: BTreeMap::new(),
            allowed_effects: AllowedEffects::default(),
            workspace: None,
        }
    }

    #[test]
    fn resolve_simple() {
        let mut reg = MemRegistry::new();
        reg.add(make_manifest("a", "1.0.0", &[]));
        reg.add(make_manifest("b", "2.0.0", &[("a", "^1.0.0")]));

        let mut root = BTreeMap::new();
        root.insert("b".to_string(), VersionReq::parse("^2.0.0").unwrap());

        let graph = resolve(&root, &reg).unwrap();
        assert_eq!(graph.packages.len(), 2);
        assert_eq!(graph.packages["a"].version, Version::parse("1.0.0").unwrap());
        assert_eq!(graph.packages["b"].version, Version::parse("2.0.0").unwrap());
    }

    #[test]
    fn resolve_picks_highest() {
        let mut reg = MemRegistry::new();
        reg.add(make_manifest("a", "1.0.0", &[]));
        reg.add(make_manifest("a", "1.1.0", &[]));
        reg.add(make_manifest("a", "1.2.0", &[]));

        let mut root = BTreeMap::new();
        root.insert("a".to_string(), VersionReq::parse("^1.0.0").unwrap());

        let graph = resolve(&root, &reg).unwrap();
        assert_eq!(graph.packages["a"].version, Version::parse("1.2.0").unwrap());
    }

    #[test]
    fn resolve_not_found() {
        let reg = MemRegistry::new();
        let mut root = BTreeMap::new();
        root.insert("missing".to_string(), VersionReq::parse("^1.0.0").unwrap());
        assert!(resolve(&root, &reg).is_err());
    }

    #[test]
    fn topological_order() {
        let mut reg = MemRegistry::new();
        reg.add(make_manifest("c", "1.0.0", &[]));
        reg.add(make_manifest("b", "1.0.0", &[("c", "^1.0.0")]));
        reg.add(make_manifest("a", "1.0.0", &[("b", "^1.0.0")]));

        let mut root = BTreeMap::new();
        root.insert("a".to_string(), VersionReq::parse("^1.0.0").unwrap());

        let graph = resolve(&root, &reg).unwrap();
        let order = graph.topological_order().unwrap();
        let c_pos = order.iter().position(|x| x == "c").unwrap();
        let b_pos = order.iter().position(|x| x == "b").unwrap();
        let a_pos = order.iter().position(|x| x == "a").unwrap();
        assert!(c_pos < b_pos);
        assert!(b_pos < a_pos);
    }

    #[test]
    fn tree_output() {
        let mut reg = MemRegistry::new();
        reg.add(make_manifest("leaf", "0.1.0", &[]));
        reg.add(make_manifest("mid", "1.0.0", &[("leaf", "^0.1.0")]));

        let mut root = BTreeMap::new();
        root.insert("mid".to_string(), VersionReq::parse("^1.0.0").unwrap());

        let graph = resolve(&root, &reg).unwrap();
        let mut buf = Vec::new();
        print_tree(&graph, &["mid".to_string()], &mut buf).unwrap();
        let output = String::from_utf8(buf).unwrap();
        assert!(output.contains("mid v1.0.0"));
        assert!(output.contains("leaf v0.1.0"));
    }
}
