//! CLI subcommand dispatch for `riinac pkg <command>`.

use crate::error::{PkgError, Result};
use crate::effects::EffectPermissions;
use crate::integrity::sha256_hex;
use crate::layout::{self, Layout};
use crate::lockfile::{Lockfile, LockedPackage};
use crate::manifest::Manifest;
use crate::registry::{FsRegistry, Registry};
use crate::resolve;
use crate::workspace::Workspace;
use std::path::PathBuf;

/// Run a pkg subcommand. Args should be everything after `riinac pkg`.
pub fn run(args: &[String]) -> Result<()> {
    if args.is_empty() {
        return Err(PkgError::Other(usage_string()));
    }

    match args[0].as_str() {
        "init" => cmd_init(args.get(1).map(|s| s.as_str())),
        "add" => {
            let name = args.get(1).ok_or_else(|| PkgError::Other("usage: riinac pkg add <dep> [version]".into()))?;
            let version = args.get(2).map(|s| s.as_str()).unwrap_or("*");
            cmd_add(name, version)
        }
        "remove" => {
            let name = args.get(1).ok_or_else(|| PkgError::Other("usage: riinac pkg remove <dep>".into()))?;
            cmd_remove(name)
        }
        "update" => cmd_update(args.get(1).map(|s| s.as_str())),
        "lock" => cmd_lock(),
        "build" => cmd_build(),
        "publish" => cmd_publish(),
        "list" => cmd_list(),
        "tree" => cmd_tree(),
        "clean" => cmd_clean(),
        other => Err(PkgError::Other(format!("unknown pkg command: {other}\n{}", usage_string()))),
    }
}

fn usage_string() -> String {
    "Usage: riinac pkg <command>\n\n\
     Commands:\n\
     \x20 init [name]       Create riina.toml + scaffold\n\
     \x20 add <dep> [ver]   Add dependency\n\
     \x20 remove <dep>      Remove dependency\n\
     \x20 update [dep]      Update dependencies\n\
     \x20 lock              Resolve and write riina.lock\n\
     \x20 build             Build package + deps\n\
     \x20 publish           Publish to registry\n\
     \x20 list              List dependencies\n\
     \x20 tree              Print dependency tree\n\
     \x20 clean             Clean cache and build artifacts".to_string()
}

fn find_project_root() -> Result<PathBuf> {
    let cwd = std::env::current_dir()
        .map_err(|e| PkgError::io(".", e))?;
    let manifest = cwd.join("riina.toml");
    if manifest.is_file() {
        Ok(cwd)
    } else {
        Err(PkgError::Other("no riina.toml found in current directory".into()))
    }
}

fn registry_root() -> PathBuf {
    std::env::var("RIINA_REGISTRY")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            let home = std::env::var("HOME")
                .or_else(|_| std::env::var("USERPROFILE"))
                .unwrap_or_else(|_| ".".into());
            PathBuf::from(home).join(".riina").join("registry")
        })
}

fn cmd_init(name: Option<&str>) -> Result<()> {
    let cwd = std::env::current_dir().map_err(|e| PkgError::io(".", e))?;
    let pkg_name = name.unwrap_or_else(|| {
        cwd.file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("pakej-baru")
    });
    layout::create_scaffold(&cwd, pkg_name)?;
    eprintln!("Created package '{}' in {}", pkg_name, cwd.display());
    Ok(())
}

fn cmd_add(name: &str, version: &str) -> Result<()> {
    let root = find_project_root()?;
    let manifest_path = root.join("riina.toml");
    let mut source = std::fs::read_to_string(&manifest_path)
        .map_err(|e| PkgError::io(&manifest_path, e))?;

    // Find [kebergantungan] section and add entry
    if let Some(pos) = source.find("[kebergantungan]") {
        let insert_pos = source[pos..].find('\n').map(|p| pos + p + 1).unwrap_or(source.len());
        let line = format!("{} = \"{}\"\n", name, version);
        source.insert_str(insert_pos, &line);
    } else {
        source.push_str(&format!("\n[kebergantungan]\n{} = \"{}\"\n", name, version));
    }

    std::fs::write(&manifest_path, &source)
        .map_err(|e| PkgError::io(&manifest_path, e))?;
    eprintln!("Added {} = \"{}\"", name, version);
    Ok(())
}

fn cmd_remove(name: &str) -> Result<()> {
    let root = find_project_root()?;
    let manifest_path = root.join("riina.toml");
    let source = std::fs::read_to_string(&manifest_path)
        .map_err(|e| PkgError::io(&manifest_path, e))?;

    let mut lines: Vec<&str> = source.lines().collect();
    let pattern = format!("{} = ", name);
    lines.retain(|line| !line.trim().starts_with(&pattern));

    let new_source = lines.join("\n") + "\n";
    std::fs::write(&manifest_path, &new_source)
        .map_err(|e| PkgError::io(&manifest_path, e))?;
    eprintln!("Removed {}", name);
    Ok(())
}

fn cmd_update(_dep: Option<&str>) -> Result<()> {
    // Re-resolve: just run lock again (lockfile is regenerated)
    cmd_lock()
}

fn cmd_lock() -> Result<()> {
    let root = find_project_root()?;
    let manifest = Manifest::from_file(&root.join("riina.toml"))?;

    // Check for workspace
    let deps = if let Some(ws) = Workspace::discover(&root)? {
        ws.all_dependencies()?
    } else {
        manifest.dep_reqs()?
    };

    if deps.is_empty() {
        let lockfile = Lockfile::new();
        lockfile.write_to(&root.join("riina.lock"))?;
        eprintln!("No dependencies. Wrote riina.lock");
        return Ok(());
    }

    let reg = FsRegistry::new(registry_root());
    let graph = resolve::resolve(&deps, &reg)?;

    // Effect escalation check
    let root_perms = EffectPermissions::from_allowed(&manifest.allowed_effects);
    for (name, pkg) in &graph.packages {
        let dep_manifest = reg.get_manifest(name, &pkg.version)?;
        let dep_perms = EffectPermissions::from_allowed(&dep_manifest.allowed_effects);
        root_perms.check_escalation(name, &dep_perms)?;
    }

    // Build lockfile
    let mut lockfile = Lockfile::new();
    let order = graph.topological_order()?;
    for name in &order {
        let pkg = &graph.packages[name];
        let pkg_path = reg.package_path(name, &pkg.version);
        let checksum = if pkg_path.join("riina.toml").is_file() {
            let data = std::fs::read(pkg_path.join("riina.toml"))
                .unwrap_or_default();
            sha256_hex(&data)
        } else {
            String::new()
        };
        let dep_strs: Vec<String> = pkg.deps.iter()
            .map(|d| {
                let dv = &graph.packages[d].version;
                format!("{d} {dv}")
            })
            .collect();
        lockfile.packages.push(LockedPackage {
            name: name.clone(),
            version: pkg.version.clone(),
            checksum,
            dependencies: dep_strs,
        });
    }

    lockfile.write_to(&root.join("riina.lock"))?;
    eprintln!("Resolved {} packages. Wrote riina.lock", lockfile.packages.len());
    Ok(())
}

fn cmd_build() -> Result<()> {
    let root = find_project_root()?;
    let manifest = Manifest::from_file(&root.join("riina.toml"))?;
    let deps = manifest.dep_reqs()?;

    if deps.is_empty() {
        // Just build root
        let config = crate::build::BuildConfig::new(&root);
        let mut graph_packages = std::collections::BTreeMap::new();
        graph_packages.insert(manifest.package.name.clone(), crate::resolve::ResolvedPackage {
            name: manifest.package.name.clone(),
            version: manifest.package.version.clone(),
            deps: vec![],
        });
        let graph = crate::resolve::ResolvedGraph { packages: graph_packages };
        let steps = crate::build::build_plan(&graph, &config, &manifest.package.name)?;
        crate::build::execute_build(&steps)?;
    } else {
        let reg = FsRegistry::new(registry_root());
        let graph = resolve::resolve(&deps, &reg)?;
        let config = crate::build::BuildConfig::new(&root)
            .with_registry(registry_root());
        let steps = crate::build::build_plan(&graph, &config, &manifest.package.name)?;
        crate::build::execute_build(&steps)?;
    }

    eprintln!("Build complete.");
    Ok(())
}

fn cmd_publish() -> Result<()> {
    let root = find_project_root()?;
    let manifest = Manifest::from_file(&root.join("riina.toml"))?;
    let reg = FsRegistry::new(registry_root());
    reg.publish(&manifest.package.name, &manifest.package.version, &root)?;
    eprintln!("Published {} v{}", manifest.package.name, manifest.package.version);
    Ok(())
}

fn cmd_list() -> Result<()> {
    let root = find_project_root()?;
    let manifest = Manifest::from_file(&root.join("riina.toml"))?;

    if manifest.dependencies.is_empty() {
        eprintln!("No dependencies.");
        return Ok(());
    }

    eprintln!("{} v{}", manifest.package.name, manifest.package.version);
    for (name, req) in &manifest.dependencies {
        eprintln!("  {} = \"{}\"", name, req);
    }

    // Show locked versions if lockfile exists
    let lock_path = root.join("riina.lock");
    if lock_path.is_file() {
        let lockfile = Lockfile::from_file(&lock_path)?;
        if !lockfile.packages.is_empty() {
            eprintln!("\nLocked:");
            for pkg in &lockfile.packages {
                eprintln!("  {} v{}", pkg.name, pkg.version);
            }
        }
    }

    Ok(())
}

fn cmd_tree() -> Result<()> {
    let root = find_project_root()?;
    let manifest = Manifest::from_file(&root.join("riina.toml"))?;
    let deps = manifest.dep_reqs()?;

    eprintln!("{} v{}", manifest.package.name, manifest.package.version);

    if deps.is_empty() {
        return Ok(());
    }

    let reg = FsRegistry::new(registry_root());
    let graph = resolve::resolve(&deps, &reg)?;
    let root_deps: Vec<String> = manifest.dependencies.keys().cloned().collect();

    let stdout = std::io::stderr();
    let mut handle = stdout.lock();
    resolve::print_tree(&graph, &root_deps, &mut handle)
        .map_err(|e| PkgError::Other(e.to_string()))?;

    Ok(())
}

fn cmd_clean() -> Result<()> {
    let root = find_project_root()?;
    let layout = Layout::new(&root);
    crate::build::clean(&layout.target_dir())?;

    // Also clean cache
    if let Ok(cache) = crate::cache::Cache::default_location() {
        cache.clean()?;
        eprintln!("Cleaned cache.");
    }

    Ok(())
}
