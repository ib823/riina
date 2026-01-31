//! Hand-written TOML subset parser for riina.toml manifests.

use crate::error::{PkgError, Result};
use crate::version::{Version, VersionReq};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// A parsed riina.toml manifest.
#[derive(Debug, Clone)]
pub struct Manifest {
    /// Package metadata.
    pub package: PackageMeta,
    /// Regular dependencies: name -> version requirement string.
    pub dependencies: BTreeMap<String, String>,
    /// Dev dependencies.
    pub dev_dependencies: BTreeMap<String, String>,
    /// Allowed effect categories.
    pub allowed_effects: AllowedEffects,
    /// Workspace config (only present in workspace root).
    pub workspace: Option<WorkspaceConfig>,
}

#[derive(Debug, Clone)]
pub struct PackageMeta {
    pub name: String,
    pub version: Version,
    pub authors: Vec<String>,
    pub license: Option<String>,
    pub description: Option<String>,
    pub homepage: Option<String>,
    pub repository: Option<String>,
}

#[derive(Debug, Clone, Default)]
pub struct AllowedEffects {
    pub io: bool,
    pub crypto: bool,
    pub network: bool,
    pub system: bool,
    pub product: bool,
}

#[derive(Debug, Clone)]
pub struct WorkspaceConfig {
    pub members: Vec<String>,
}

impl Manifest {
    /// Parse a riina.toml from a string, with file path for error messages.
    pub fn parse(source: &str, file: &Path) -> Result<Self> {
        let mut parser = TomlParser::new(source, file);
        parser.parse()
    }

    /// Read and parse a riina.toml from disk.
    pub fn from_file(path: &Path) -> Result<Self> {
        let source = std::fs::read_to_string(path)
            .map_err(|e| PkgError::io(path, e))?;
        Self::parse(&source, path)
    }

    /// Dependency as VersionReq map.
    pub fn dep_reqs(&self) -> Result<BTreeMap<String, VersionReq>> {
        let mut out = BTreeMap::new();
        for (name, req_str) in &self.dependencies {
            out.insert(name.clone(), VersionReq::parse(req_str)?);
        }
        Ok(out)
    }
}

// ── Minimal TOML subset parser ──────────────────────────────────────────

struct TomlParser<'a> {
    lines: Vec<&'a str>,
    file: PathBuf,
}

enum TableKind {
    Pakej,
    Kebergantungan,
    DevKebergantungan,
    KesanDibenarkan,
    Workspace,
    Unknown,
}

impl<'a> TomlParser<'a> {
    fn new(source: &'a str, file: &Path) -> Self {
        Self {
            lines: source.lines().collect(),
            file: file.to_path_buf(),
        }
    }

    fn parse(&mut self) -> Result<Manifest> {
        let mut package = None::<PackageMeta>;
        let mut deps = BTreeMap::new();
        let mut dev_deps = BTreeMap::new();
        let mut effects = AllowedEffects::default();
        let mut workspace = None::<WorkspaceConfig>;

        let mut current_table = TableKind::Unknown;
        // temp storage for [pakej]
        let mut pkg_fields: BTreeMap<String, TomlValue> = BTreeMap::new();

        for (line_idx, line) in self.lines.iter().enumerate() {
            let trimmed = line.trim();
            // skip empty and comments
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }

            // table header
            if trimmed.starts_with('[') && trimmed.ends_with(']') {
                // finalize previous table
                if matches!(current_table, TableKind::Pakej) && package.is_none() {
                    package = Some(self.build_package(&pkg_fields)?);
                }

                let header = &trimmed[1..trimmed.len() - 1].trim();
                current_table = match *header {
                    "pakej" => TableKind::Pakej,
                    "kebergantungan" => TableKind::Kebergantungan,
                    "dev-kebergantungan" => TableKind::DevKebergantungan,
                    "kesan-dibenarkan" => TableKind::KesanDibenarkan,
                    "workspace" => TableKind::Workspace,
                    _ => TableKind::Unknown,
                };
                continue;
            }

            // key = value
            let (key, value) = self.parse_kv(trimmed, line_idx + 1)?;

            match current_table {
                TableKind::Pakej => { pkg_fields.insert(key, value); }
                TableKind::Kebergantungan => {
                    deps.insert(key, value.as_str(line_idx + 1, &self.file)?);
                }
                TableKind::DevKebergantungan => {
                    dev_deps.insert(key, value.as_str(line_idx + 1, &self.file)?);
                }
                TableKind::KesanDibenarkan => {
                    let b = value.as_bool(line_idx + 1, &self.file)?;
                    match key.as_str() {
                        "IO" => effects.io = b,
                        "Crypto" => effects.crypto = b,
                        "Network" => effects.network = b,
                        "System" => effects.system = b,
                        "Product" => effects.product = b,
                        _ => {}
                    }
                }
                TableKind::Workspace => {
                    if key == "members" {
                        let members = value.as_string_array(line_idx + 1, &self.file)?;
                        workspace = Some(WorkspaceConfig { members });
                    }
                }
                TableKind::Unknown => {}
            }
        }

        // finalize [pakej] if it was the last table
        if matches!(current_table, TableKind::Pakej) && package.is_none() {
            package = Some(self.build_package(&pkg_fields)?);
        }

        let package = package.ok_or_else(|| PkgError::ManifestMissing {
            file: self.file.clone(),
            field: "pakej".to_string(),
        })?;

        Ok(Manifest { package, dependencies: deps, dev_dependencies: dev_deps, allowed_effects: effects, workspace })
    }

    fn build_package(&self, fields: &BTreeMap<String, TomlValue>) -> Result<PackageMeta> {
        let name = fields.get("nama")
            .ok_or_else(|| PkgError::ManifestMissing { file: self.file.clone(), field: "nama".into() })?
            .as_str(0, &self.file)?;
        let version_str = fields.get("versi")
            .ok_or_else(|| PkgError::ManifestMissing { file: self.file.clone(), field: "versi".into() })?
            .as_str(0, &self.file)?;
        let version = Version::parse(&version_str)?;
        let authors = fields.get("pengarang")
            .map(|v| v.as_string_array(0, &self.file))
            .transpose()?
            .unwrap_or_default();
        let license = fields.get("lesen").map(|v| v.as_str(0, &self.file)).transpose()?;
        let description = fields.get("keterangan").map(|v| v.as_str(0, &self.file)).transpose()?;
        let homepage = fields.get("laman").map(|v| v.as_str(0, &self.file)).transpose()?;
        let repository = fields.get("repositori").map(|v| v.as_str(0, &self.file)).transpose()?;
        Ok(PackageMeta { name, version, authors, license, description, homepage, repository })
    }

    fn parse_kv(&self, line: &str, line_num: usize) -> Result<(String, TomlValue)> {
        let eq_pos = line.find('=').ok_or_else(|| PkgError::ManifestParse {
            file: self.file.clone(), line: line_num,
            message: format!("expected 'key = value', got: {line}"),
        })?;
        let key = line[..eq_pos].trim().to_string();
        let val_str = line[eq_pos + 1..].trim();
        let value = self.parse_value(val_str, line_num)?;
        Ok((key, value))
    }

    fn parse_value(&self, s: &str, line_num: usize) -> Result<TomlValue> {
        let s = s.trim();
        if s == "true" {
            Ok(TomlValue::Bool(true))
        } else if s == "false" {
            Ok(TomlValue::Bool(false))
        } else if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
            Ok(TomlValue::Str(s[1..s.len() - 1].to_string()))
        } else if s.starts_with('[') && s.ends_with(']') {
            // Parse array of strings
            let inner = s[1..s.len() - 1].trim();
            if inner.is_empty() {
                return Ok(TomlValue::Array(vec![]));
            }
            let mut items = Vec::new();
            for item in inner.split(',') {
                let item = item.trim();
                if item.starts_with('"') && item.ends_with('"') && item.len() >= 2 {
                    items.push(item[1..item.len() - 1].to_string());
                } else if !item.is_empty() {
                    return Err(PkgError::ManifestParse {
                        file: self.file.clone(), line: line_num,
                        message: format!("expected quoted string in array, got: {item}"),
                    });
                }
            }
            Ok(TomlValue::Array(items))
        } else {
            Err(PkgError::ManifestParse {
                file: self.file.clone(), line: line_num,
                message: format!("unsupported value: {s}"),
            })
        }
    }
}

#[derive(Debug, Clone)]
enum TomlValue {
    Str(String),
    Bool(bool),
    Array(Vec<String>),
}

impl TomlValue {
    fn as_str(&self, line: usize, file: &Path) -> Result<String> {
        match self {
            Self::Str(s) => Ok(s.clone()),
            _ => Err(PkgError::ManifestParse {
                file: file.to_path_buf(), line,
                message: "expected string".into(),
            }),
        }
    }

    fn as_bool(&self, line: usize, file: &Path) -> Result<bool> {
        match self {
            Self::Bool(b) => Ok(*b),
            _ => Err(PkgError::ManifestParse {
                file: file.to_path_buf(), line,
                message: "expected boolean".into(),
            }),
        }
    }

    fn as_string_array(&self, line: usize, file: &Path) -> Result<Vec<String>> {
        match self {
            Self::Array(a) => Ok(a.clone()),
            _ => Err(PkgError::ManifestParse {
                file: file.to_path_buf(), line,
                message: "expected array".into(),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const SAMPLE: &str = r#"
[pakej]
nama = "contoh"
versi = "0.1.0"
pengarang = ["Ahmad <ahmad@example.my>"]
lesen = "MIT"
keterangan = "Contoh pakej RIINA"

[kebergantungan]
kripto = "^1.0.0"
masa = "~0.5.0"

[dev-kebergantungan]
ujian-rangka = "*"

[kesan-dibenarkan]
IO = true
Crypto = true
Network = false
System = false
Product = false
"#;

    #[test]
    fn parse_manifest() {
        let m = Manifest::parse(SAMPLE, Path::new("riina.toml")).unwrap();
        assert_eq!(m.package.name, "contoh");
        assert_eq!(m.package.version, Version::new(0, 1, 0));
        assert_eq!(m.package.authors, vec!["Ahmad <ahmad@example.my>"]);
        assert_eq!(m.package.license.as_deref(), Some("MIT"));
        assert_eq!(m.dependencies.len(), 2);
        assert_eq!(m.dependencies["kripto"], "^1.0.0");
        assert_eq!(m.dev_dependencies.len(), 1);
        assert!(m.allowed_effects.io);
        assert!(m.allowed_effects.crypto);
        assert!(!m.allowed_effects.network);
    }

    #[test]
    fn missing_pakej() {
        let src = "[kebergantungan]\nfoo = \"^1.0.0\"\n";
        assert!(Manifest::parse(src, Path::new("riina.toml")).is_err());
    }

    #[test]
    fn workspace_manifest() {
        let src = r#"
[pakej]
nama = "root"
versi = "0.1.0"

[workspace]
members = ["pakej-a", "pakej-b"]
"#;
        let m = Manifest::parse(src, Path::new("riina.toml")).unwrap();
        assert!(m.workspace.is_some());
        assert_eq!(m.workspace.unwrap().members, vec!["pakej-a", "pakej-b"]);
    }
}
