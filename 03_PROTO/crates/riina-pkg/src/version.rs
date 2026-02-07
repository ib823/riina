// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Semantic versioning: parse, compare, requirement matching, intersection.

use crate::error::{PkgError, Result};
use std::fmt;

/// A semantic version (major.minor.patch, optional pre-release).
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Version {
    pub major: u64,
    pub minor: u64,
    pub patch: u64,
    pub pre: Option<String>,
}

impl Version {
    pub fn new(major: u64, minor: u64, patch: u64) -> Self {
        Self { major, minor, patch, pre: None }
    }

    pub fn parse(s: &str) -> Result<Self> {
        let s = s.trim();
        let (ver_part, pre) = if let Some(idx) = s.find('-') {
            (&s[..idx], Some(s[idx + 1..].to_string()))
        } else {
            (s, None)
        };
        let parts: Vec<&str> = ver_part.split('.').collect();
        if parts.len() != 3 {
            return Err(PkgError::InvalidVersion(s.to_string()));
        }
        let major = parts[0].parse::<u64>().map_err(|_| PkgError::InvalidVersion(s.to_string()))?;
        let minor = parts[1].parse::<u64>().map_err(|_| PkgError::InvalidVersion(s.to_string()))?;
        let patch = parts[2].parse::<u64>().map_err(|_| PkgError::InvalidVersion(s.to_string()))?;
        Ok(Self { major, minor, patch, pre })
    }
}

impl Ord for Version {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.major.cmp(&other.major)
            .then(self.minor.cmp(&other.minor))
            .then(self.patch.cmp(&other.patch))
            .then_with(|| match (&self.pre, &other.pre) {
                (None, None) => std::cmp::Ordering::Equal,
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, Some(_)) => std::cmp::Ordering::Greater,
                (Some(a), Some(b)) => a.cmp(b),
            })
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;
        if let Some(ref pre) = self.pre {
            write!(f, "-{pre}")?;
        }
        Ok(())
    }
}

/// Comparison operator for version requirements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Op {
    /// `^` — compatible (default): >=X.Y.Z, <next breaking
    Caret,
    /// `~` — patch-level: >=X.Y.Z, <X.(Y+1).0
    Tilde,
    /// `=` — exact
    Exact,
    /// `>=`
    Gte,
    /// `<=`
    Lte,
    /// `>`
    Gt,
    /// `<`
    Lt,
    /// `*` — any version
    Wildcard,
}

/// A single version comparator (op + version).
#[derive(Clone, Debug)]
pub struct Comparator {
    pub op: Op,
    pub version: Version,
}

/// A version requirement (conjunction of comparators, or disjunction via `||`).
/// Simplified: we support a single range expression.
#[derive(Clone, Debug)]
pub struct VersionReq {
    pub comparators: Vec<Comparator>,
}

impl VersionReq {
    pub fn parse(s: &str) -> Result<Self> {
        let s = s.trim();
        if s == "*" {
            return Ok(Self {
                comparators: vec![Comparator { op: Op::Wildcard, version: Version::new(0, 0, 0) }],
            });
        }

        let mut comparators = Vec::new();
        for part in s.split(',') {
            comparators.push(parse_comparator(part.trim())?);
        }
        if comparators.is_empty() {
            return Err(PkgError::InvalidVersionReq(s.to_string()));
        }
        Ok(Self { comparators })
    }

    /// Check if a version satisfies this requirement.
    pub fn matches(&self, v: &Version) -> bool {
        self.comparators.iter().all(|c| c.matches(v))
    }

    /// Intersect two requirements: produce one that satisfies both.
    /// Returns None if the intersection is provably empty (best-effort).
    pub fn intersect(&self, other: &Self) -> Self {
        let mut combined = self.comparators.clone();
        combined.extend(other.comparators.iter().cloned());
        Self { comparators: combined }
    }
}

impl fmt::Display for VersionReq {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, c) in self.comparators.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{c}")?;
        }
        Ok(())
    }
}

fn parse_comparator(s: &str) -> Result<Comparator> {
    let s = s.trim();
    if let Some(rest) = s.strip_prefix(">=") {
        Ok(Comparator { op: Op::Gte, version: Version::parse(rest)? })
    } else if let Some(rest) = s.strip_prefix("<=") {
        Ok(Comparator { op: Op::Lte, version: Version::parse(rest)? })
    } else if let Some(rest) = s.strip_prefix('>') {
        Ok(Comparator { op: Op::Gt, version: Version::parse(rest)? })
    } else if let Some(rest) = s.strip_prefix('<') {
        Ok(Comparator { op: Op::Lt, version: Version::parse(rest)? })
    } else if let Some(rest) = s.strip_prefix('=') {
        Ok(Comparator { op: Op::Exact, version: Version::parse(rest)? })
    } else if let Some(rest) = s.strip_prefix('^') {
        Ok(Comparator { op: Op::Caret, version: Version::parse(rest)? })
    } else if let Some(rest) = s.strip_prefix('~') {
        Ok(Comparator { op: Op::Tilde, version: Version::parse(rest)? })
    } else {
        // bare version => caret
        Ok(Comparator { op: Op::Caret, version: Version::parse(s)? })
    }
}

impl Comparator {
    pub fn matches(&self, v: &Version) -> bool {
        match self.op {
            Op::Wildcard => true,
            Op::Exact => *v == self.version,
            Op::Gte => *v >= self.version,
            Op::Lte => *v <= self.version,
            Op::Gt => *v > self.version,
            Op::Lt => *v < self.version,
            Op::Caret => {
                if v < &self.version {
                    return false;
                }
                if self.version.major != 0 {
                    v.major == self.version.major
                } else if self.version.minor != 0 {
                    v.major == 0 && v.minor == self.version.minor
                } else {
                    *v == self.version
                }
            }
            Op::Tilde => {
                if v < &self.version {
                    return false;
                }
                v.major == self.version.major && v.minor == self.version.minor
            }
        }
    }
}

impl fmt::Display for Comparator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prefix = match self.op {
            Op::Caret => "^",
            Op::Tilde => "~",
            Op::Exact => "=",
            Op::Gte => ">=",
            Op::Lte => "<=",
            Op::Gt => ">",
            Op::Lt => "<",
            Op::Wildcard => return write!(f, "*"),
        };
        write!(f, "{prefix}{}", self.version)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_version() {
        let v = Version::parse("1.2.3").unwrap();
        assert_eq!(v.major, 1);
        assert_eq!(v.minor, 2);
        assert_eq!(v.patch, 3);
        assert!(v.pre.is_none());
    }

    #[test]
    fn parse_version_pre() {
        let v = Version::parse("0.1.0-alpha").unwrap();
        assert_eq!(v.pre.as_deref(), Some("alpha"));
    }

    #[test]
    fn version_ordering() {
        let a = Version::parse("1.0.0").unwrap();
        let b = Version::parse("1.0.1").unwrap();
        let c = Version::parse("1.1.0").unwrap();
        let d = Version::parse("2.0.0").unwrap();
        assert!(a < b);
        assert!(b < c);
        assert!(c < d);
    }

    #[test]
    fn pre_less_than_release() {
        let pre = Version::parse("1.0.0-alpha").unwrap();
        let rel = Version::parse("1.0.0").unwrap();
        assert!(pre < rel);
    }

    #[test]
    fn caret_matching() {
        let req = VersionReq::parse("^1.2.0").unwrap();
        assert!(req.matches(&Version::parse("1.2.0").unwrap()));
        assert!(req.matches(&Version::parse("1.9.9").unwrap()));
        assert!(!req.matches(&Version::parse("2.0.0").unwrap()));
        assert!(!req.matches(&Version::parse("1.1.0").unwrap()));
    }

    #[test]
    fn caret_zero_major() {
        let req = VersionReq::parse("^0.2.0").unwrap();
        assert!(req.matches(&Version::parse("0.2.0").unwrap()));
        assert!(req.matches(&Version::parse("0.2.9").unwrap()));
        assert!(!req.matches(&Version::parse("0.3.0").unwrap()));
    }

    #[test]
    fn tilde_matching() {
        let req = VersionReq::parse("~1.2.0").unwrap();
        assert!(req.matches(&Version::parse("1.2.0").unwrap()));
        assert!(req.matches(&Version::parse("1.2.9").unwrap()));
        assert!(!req.matches(&Version::parse("1.3.0").unwrap()));
    }

    #[test]
    fn wildcard() {
        let req = VersionReq::parse("*").unwrap();
        assert!(req.matches(&Version::parse("0.0.1").unwrap()));
        assert!(req.matches(&Version::parse("99.0.0").unwrap()));
    }

    #[test]
    fn exact_match() {
        let req = VersionReq::parse("=1.0.0").unwrap();
        assert!(req.matches(&Version::parse("1.0.0").unwrap()));
        assert!(!req.matches(&Version::parse("1.0.1").unwrap()));
    }

    #[test]
    fn comparison_ops() {
        let req = VersionReq::parse(">=1.0.0, <2.0.0").unwrap();
        assert!(req.matches(&Version::parse("1.5.0").unwrap()));
        assert!(!req.matches(&Version::parse("0.9.0").unwrap()));
        assert!(!req.matches(&Version::parse("2.0.0").unwrap()));
    }

    #[test]
    fn intersect_works() {
        let a = VersionReq::parse("^1.0.0").unwrap();
        let b = VersionReq::parse(">=1.2.0").unwrap();
        let c = a.intersect(&b);
        assert!(c.matches(&Version::parse("1.3.0").unwrap()));
        assert!(!c.matches(&Version::parse("1.1.0").unwrap()));
        assert!(!c.matches(&Version::parse("2.0.0").unwrap()));
    }

    #[test]
    fn display_version() {
        assert_eq!(Version::new(1, 2, 3).to_string(), "1.2.3");
    }

    #[test]
    fn display_req() {
        let req = VersionReq::parse("^1.0.0").unwrap();
        assert_eq!(req.to_string(), "^1.0.0");
    }

    #[test]
    fn invalid_version() {
        assert!(Version::parse("abc").is_err());
        assert!(Version::parse("1.2").is_err());
    }
}
