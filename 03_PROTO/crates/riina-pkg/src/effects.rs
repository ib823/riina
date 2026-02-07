// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Effect permission checking for packages.
//!
//! Maps between riina-types Effect categories and the manifest's
//! `[kesan-dibenarkan]` (allowed effects) section.

use crate::error::{PkgError, Result};
use crate::manifest::AllowedEffects;

/// Effect category matching the manifest's permission keys.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EffectCategory {
    IO,
    Crypto,
    Network,
    System,
    Product,
}

impl EffectCategory {
    /// All categories.
    pub const ALL: &'static [EffectCategory] = &[
        Self::IO, Self::Crypto, Self::Network, Self::System, Self::Product,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Self::IO => "IO",
            Self::Crypto => "Crypto",
            Self::Network => "Network",
            Self::System => "System",
            Self::Product => "Product",
        }
    }

    /// Map riina_types::Effect to our category.
    pub fn from_effect(eff: riina_types::Effect) -> Option<Self> {
        use riina_types::Effect;
        match eff {
            Effect::Pure | Effect::Mut => None, // Local effects don't need permissions
            Effect::Read | Effect::Write | Effect::Alloc | Effect::FileSystem => Some(Self::IO),
            Effect::Network | Effect::NetworkSecure => Some(Self::Network),
            Effect::Crypto | Effect::Random => Some(Self::Crypto),
            Effect::System | Effect::Process | Effect::Time => Some(Self::System),
            Effect::Panel | Effect::Zirah | Effect::Benteng
            | Effect::Sandi | Effect::Menara | Effect::Gapura => Some(Self::Product),
        }
    }
}

/// Set of effect permissions.
#[derive(Debug, Clone, Default)]
pub struct EffectPermissions {
    pub io: bool,
    pub crypto: bool,
    pub network: bool,
    pub system: bool,
    pub product: bool,
}

impl EffectPermissions {
    pub fn from_allowed(a: &AllowedEffects) -> Self {
        Self {
            io: a.io,
            crypto: a.crypto,
            network: a.network,
            system: a.system,
            product: a.product,
        }
    }

    /// Check if a category is permitted.
    pub fn permits(&self, cat: EffectCategory) -> bool {
        match cat {
            EffectCategory::IO => self.io,
            EffectCategory::Crypto => self.crypto,
            EffectCategory::Network => self.network,
            EffectCategory::System => self.system,
            EffectCategory::Product => self.product,
        }
    }

    /// Union of two permission sets.
    pub fn union(&self, other: &Self) -> Self {
        Self {
            io: self.io || other.io,
            crypto: self.crypto || other.crypto,
            network: self.network || other.network,
            system: self.system || other.system,
            product: self.product || other.product,
        }
    }

    /// Check that `dep_perms` doesn't escalate beyond `self`.
    /// Returns an error listing the first forbidden effect.
    pub fn check_escalation(&self, dep_name: &str, dep_perms: &Self) -> Result<()> {
        for &cat in EffectCategory::ALL {
            if dep_perms.permits(cat) && !self.permits(cat) {
                return Err(PkgError::EffectEscalation {
                    dep: dep_name.to_string(),
                    effect: cat.name().to_string(),
                });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn permits_check() {
        let p = EffectPermissions { io: true, crypto: false, ..Default::default() };
        assert!(p.permits(EffectCategory::IO));
        assert!(!p.permits(EffectCategory::Crypto));
    }

    #[test]
    fn union_works() {
        let a = EffectPermissions { io: true, ..Default::default() };
        let b = EffectPermissions { crypto: true, ..Default::default() };
        let c = a.union(&b);
        assert!(c.io);
        assert!(c.crypto);
        assert!(!c.network);
    }

    #[test]
    fn escalation_detected() {
        let parent = EffectPermissions { io: true, ..Default::default() };
        let dep = EffectPermissions { io: true, network: true, ..Default::default() };
        assert!(parent.check_escalation("bad-dep", &dep).is_err());
    }

    #[test]
    fn escalation_ok() {
        let parent = EffectPermissions { io: true, network: true, ..Default::default() };
        let dep = EffectPermissions { io: true, ..Default::default() };
        assert!(parent.check_escalation("good-dep", &dep).is_ok());
    }

    #[test]
    fn from_effect_mapping() {
        use riina_types::Effect;
        assert_eq!(EffectCategory::from_effect(Effect::Pure), None);
        assert_eq!(EffectCategory::from_effect(Effect::FileSystem), Some(EffectCategory::IO));
        assert_eq!(EffectCategory::from_effect(Effect::Network), Some(EffectCategory::Network));
        assert_eq!(EffectCategory::from_effect(Effect::Crypto), Some(EffectCategory::Crypto));
        assert_eq!(EffectCategory::from_effect(Effect::Process), Some(EffectCategory::System));
        assert_eq!(EffectCategory::from_effect(Effect::Panel), Some(EffectCategory::Product));
    }
}
