//! cfg defines conditional compiling options, `cfg` attribute parser and evaluator

#![cfg_attr(feature = "in-rust-tree", feature(rustc_private))]

#[cfg(feature = "in-rust-tree")]
extern crate rustc_driver as _;

mod cfg_expr;
mod dnf;
#[cfg(test)]
mod tests;

use std::{
    collections::BTreeMap,
    fmt,
    sync::{Arc, Mutex},
};

use rustc_hash::FxHashSet;

use intern::{Symbol, sym};

pub use cfg_expr::{CfgAtom, CfgExpr};
pub use dnf::DnfExpr;

/// Configuration options used for conditional compilation on items with `cfg` attributes.
/// We have two kind of options in different namespaces: atomic options like `unix`, and
/// key-value options like `target_arch="x86"`.
///
/// Note that for key-value options, one key can have multiple values (but not none).
/// `feature` is an example. We have both `feature="foo"` and `feature="bar"` if features
/// `foo` and `bar` are both enabled. And here, we store key-value options as a set of tuple
/// of key and value in `key_values`.
///
/// See: <https://doc.rust-lang.org/reference/conditional-compilation.html#set-configuration-options>
#[derive(Clone)]
pub struct CfgOptions {
    enabled: FxHashSet<CfgAtom>,
    reads: Option<CfgReadRecorder>,
}

impl PartialEq for CfgOptions {
    fn eq(&self, other: &Self) -> bool {
        self.enabled == other.enabled
    }
}

impl Eq for CfgOptions {}

/// Observations made by one lowering operation, including absent atoms.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CfgReads {
    pub atoms: BTreeMap<CfgAtom, bool>,
    pub read_all: Option<HashableCfgOptions>,
    pub unknown: bool,
}

impl CfgReads {
    pub fn merge(&mut self, other: &Self) {
        self.unknown |= other.unknown;
        for (atom, answer) in &other.atoms {
            if self.atoms.insert(atom.clone(), *answer).is_some_and(|old| old != *answer) {
                self.unknown = true;
            }
        }
        if let Some(all) = &other.read_all {
            if self.read_all.as_ref().is_some_and(|old| old != all) {
                self.unknown = true;
            }
            self.read_all = Some(all.clone());
        }
    }

    pub fn agrees_with(&self, options: &CfgOptions) -> bool {
        !self.unknown && !self.differs_from(options)
    }

    pub fn differs_from(&self, options: &CfgOptions) -> bool {
        self.atoms.iter().any(|(atom, answer)| options.check_atom(atom) != *answer)
            || self.read_all.as_ref().is_some_and(|all| *all != options.to_hashable())
    }
}

/// A recorder belongs to a local copy of options, never to a database input.
#[derive(Clone, Debug, Default)]
pub struct CfgReadRecorder(Arc<Mutex<CfgReads>>);

impl CfgReadRecorder {
    pub fn finish(&self) -> CfgReads {
        self.0.lock().unwrap().clone()
    }
}

impl Default for CfgOptions {
    fn default() -> Self {
        Self { enabled: FxHashSet::from_iter([CfgAtom::Flag(sym::true_)]), reads: None }
    }
}

impl fmt::Debug for CfgOptions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut items = self
            .enabled
            .iter()
            .map(|atom| match atom {
                CfgAtom::Flag(it) => it.to_string(),
                CfgAtom::KeyValue { key, value } => format!("{key}={value}"),
            })
            .collect::<Vec<_>>();
        items.sort();
        f.debug_tuple("CfgOptions").field(&items).finish()
    }
}

impl CfgOptions {
    pub fn recording(&self) -> (Self, CfgReadRecorder) {
        let reads = CfgReadRecorder::default();
        let options = Self { enabled: self.enabled.clone(), reads: Some(reads.clone()) };
        (options, reads)
    }

    pub fn check(&self, cfg: &CfgExpr) -> Option<bool> {
        let result = cfg.fold(&|atom| self.check_atom(atom));
        if result.is_none()
            && let Some(reads) = &self.reads
        {
            reads.0.lock().unwrap().unknown = true;
        }
        result
    }

    pub fn check_atom(&self, cfg: &CfgAtom) -> bool {
        let answer = self.enabled.contains(cfg);
        if let Some(reads) = &self.reads {
            reads.0.lock().unwrap().atoms.insert(cfg.clone(), answer);
        }
        answer
    }

    pub fn insert_atom(&mut self, key: Symbol) {
        self.insert_any_atom(CfgAtom::Flag(key));
    }

    pub fn insert_key_value(&mut self, key: Symbol, value: Symbol) {
        self.insert_any_atom(CfgAtom::KeyValue { key, value });
    }

    pub fn apply_diff(&mut self, diff: CfgDiff) {
        for atom in diff.enable {
            self.insert_any_atom(atom);
        }

        for atom in diff.disable {
            let (CfgAtom::Flag(sym) | CfgAtom::KeyValue { key: sym, .. }) = &atom;
            if *sym == sym::true_ || *sym == sym::false_ {
                tracing::error!("cannot remove `true` or `false` from cfg");
                continue;
            }
            self.enabled.remove(&atom);
        }
    }

    fn insert_any_atom(&mut self, atom: CfgAtom) {
        let (CfgAtom::Flag(sym) | CfgAtom::KeyValue { key: sym, .. }) = &atom;
        if *sym == sym::true_ || *sym == sym::false_ {
            tracing::error!("cannot insert `true` or `false` to cfg");
            return;
        }
        self.enabled.insert(atom);
    }

    pub fn get_cfg_keys(&self) -> impl Iterator<Item = &Symbol> {
        self.record_all();
        self.enabled.iter().map(|it| match it {
            CfgAtom::Flag(key) => key,
            CfgAtom::KeyValue { key, .. } => key,
        })
    }

    pub fn get_cfg_values<'a>(&'a self, cfg_key: &'a str) -> impl Iterator<Item = &'a Symbol> + 'a {
        self.record_all();
        self.enabled.iter().filter_map(move |it| match it {
            CfgAtom::KeyValue { key, value } if cfg_key == key.as_str() => Some(value),
            _ => None,
        })
    }

    pub fn to_hashable(&self) -> HashableCfgOptions {
        self.record_all();
        self.hashable()
    }

    fn record_all(&self) {
        if let Some(reads) = &self.reads {
            reads.0.lock().unwrap().read_all = Some(self.hashable());
        }
    }

    fn hashable(&self) -> HashableCfgOptions {
        let mut enabled = self.enabled.iter().cloned().collect::<Box<[_]>>();
        enabled.sort_unstable();
        HashableCfgOptions { _enabled: enabled }
    }

    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.enabled.shrink_to_fit();
    }

    pub fn append(&mut self, other: CfgOptions) {
        // Do not call `insert_any_atom()`, as it'll check for `true` and `false`, but this is not
        // needed since we already checked for that when constructing `other`. Furthermore, this
        // will always err, as `other` inevitably contains `true` (just as we do).
        self.enabled.extend(other.enabled);
    }
}

impl Extend<CfgAtom> for CfgOptions {
    fn extend<T: IntoIterator<Item = CfgAtom>>(&mut self, iter: T) {
        iter.into_iter().for_each(|cfg_flag| self.insert_any_atom(cfg_flag));
    }
}

impl IntoIterator for CfgOptions {
    type Item = <FxHashSet<CfgAtom> as IntoIterator>::Item;

    type IntoIter = <FxHashSet<CfgAtom> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.record_all();
        <FxHashSet<CfgAtom> as IntoIterator>::into_iter(self.enabled)
    }
}

impl<'a> IntoIterator for &'a CfgOptions {
    type Item = <&'a FxHashSet<CfgAtom> as IntoIterator>::Item;

    type IntoIter = <&'a FxHashSet<CfgAtom> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.record_all();
        <&FxHashSet<CfgAtom> as IntoIterator>::into_iter(&self.enabled)
    }
}

impl FromIterator<CfgAtom> for CfgOptions {
    fn from_iter<T: IntoIterator<Item = CfgAtom>>(iter: T) -> Self {
        let mut options = CfgOptions::default();
        options.extend(iter);
        options
    }
}

#[derive(Default, Clone, Debug, PartialEq, Eq)]
pub struct CfgDiff {
    // Invariants: No duplicates, no atom that's both in `enable` and `disable`.
    enable: Vec<CfgAtom>,
    disable: Vec<CfgAtom>,
}

impl CfgDiff {
    /// Create a new CfgDiff.
    pub fn new(mut enable: Vec<CfgAtom>, mut disable: Vec<CfgAtom>) -> CfgDiff {
        enable.sort();
        enable.dedup();
        disable.sort();
        disable.dedup();
        for i in (0..enable.len()).rev() {
            if let Some(j) = disable.iter().position(|atom| *atom == enable[i]) {
                enable.remove(i);
                disable.remove(j);
            }
        }

        CfgDiff { enable, disable }
    }

    /// Returns the total number of atoms changed by this diff.
    pub fn len(&self) -> usize {
        self.enable.len() + self.disable.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl fmt::Display for CfgDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.enable.is_empty() {
            f.write_str("enable ")?;
            for (i, atom) in self.enable.iter().enumerate() {
                let sep = match i {
                    0 => "",
                    _ if i == self.enable.len() - 1 => " and ",
                    _ => ", ",
                };
                f.write_str(sep)?;

                atom.fmt(f)?;
            }

            if !self.disable.is_empty() {
                f.write_str("; ")?;
            }
        }

        if !self.disable.is_empty() {
            f.write_str("disable ")?;
            for (i, atom) in self.disable.iter().enumerate() {
                let sep = match i {
                    0 => "",
                    _ if i == self.disable.len() - 1 => " and ",
                    _ => ", ",
                };
                f.write_str(sep)?;

                atom.fmt(f)?;
            }
        }

        Ok(())
    }
}

pub struct InactiveReason {
    enabled: Vec<CfgAtom>,
    disabled: Vec<CfgAtom>,
}

impl fmt::Display for InactiveReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.enabled.is_empty() {
            for (i, atom) in self.enabled.iter().enumerate() {
                let sep = match i {
                    0 => "",
                    _ if i == self.enabled.len() - 1 => " and ",
                    _ => ", ",
                };
                f.write_str(sep)?;

                atom.fmt(f)?;
            }
            let is_are = if self.enabled.len() == 1 { "is" } else { "are" };
            write!(f, " {is_are} enabled")?;

            if !self.disabled.is_empty() {
                f.write_str(" and ")?;
            }
        }

        if !self.disabled.is_empty() {
            for (i, atom) in self.disabled.iter().enumerate() {
                let sep = match i {
                    0 => "",
                    _ if i == self.disabled.len() - 1 => " and ",
                    _ => ", ",
                };
                f.write_str(sep)?;

                atom.fmt(f)?;
            }
            let is_are = if self.disabled.len() == 1 { "is" } else { "are" };
            write!(f, " {is_are} disabled")?;
        }

        Ok(())
    }
}

/// A `CfgOptions` that implements `Hash`, for the sake of hashing only.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HashableCfgOptions {
    _enabled: Box<[CfgAtom]>,
}
