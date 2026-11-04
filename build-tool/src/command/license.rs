//! Check the license of every package in the dependency graph against the allowlist.

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use anyhow::anyhow;
use clap::Parser;

use super::{GlobalOpts, SubCommand};
use crate::error::Result;
use crate::project::{Project, ProjectHandle};

/// The allowlist, relative to the project root. It is the only place the allowed set lives.
const ALLOWLIST_PATH: &str = "tools/license-allowlist";

/// Check dependency licenses.
#[derive(Debug, Parser)]
pub struct Opts {
    /// Check this manifest's graph instead of the workspace's.
    #[clap(long)]
    manifest_path: Option<PathBuf>,
}

pub(super) async fn run(global: GlobalOpts) -> Result<()> {
    let local = unwrap_command!(global, SubCommand::License);
    let project = Project::discover()?;
    let manifest = local
        .manifest_path
        .unwrap_or_else(|| project.root().join("Cargo.toml"));
    println!("{}", check_manifest(&project, &manifest)?);
    Ok(())
}

/// Checks the workspace's graph.
pub(super) fn check(project: &ProjectHandle) -> Result<String> {
    check_manifest(project, &project.root().join("Cargo.toml"))
}

fn check_manifest(project: &ProjectHandle, manifest: &Path) -> Result<String> {
    let text = fs::read_to_string(project.root().join(ALLOWLIST_PATH))?;
    let allowlist = Allowlist::parse(&text).map_err(|error| anyhow!("{}: {}", ALLOWLIST_PATH, error))?;

    let metadata = cargo_metadata::MetadataCommand::new()
        .manifest_path(manifest)
        .other_options(vec!["--locked".to_string()])
        .exec()?;

    let mut failures = vec![];
    for package in &metadata.packages {
        let member = metadata.workspace_members.contains(&package.id);
        let source = package.source.as_ref().map(|source| source.to_string());
        let verdict = allowlist.check(&package.name, source.as_deref(), package.license.as_deref(), member);
        if let Err(reason) = verdict {
            failures.push(format!("{} {}: {}", package.name, package.version, reason));
        }
    }

    if failures.is_empty() {
        return Ok(format!("{} packages within the allowlist", metadata.packages.len()));
    }
    Err(anyhow!("{}", failures.join("; ")))
}

struct Allowlist {
    licenses: HashSet<String>,
    /// Packages without a license field: (name, source without its revision, verified license).
    packages: Vec<(String, String, String)>,
}

impl Allowlist {
    fn parse(text: &str) -> std::result::Result<Self, String> {
        let mut allowlist = Allowlist {
            licenses: HashSet::new(),
            packages: vec![],
        };
        for line in text.lines().map(str::trim) {
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let fields: Vec<&str> = line.split_whitespace().collect();
            match fields.as_slice() {
                ["license", id] => {
                    allowlist.licenses.insert(id.to_string());
                }
                ["package", name, source, expression @ ..] if !expression.is_empty() => {
                    allowlist
                        .packages
                        .push((name.to_string(), source.to_string(), expression.join(" ")));
                }
                _ => return Err(format!("cannot read {:?}", line)),
            }
        }
        for (name, _, expression) in &allowlist.packages {
            if !allowlist.allows(expression)? {
                return Err(format!("{} names {}, which is not allowed", name, expression));
            }
        }
        Ok(allowlist)
    }

    /// Checks one package. Workspace members with no field are covered by the tree's LICENSE.
    fn check(
        &self,
        name: &str,
        source: Option<&str>,
        license: Option<&str>,
        member: bool,
    ) -> std::result::Result<(), String> {
        match license {
            Some(expression) => match self.allows(expression)? {
                true => Ok(()),
                false => Err(format!("{} is not allowed", expression)),
            },
            None if member => Ok(()),
            None => {
                let source = source.unwrap_or("a path").split('#').next().unwrap();
                let listed = self
                    .packages
                    .iter()
                    .any(|entry| entry.0 == name && entry.1 == source);
                match listed {
                    true => Ok(()),
                    false => Err(format!("no license field and no entry for {}", source)),
                }
            }
        }
    }

    fn allows(&self, expression: &str) -> std::result::Result<bool, String> {
        let spaced = expression
            .replace('(', " ( ")
            .replace(')', " ) ")
            .replace('/', " OR ");
        let tokens: Vec<&str> = spaced.split_whitespace().collect();
        let mut parser = Expression {
            tokens: &tokens,
            next: 0,
            licenses: &self.licenses,
        };
        let allowed = parser.or()?;
        match parser.peek() {
            None => Ok(allowed),
            Some(token) => Err(format!("cannot read {:?} at {:?}", expression, token)),
        }
    }
}

/// A recursive descent over an SPDX expression. AND binds tighter than OR; WITH binds to one id.
struct Expression<'a> {
    tokens: &'a [&'a str],
    next: usize,
    licenses: &'a HashSet<String>,
}

impl<'a> Expression<'a> {
    fn peek(&self) -> Option<&'a str> {
        self.tokens.get(self.next).copied()
    }

    fn eat(&mut self, token: &str) -> bool {
        let found = self.peek() == Some(token);
        if found {
            self.next += 1;
        }
        found
    }

    fn or(&mut self) -> std::result::Result<bool, String> {
        let mut allowed = self.and()?;
        while self.eat("OR") {
            allowed |= self.and()?;
        }
        Ok(allowed)
    }

    fn and(&mut self) -> std::result::Result<bool, String> {
        let mut allowed = self.with()?;
        while self.eat("AND") {
            allowed &= self.with()?;
        }
        Ok(allowed)
    }

    fn with(&mut self) -> std::result::Result<bool, String> {
        if self.eat("(") {
            let allowed = self.or()?;
            return match self.eat(")") {
                true => Ok(allowed),
                false => Err("an unclosed parenthesis".to_string()),
            };
        }
        let allowed = self.licenses.contains(self.id()?);
        if self.eat("WITH") {
            self.id()?;
        }
        Ok(allowed)
    }

    fn id(&mut self) -> std::result::Result<&'a str, String> {
        match self.peek() {
            Some(token) if !["AND", "OR", "WITH", "(", ")"].contains(&token) => {
                self.next += 1;
                Ok(token)
            }
            token => Err(format!("expected a license at {:?}", token)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn allowlist() -> Allowlist {
        Allowlist::parse(
            "# comment\n\nlicense MIT\nlicense Apache-2.0\nlicense Unicode-3.0\n\
             package vstd git+https://example.org/verus?branch=mars MIT\n",
        )
        .unwrap()
    }

    fn allows(expression: &str) -> std::result::Result<bool, String> {
        allowlist().allows(expression)
    }

    #[test]
    fn single_license() {
        assert_eq!(allows("MIT"), Ok(true));
        assert_eq!(allows("GPL-3.0"), Ok(false));
    }

    #[test]
    fn or_needs_one_alternative() {
        assert_eq!(allows("MIT OR GPL-3.0"), Ok(true));
        assert_eq!(allows("GPL-3.0 OR LGPL-2.1"), Ok(false));
    }

    #[test]
    fn slash_is_or() {
        assert_eq!(allows("GPL-3.0/MIT"), Ok(true));
        assert_eq!(allows("GPL-3.0/LGPL-2.1"), Ok(false));
    }

    #[test]
    fn and_needs_every_operand() {
        assert_eq!(allows("(MIT OR Apache-2.0) AND Unicode-3.0"), Ok(true));
        assert_eq!(allows("MIT AND GPL-3.0"), Ok(false));
    }

    #[test]
    fn and_binds_tighter_than_or() {
        assert_eq!(allows("GPL-3.0 AND LGPL-2.1 OR MIT"), Ok(true));
        assert_eq!(allows("MIT OR GPL-3.0 AND LGPL-2.1"), Ok(true));
        assert_eq!(allows("GPL-3.0 OR MIT AND LGPL-2.1"), Ok(false));
    }

    #[test]
    fn with_follows_its_base() {
        assert_eq!(allows("Apache-2.0 WITH LLVM-exception"), Ok(true));
        assert_eq!(allows("GPL-2.0 WITH Classpath-exception-2.0"), Ok(false));
    }

    /// An expression that does not parse must fail, not read as allowed or merely as not allowed.
    #[test]
    fn unknown_strings_are_errors() {
        for expression in ["see the file", "MIT or Apache-2.0", "MIT OR", "(MIT", "MIT)", "", "WITH MIT"] {
            assert!(allows(expression).is_err(), "{:?}", expression);
        }
    }

    #[test]
    fn package_with_a_field_is_judged_by_it() {
        let list = allowlist();
        assert!(list.check("a", Some("registry+x"), Some("MIT"), false).is_ok());
        assert!(list.check("a", Some("registry+x"), Some("GPL-3.0"), false).is_err());
        assert!(list.check("a", None, Some("GPL-3.0"), true).is_err());
    }

    #[test]
    fn workspace_member_without_a_field_passes() {
        assert!(allowlist().check("a", None, None, true).is_ok());
    }

    #[test]
    fn dependency_without_a_field_fails_without_an_entry() {
        let list = allowlist();
        assert!(list.check("a", Some("registry+x"), None, false).is_err());
        assert!(list.check("a", None, None, false).is_err());
    }

    #[test]
    fn entry_must_match_name_and_source_at_any_revision() {
        let list = allowlist();
        let source = "git+https://example.org/verus?branch=mars#abc123";
        assert!(list.check("vstd", Some(source), None, false).is_ok());
        assert!(list.check("other", Some(source), None, false).is_err());
        assert!(list.check("vstd", Some("git+https://example.org/fork#abc123"), None, false).is_err());
    }

    #[test]
    fn entry_must_name_an_allowed_license() {
        assert!(Allowlist::parse("license MIT\npackage a b GPL-3.0\n").is_err());
    }

    #[test]
    fn malformed_allowlist_is_an_error() {
        assert!(Allowlist::parse("licence MIT\n").is_err());
        assert!(Allowlist::parse("license\n").is_err());
        assert!(Allowlist::parse("package a b\n").is_err());
    }
}
