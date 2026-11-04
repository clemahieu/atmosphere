//! Check that every external_body in the verified kernel is listed with its reason.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use anyhow::anyhow;

use crate::error::Result;
use crate::project::ProjectHandle;

/// The inventory, relative to the project root: path, item, class and reason, separated by tabs.
const LIST_PATH: &str = "tools/external-body-list";

/// The tree the inventory covers, relative to the project root.
const VERIFIED_ROOT: &str = "kernel/verified";

const CLASSES: [&str; 3] = ["glue", "gap", "unproven"];

/// One attribute, as the list and the source both state it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Item {
    path: String,
    name: String,
    class: String,
    reason: String,
}

/// Checks the sources against the list.
pub(super) fn check(project: &ProjectHandle) -> Result<String> {
    let root = project.root();
    let list = parse_list(&fs::read_to_string(root.join(LIST_PATH))?).map_err(|error| anyhow!(error))?;

    let mut found = vec![];
    let verified = root.join(VERIFIED_ROOT);
    let mut files = vec![];
    collect_sources(&verified, &mut files)?;
    for file in files {
        let path = file.strip_prefix(&verified)?.to_string_lossy().into_owned();
        found.extend(scan(&path, &fs::read_to_string(&file)?).map_err(|error| anyhow!(error))?);
    }

    let differences = compare(&found, &list);
    if !differences.is_empty() {
        return Err(anyhow!("{}", differences.join("; ")));
    }

    let mut classes: BTreeMap<&str, usize> = BTreeMap::new();
    for item in &found {
        *classes.entry(item.class.as_str()).or_default() += 1;
    }
    let totals: Vec<String> = classes.iter().map(|(class, count)| format!("{} {}", count, class)).collect();
    Ok(format!("{} items listed: {}", found.len(), totals.join(", ")))
}

/// Collects the Rust sources under `dir`, leaving out the retired `old` tree.
fn collect_sources(dir: &Path, files: &mut Vec<std::path::PathBuf>) -> Result<()> {
    for entry in fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            if path.file_name().map_or(true, |name| name != "old") {
                collect_sources(&path, files)?;
            }
        } else if path.extension().map_or(false, |extension| extension == "rs") {
            files.push(path);
        }
    }
    Ok(())
}

fn parse_list(text: &str) -> std::result::Result<Vec<Item>, String> {
    let mut items = vec![];
    for line in text.lines() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        match fields.as_slice() {
            [path, name, class, reason] if CLASSES.contains(class) && !reason.trim().is_empty() => {
                items.push(Item {
                    path: path.to_string(),
                    name: name.to_string(),
                    class: class.to_string(),
                    reason: reason.to_string(),
                });
            }
            _ => return Err(format!("{}: cannot read {:?}", LIST_PATH, line)),
        }
    }
    Ok(items)
}

/// Finds each live attribute in one file, with the reason line after it and the item it applies to.
fn scan(path: &str, source: &str) -> std::result::Result<Vec<Item>, String> {
    let lines: Vec<&str> = source.lines().map(str::trim).collect();
    let mut items = vec![];
    for (index, line) in lines.iter().enumerate() {
        if !line.starts_with("#[verifier(external_body)]") {
            continue;
        }
        let at = format!("{}:{}", path, index + 1);
        let reason_line = lines.get(index + 1).copied().unwrap_or("");
        let (class, reason) = parse_reason(reason_line)
            .ok_or_else(|| format!("{}: no reason line in the form // external_body(<class>): <reason>", at))?;
        let name = lines[index + 2..]
            .iter()
            .find_map(|line| item_name(line))
            .ok_or_else(|| format!("{}: no item follows", at))?;
        items.push(Item {
            path: path.to_string(),
            name: name.to_string(),
            class: class.to_string(),
            reason: reason.to_string(),
        });
    }
    Ok(items)
}

fn parse_reason(line: &str) -> Option<(&str, &str)> {
    let (class, reason) = line.strip_prefix("// external_body(")?.split_once("): ")?;
    (CLASSES.contains(&class) && !reason.trim().is_empty()).then_some((class, reason))
}

/// Returns the name of the function a line declares.
fn item_name(line: &str) -> Option<&str> {
    if line.starts_with("//") || line.starts_with("#[") {
        return None;
    }
    let after = line.split_once("fn ")?.1;
    let end = after.find(|c: char| !(c.is_alphanumeric() || c == '_'))?;
    Some(&after[..end])
}

/// Describes every item only one side has.
fn compare(found: &[Item], list: &[Item]) -> Vec<String> {
    let mut differences = vec![];
    let describe = |item: &Item| format!("{} {} ({}: {})", item.path, item.name, item.class, item.reason);
    let mut listed = list.to_vec();
    for item in found {
        match listed.iter().position(|entry| entry == item) {
            Some(index) => {
                listed.swap_remove(index);
            }
            None => differences.push(format!("{} is not on the list", describe(item))),
        }
    }
    for item in &listed {
        differences.push(format!("{} is not in the source", describe(item)));
    }
    differences
}

#[cfg(test)]
mod tests {
    use super::*;

    const ATTR: &str = "#[verifier(external_body)]";

    fn item(path: &str, name: &str, class: &str, reason: &str) -> Item {
        Item { path: path.into(), name: name.into(), class: class.into(), reason: reason.into() }
    }

    #[test]
    fn scan_reads_the_reason_and_the_item() {
        let source = format!("{ATTR}\n// external_body(gap): raw write\npub fn set_state(x: u8)\n    ensures true,\n{{}}\n");
        assert_eq!(scan("a.rs", &source), Ok(vec![item("a.rs", "set_state", "gap", "raw write")]));
    }

    #[test]
    fn scan_handles_proof_fns_and_a_trailing_comment_on_the_attribute() {
        let source = format!("    {ATTR} // a note\n    // external_body(unproven): axiom\n    pub proof fn page_lemma()\n");
        assert_eq!(scan("a.rs", &source), Ok(vec![item("a.rs", "page_lemma", "unproven", "axiom")]));
    }

    #[test]
    fn scan_skips_other_attributes_before_the_item() {
        let source = format!("{ATTR}\n// external_body(glue): hw\n#[inline(always)]\npub const fn zeroed() -> Self {{}}\n");
        assert_eq!(scan("a.rs", &source), Ok(vec![item("a.rs", "zeroed", "glue", "hw")]));
    }

    #[test]
    fn scan_ignores_a_commented_attribute() {
        assert_eq!(scan("a.rs", &format!("// {ATTR}\npub fn f() {{}}\n")), Ok(vec![]));
    }

    #[test]
    fn scan_rejects_a_missing_reason() {
        assert!(scan("a.rs", &format!("{ATTR}\npub fn f() {{}}\n")).is_err());
    }

    #[test]
    fn scan_rejects_an_unknown_class_and_an_empty_reason() {
        assert!(scan("a.rs", &format!("{ATTR}\n// external_body(later): x\npub fn f() {{}}\n")).is_err());
        assert!(scan("a.rs", &format!("{ATTR}\n// external_body(gap): \npub fn f() {{}}\n")).is_err());
    }

    #[test]
    fn list_has_four_tab_separated_fields() {
        assert_eq!(parse_list("# note\n\na.rs\tf\tgap\traw write\n"), Ok(vec![item("a.rs", "f", "gap", "raw write")]));
        assert!(parse_list("a.rs\tf\tgap\n").is_err());
        assert!(parse_list("a.rs\tf\tlater\tx\n").is_err());
    }

    #[test]
    fn compare_reports_each_side() {
        let a = item("a.rs", "f", "gap", "x");
        let b = item("a.rs", "g", "gap", "x");
        assert!(compare(&[a.clone()], &[a.clone()]).is_empty());
        let unlisted = compare(&[a.clone(), b.clone()], &[a.clone()]);
        assert!(unlisted.len() == 1 && unlisted[0].contains("not on the list"), "{:?}", unlisted);
        let gone = compare(&[a.clone()], &[a.clone(), b.clone()]);
        assert!(gone.len() == 1 && gone[0].contains("not in the source"), "{:?}", gone);
    }

    #[test]
    fn compare_counts_duplicates_in_one_file() {
        let a = item("trap.rs", "set_self_fast", "unproven", "x");
        assert!(!compare(&[a.clone(), a.clone()], &[a.clone()]).is_empty());
        assert!(compare(&[a.clone(), a.clone()], &[a.clone(), a.clone()]).is_empty());
    }

    #[test]
    fn a_changed_reason_shows_on_both_sides() {
        let source = item("a.rs", "f", "gap", "x");
        let listed = item("a.rs", "f", "gap", "y");
        assert_eq!(compare(&[source], &[listed]).len(), 2);
    }
}
