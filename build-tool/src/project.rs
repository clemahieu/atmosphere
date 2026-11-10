//! Project.

use std::path::PathBuf;
use std::sync::Arc;

use anyhow::anyhow;

use cargo_metadata::MetadataCommand;

use super::error::Result;

/// A handle to a project.
pub type ProjectHandle = Arc<Project>;

/// The Atmosphere project.
#[derive(Debug)]
pub struct Project {
    root: PathBuf,
}

impl Project {
    /// Automatically discover the Atmosphere project root.
    pub fn discover() -> Result<ProjectHandle> {
        let metadata = MetadataCommand::new().no_deps().exec()?;

        // sanity check
        let has_kernel = metadata
            .workspace_packages()
            .iter()
            .any(|pkg| pkg.name == "kernel");

        if !has_kernel {
            return Err(anyhow!(
                "Invalid workspace - The kernel crate (\"kernel\") doesn't exist"
            ));
        }

        let root = metadata.workspace_root.into_std_path_buf();
        Ok(Arc::new(Self { root }))
    }

    /// Returns the path to the workspace root.
    pub fn root(&self) -> PathBuf {
        self.root.clone()
    }
}
