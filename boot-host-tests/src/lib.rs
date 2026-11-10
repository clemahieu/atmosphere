//! Host runs of the kernel's boot checks, the loader map check (lines starting `free page ranges:`)
//! and the dom0 run check (lines starting `mapped runs:`). Each test module builds the kernel's own
//! file, so the host runs the code the kernel does. The dom0 run check reads the built dom0, so the
//! gate runs these tests after the build.

#[cfg(test)]
mod free_ranges_test;
#[cfg(test)]
mod mapped_runs_test;
