use super::append_only_file::AppendOnlyFile;
use anyhow::{Context, Result};
use std::path::Path;

pub struct Partition {
    f: AppendOnlyFile,
}

impl Partition {
    pub fn open<P: AsRef<Path>>(path: P) -> Result<Self> {
        let f = AppendOnlyFile::open(path).with_context(|| "unable to create append-only file")?;
        Ok(Self { f })
    }
}

#[cfg(tests)]
mod tests {
    #[test]
    fn test_partition() {
        // TODO
    }
}
