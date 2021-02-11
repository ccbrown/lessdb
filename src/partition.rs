use super::{append_only_file::AppendOnlyFile, b_tree_2d};
use anyhow::{Context, Result};
use std::{path::Path, sync::Arc};

pub struct Partition {
    f: AppendOnlyFile,
}

pub type Binary = Arc<Vec<u8>>;
pub type Tree = b_tree_2d::Tree<Binary, Binary, Binary>;

impl Partition {
    pub fn open<P: AsRef<Path>>(path: P) -> Result<Self> {
        let f = AppendOnlyFile::open(path).with_context(|| "unable to create append-only file")?;
        Ok(Self { f })
    }

    pub fn commit<F: FnOnce(Tree) -> Tree>(&mut self, op: F) -> Result<()> {
        // TODO
        unimplemented!()
    }
}

#[cfg(tests)]
mod tests {
    #[test]
    fn test_partition() {
        // TODO
    }
}
