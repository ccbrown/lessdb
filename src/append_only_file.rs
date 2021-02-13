use anyhow::Context;
use std::{
    convert::{TryFrom, TryInto},
    fs::File,
    io::{self, Read, Seek, SeekFrom, Write},
    path::Path,
};
use thiserror::Error;

pub struct AppendOnlyFile {
    f: File,
    size: u64,
    last_entry_offset: Option<u64>,
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("corruption")]
    Corruption,
    #[error("io error")]
    IOError(#[from] io::Error),
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}

type Result<T> = std::result::Result<T, Error>;

pub const ENTRY_PREFIX_LENGTH: usize = 8; // 4 byte length + 4 byte crc

impl AppendOnlyFile {
    /// Opens the append-only file at the given path, creating it if it doesn't exist.
    pub fn open<P: AsRef<Path>>(path: P) -> Result<Self> {
        let mut f = std::fs::OpenOptions::new()
            .create(true)
            .write(true)
            .read(true)
            .open(path)?;
        let size = f.seek(SeekFrom::End(0))?;
        let mut ret = Self {
            f,
            size,
            last_entry_offset: None,
        };
        let mut last_entry_offset = None;
        for entry in ret.entries() {
            last_entry_offset = Some(entry?.offset);
        }
        ret.last_entry_offset = last_entry_offset;
        Ok(ret)
    }

    /// Moves the cursor to the end of the verified portion of the file and writes an entry to it.
    pub fn append(&mut self, data: &[u8]) -> Result<()> {
        let len = u32::try_from(data.len()).with_context(|| "unsupported data length")?;
        self.f.seek(SeekFrom::Start(self.size))?;
        self.f.write_all(&len.to_be_bytes())?;
        let mut crc = crc32fast::Hasher::new();
        crc.update(&data);
        self.f.write_all(&crc.finalize().to_be_bytes())?;
        self.f.write_all(&data)?;
        // TODO: is syncing worth the insane performance hit?
        self.last_entry_offset = Some(self.size);
        self.size += ENTRY_PREFIX_LENGTH as u64 + len as u64;
        Ok(())
    }

    /// Reads an entry from the current position.
    pub fn read_entry(&mut self) -> Result<Vec<u8>> {
        let mut header = [0u8; ENTRY_PREFIX_LENGTH];
        self.f.read_exact(&mut header).map_err(|e| match e.kind() {
            io::ErrorKind::UnexpectedEof => Error::Corruption,
            _ => e.into(),
        })?;

        let len = u32::from_be_bytes((&header[..4]).try_into().expect("we know this is 4 bytes"))
            as usize;
        let expected_crc =
            u32::from_be_bytes((&header[4..]).try_into().expect("we know this is 4 bytes"));

        let mut data = Vec::with_capacity(len);
        let read_len = (&self.f).take(len as _).read_to_end(&mut data)?;
        if read_len != len {
            return Err(Error::Corruption);
        }

        let mut crc = crc32fast::Hasher::new();
        crc.update(&data);
        if crc.finalize() != expected_crc {
            return Err(Error::Corruption);
        }

        Ok(data)
    }

    /// Iterates through entries, beginning at the start of the file.
    pub fn entries(&mut self) -> Entries {
        Entries { offset: 0, f: self }
    }

    /// The size of the file. The next entry will be written to this offset. The data for the next
    /// entry will be written to this offset plus ENTRY_PREFIX_LENGTH.
    pub fn size(&self) -> u64 {
        self.size
    }

    /// Returns the offset of the last entry in the file, if any.
    pub fn last_entry_offset(&self) -> Option<u64> {
        self.last_entry_offset
    }
}

impl Read for AppendOnlyFile {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.f.read(buf)
    }
}

impl Seek for AppendOnlyFile {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        self.f.seek(pos)
    }
}

#[derive(Debug, PartialEq)]
pub struct Entry {
    /// The offset of the entry within the file. The offset of the data is this plus
    /// `ENTRY_PREFIX_LENGTH`.
    pub offset: u64,

    /// The original data.
    pub data: Vec<u8>,
}

pub struct Entries<'a> {
    offset: u64,
    f: &'a mut AppendOnlyFile,
}

impl<'a> Iterator for Entries<'a> {
    type Item = Result<Entry>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset >= self.f.size {
            None
        } else {
            if self.offset == 0 {
                if let Err(e) = self.f.seek(SeekFrom::Start(0)) {
                    return Some(Err(e.into()));
                }
            }
            match self.f.read_entry() {
                Ok(data) => {
                    let entry = Entry {
                        offset: self.offset,
                        data,
                    };
                    self.offset += (ENTRY_PREFIX_LENGTH + entry.data.len()) as u64;
                    Some(Ok(entry))
                }
                Err(e) => Some(Err(e.into())),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempdir::TempDir;

    #[test]
    fn test_append_only_file() {
        let dir = TempDir::new("aof-test").unwrap();
        let path = dir.path().join("aof");

        let expected_entries = vec![
            Entry {
                offset: 0,
                data: "foo".as_bytes().to_vec(),
            },
            Entry {
                offset: ENTRY_PREFIX_LENGTH as u64 + 3,
                data: "bar".as_bytes().to_vec(),
            },
        ];

        // create the file and add some entries
        {
            let mut f = AppendOnlyFile::open(&path).unwrap();
            f.append("foo".as_bytes()).unwrap();
            f.append("bar".as_bytes()).unwrap();
            assert_eq!(f.last_entry_offset(), Some(11));

            assert_eq!(
                f.entries().collect::<Result<Vec<_>>>().unwrap(),
                expected_entries,
            );
            assert_eq!(f.size(), 2 * (ENTRY_PREFIX_LENGTH + 3) as u64);
        }

        // verify that everything looks fine after re-opening the file
        {
            let mut f = AppendOnlyFile::open(&path).unwrap();
            assert_eq!(f.last_entry_offset(), Some(11));

            assert_eq!(
                f.entries().collect::<Result<Vec<_>>>().unwrap(),
                expected_entries,
            );
            assert_eq!(f.size(), 2 * (ENTRY_PREFIX_LENGTH + 3) as u64);
        }

        // corrupt the second entry in the file
        {
            let mut f = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
            f.seek(SeekFrom::Start(20)).unwrap();
            f.write(&[0]).unwrap();
        }

        // the file should now be corrupt
        {
            match AppendOnlyFile::open(&path) {
                Err(Error::Corruption) => {}
                _ => panic!("expected corruption"),
            }
        }
    }
}
