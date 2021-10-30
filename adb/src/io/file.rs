//! [`File`] backend.

use std::fs::File;
use crate::{Error, Io};

impl Io for File {
    fn read(&mut self, position: u64, buffer: &mut [u8]) -> Result<(), Error> {
        use std::io::{Read, Seek, SeekFrom};

        if self.stream_position().unwrap_or(0) != position {
            self.seek(SeekFrom::Start(position)).map_err(|_| Error::ReadError)?;
        }
        self.read_exact(buffer).map_err(|_| Error::ReadError)
    }
    
    fn write(&mut self, position: u64, buffer: &[u8]) -> Result<(), Error> {
        use std::io::{Write, Seek, SeekFrom};

        if self.stream_position().unwrap_or(0) != position {
            self.seek(SeekFrom::Start(position)).map_err(|_| Error::WriteError)?;
        }
        self.write_all(buffer).map_err(|_| Error::WriteError)?;
        self.sync_all().map_err(|_| Error::WriteError)
    }
}
