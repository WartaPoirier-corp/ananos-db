//! I/O backends

use crate::Error;

#[cfg(not(feature = "no_std"))]
mod file;
mod memory;

/// Represents a backend for the database.
pub trait Io: core::fmt::Debug {
    /// Reads some bytes.
    ///
    /// # Parameters
    ///
    /// - `position`: the offset at which to read
    /// - `buffer`: a buffer in which to write the data that has been read.
    ///    The backend should try to fill has much of it as possible, but may
    ///    write less if there is not enough data until the end of the database.
    ///
    /// # Returns
    ///
    /// `Ok(())` if everything went well, `Err(e)` if there was an error. `e` will
    /// usually be [`Error::ReadError`].
    fn read(&mut self, position: u64, buffer: &mut [u8]) -> Result<(), Error>;

    /// Writes some bytes.
    ///
    /// # Parameters
    ///
    /// - `position`: the offset at which to write
    /// - `buffer`: a buffer containing the data to write. The backend should
    ///    try to write as much as possible of this buffer, but may stop before
    ///    the end if there is no space left.
    ///
    /// # Returns
    ///
    /// `Ok(())` if everything went well, `Err(e)` if there was an error. `e` will
    /// usually be [`Error::WriteError`].
    fn write(&mut self, position: u64, buffer: &[u8]) -> Result<(), Error>;

    /// Utility function to read a `u16` from the database.
    ///
    /// # Parameters
    ///
    /// - `position`: the offset at which the `u16` is.
    ///
    /// # Returns
    ///
    /// `Ok(value)` if everything went well, `Err(e)` if there was an error.
    fn read_u16(&mut self, position: u64) -> Result<u16, Error> {
        let mut buf = [0; 2];
        self.read(position, &mut buf)?;
        Ok(u16::from_be_bytes(buf))
    }

    /// Utility function to read a `u64` from the database.
    ///
    /// # Parameters
    ///
    /// - `position`: the offset at which the `u64` is.
    ///
    /// # Returns
    ///
    /// `Ok(value)` if everything went well, `Err(e)` if there was an error.
    fn read_u64(&mut self, position: u64) -> Result<u64, Error> {
        let mut buf = [0; 8];
        self.read(position, &mut buf)?;
        Ok(u64::from_be_bytes(buf))
    }
}
