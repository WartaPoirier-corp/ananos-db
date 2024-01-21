//! Various in-memory backends.

use crate::{Error, Io};
use alloc::vec::Vec;

impl Io for [u8] {
    fn read(&mut self, position: u64, buffer: &mut [u8]) -> Result<(), Error> {
        let pos = position as usize;
        for (i, byte) in buffer.iter_mut().enumerate() {
            *byte = self[pos + i];
        }
        Ok(())
    }
    fn write(&mut self, position: u64, buffer: &[u8]) -> Result<(), Error> {
        let pos = position as usize;
        for (i, byte) in buffer.iter().enumerate() {
            self[pos + i] = *byte;
        }
        Ok(())
    }
}

impl<T: Io> Io for alloc::boxed::Box<T> {
    fn read(&mut self, position: u64, buffer: &mut [u8]) -> Result<(), Error> {
        <T as Io>::read(self, position, buffer)
    }
    fn write(&mut self, position: u64, buffer: &[u8]) -> Result<(), Error> {
        <T as Io>::write(self, position, buffer)
    }
}

impl<'a, T: Io> Io for &'a mut T {
    fn read(&mut self, position: u64, buffer: &mut [u8]) -> Result<(), Error> {
        <T as Io>::read(self, position, buffer)
    }
    fn write(&mut self, position: u64, buffer: &[u8]) -> Result<(), Error> {
        <T as Io>::write(self, position, buffer)
    }
}

impl Io for Vec<u8> {
    fn read(&mut self, position: u64, buffer: &mut [u8]) -> Result<(), Error> {
        self[..].read(position, buffer)
    }
    fn write(&mut self, position: u64, buffer: &[u8]) -> Result<(), Error> {
        self[..].write(position, buffer)
    }
}
