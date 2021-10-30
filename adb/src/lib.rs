//! Crate to read and write to ananOS databases.
//!
//! The main type is [`Db`].

#![cfg_attr(feature = "no_std", no_std)]

extern crate alloc;

use alloc::sync::Arc;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use alloc::vec;
use alloc::string::String;
use alloc::borrow::ToOwned;
use core::convert::TryInto;

pub mod io;
pub mod objects;
pub mod types;
pub mod type_ids;

pub use io::Io;
pub use objects::{DbObject, DbValue};
pub use types::{TypeId, TypeDef, TypeInfo};

/// Errors that can happen when manipulating a DB.
#[derive(Debug)]
pub enum Error {
    /// This is not an ananOS DB.
    NotDb,
    /// The version of the database is not supported by this
    /// version of the `adb` crate.
    IncompatibleVersion,
    /// There was an error while reading data from the [`Io`] backend.
    ReadError,
    /// There was an error while writing data from the [`Io`] backend.
    WriteError,
    /// The database needed information about a given type but couldn't find it.
    MissingTypeInfo(TypeId),
    /// There is no more space in the database.
    NoSpaceLeft,
}

/// Represent a block in the database.
///
/// ananOS databases are split into blocks. Each block contains
/// objects from a given type. The type of a block is specified
/// in the type table located at the start of the database.
///
/// A block starts with a `u64` indicating how many items this block contains (this number will be
/// called *N*).
/// Then, there is another `u64` indicating how much space is already occupied in this block,
/// including both the actual objects, and the block header.
/// After that comes *N* `u64`, each indicating an offset in the block at which an object can be
/// found. Having this list of pointers allows to have objects of different sizes (some types,
/// like arrays don't have a fixed size, so knowing the type doesn't give the size of all objects
/// of this type).
///
/// Objects are written from the end of the block.
#[derive(Debug)]
pub struct Block {
    /// The data of this block
    buffer: Vec<u8>,
}

impl Block {
    /// Iterates over the objects in a block
    fn iter(&self) -> BlockIterator {
        BlockIterator {
            buffer: self.buffer.clone(),
            item_count: u64::from_be_bytes(self.buffer[0..8].try_into().unwrap()),
            current_item: 0,
        }
    }
}

/// An iterator over objects of a [`Block`].
#[derive(Debug, Clone)]
struct BlockIterator {
    /// The buffer of the block
    buffer: Vec<u8>,
    /// The number of objects in the block
    item_count: u64,
    /// The index of the current object
    current_item: usize,
}

impl<'a> Iterator for BlockIterator {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        // end of the block
        if self.item_count <= (self.current_item as u64) {
            return None;
        }

        // compute the pointer for the current object
        let pointer_start = 16 + (self.current_item * 8);
        let pointer_end = pointer_start + 8;
        let pointer = u64::from_be_bytes(self.buffer[pointer_start..pointer_end].try_into().unwrap());

        // compute the size of the object
        let size = if self.current_item == 0 {
            // for the first object, look how far from the end is the pointer
            self.buffer.len() - (pointer as usize)
        } else {
            // for other objects, compute the pointer of the previous object,
            // the size being the distance between the two
            let prev_pointer_start = pointer_start - 8;
            let prev_pointer_end = pointer_start;
            let prev_pointer = u64::from_be_bytes(self.buffer[prev_pointer_start..prev_pointer_end].try_into().unwrap());
            (prev_pointer - pointer) as usize
        };

        // compute the end of the object
        let end = (pointer as usize) + size;

        // iterate
        self.current_item += 1;

        // return the slice containing the object
        Some(self.buffer[(pointer as usize)..end].to_owned())
    }
}

/// An ananOS database.
///
/// # Format
///
/// Independently from the backend (file, partition on a disk, in memory buffer, …), a database can
/// be represented as a byte array. The bytes are laid out in a specific format that can be parsed
/// into a [`Db`] with [`Db::read_from`].
///
/// There are two parts in the database: the header, and the blocks.
///
/// All numbers are encoded in big endian.
///
/// ## Header
///
/// The header starts with a magic number (`0xADB`), and 3 `u16` indicating the
/// version number of the database (respectively major, minor and patch).
/// Then comes two `u64`: one for the number of blocks (called *N*), and one for the size of
/// a single block. Databases are divided in [`Block`]s. Each blocks stores object
/// from a single type.
///
/// After there two numbers, there is a checksum of the database (not yet implemented),
/// on 64 bytes.
///
/// After that comes two copy of the *type table*. This table contains *N* entries, that
/// are `u64`. These numbers corresponds to the [`TypeId`] of the type stored in the corresponding
/// block. For instance, if the type ID of `u8` is `0` and the type ID of `u16` is `1`, then a
/// database that contains two blocks of `u8` followed by one block of `u16` would have the
/// following type table:
///
/// ```
/// 00 00 00 00 00 00 00 00
/// 00 00 00 00 00 00 00 00
/// 00 00 00 00 00 00 00 01
/// ```
///
/// After the type table starts the actual blocks.
///
/// ## Blocks
///
/// For the format of a block, see [`Block`].
pub struct Db<I: Io> {
    /// The number of block in a database.
    block_count: u64,
    /// The size of a single block.
    block_size: u64,
    /// A cache of the blocks in the database.
    blocks_cache: BTreeMap<u64, Block>,
    /// A cache of the types that are known.
    type_cache: BTreeMap<TypeId, Arc<TypeInfo>>,
    /// The type table.
    type_table: Vec<TypeId>,
    /// The I/O backend.
    io: I,
    /// A logger.
    ///
    /// In some environment (for instance: OS kernels) `std::println!` and
    /// other similar macros are not available, and this function is used to
    /// provide logging.
    logger: Option<fn(core::fmt::Arguments)> // TODO: use the log crate instead
}

// Custom impl because `Debug` is not implemented for function pointers
impl<I: Io> core::fmt::Debug for Db<I> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Db")
            .field("block_count", &self.block_count)
            .field("block_size", &self.block_size)
            .field("blocks_cache", &self.blocks_cache)
            .field("type_cache", &self.type_cache)
            .field("type_table", &self.type_table)
            .finish()
    }
}

// the size of the database header, without the type tables.
// 2 -> magic number
// 6 -> version
// 8 -> block count
// 8 -> block size
// 64 -> checksum
const HEADER_SIZE: u64 = 2 + 6 + 8 + 8 + 64;

impl<I: Io> Db<I> {
    /// Initializes a database.
    ///
    /// # Parameters
    ///
    /// - `io`: the I/O backend from which to read and write data.
    pub fn read_from(mut io: I) -> Result<Self, Error> {
        let magic = io.read_u16(0)?;
        if magic != 0xADB {
            return Err(Error::NotDb);
        }

        // DB Version
        let major = io.read_u16(2)?;
        let minor = io.read_u16(4)?;
        let patch = io.read_u16(6)?;
        match (major, minor, patch) {
            (0, 1, 0) => {},
            _ => return Err(Error::IncompatibleVersion)
        }

        let block_count = io.read_u64(8)?;
        let block_size = io.read_u64(16)?;

        // TODO: real checksum
        let mut checksum = [0; 64];
        io.read(24, &mut checksum)?;
        let use_backup_table = checksum.iter().any(|x| *x != 0);
        
        let type_table_start = if use_backup_table {
            88 + (8 * block_count)
        } else {
            88
        };

        let mut block_types = Vec::with_capacity(block_count as usize);
        let mut type_blocks = Vec::with_capacity(8); // Safe to assume that in most case there will be at least 8 type blocks
        for i in 0..block_count {
            let block_pos = type_table_start + (8 * i);
            let type_id = io.read_u64(block_pos)?;
            block_types.push(TypeId(type_id));
            if type_id == type_ids::TYPE.0 {
                type_blocks.push(i as u64);
            }
        }

        let mut db = Self {
            block_count,
            block_size,
            blocks_cache: BTreeMap::new(),
            type_cache: BTreeMap::new(),
            type_table: block_types,
            io,
            logger: None,
        };
        
        /* Layout of the Type type:
        
           |       name : str      | id : TypeId | kind : Sum+Product | fields_or_variants : Vec<str * TypeId> |
           | len : u64 | buff : [] |             |                    |     len : u64     |     buff : []      |
        
        */

        for type_block in type_blocks {
            let block = db.fetch_block(type_block, false)?;
            for item in block.iter() {
                // Type name
                let name = read_string(&item);

                // Type ID
                let pos = 8 + name.len();
                let type_id = u64::from_be_bytes(item[pos..(pos + 8)].try_into().unwrap());

                // Type kind
                let kind = item[(pos + 15)..(pos + 16)][0];

                // Fields or Variants
                let fov_len = u64::from_be_bytes(item[(pos + 16)..(pos + 24)].try_into().unwrap()) as usize;
                let mut fov = Vec::with_capacity(fov_len);
                let mut pos = pos + 24;
                for _ in 0..fov_len {
                    let fov_name = read_string(&item[pos..]);
                    pos += 8 + fov_name.len();
                    let fov_ty = u64::from_be_bytes(item[pos..(pos + 8)].try_into().unwrap());
                    pos += 8;
                    fov.push((fov_name, TypeId(fov_ty)));
                }

                db.type_cache.insert(TypeId(type_id), Arc::new(TypeInfo {
                    name,
                    id: TypeId(type_id),
                    definition: if kind == 0 { // Sum
                        TypeDef::Sum {
                            variants: fov,
                        }
                    } else { // Product
                        TypeDef::Product {
                            fields: fov,
                        }
                    },
                }));
            }
        }

        Ok(db)
    }

    /// Returns type information about a given type.
    ///
    /// # Parameters
    ///
    /// - `ty`: the ID of the requested type
    ///
    /// # Returns
    ///
    /// `Ok` if the type was known, `Err(Error::MissingTypeInfo)` if it was not.
    pub fn get_type_info(&self, ty: TypeId) -> Result<Arc<TypeInfo>, Error> {
        // TODO: just insert that in the cache when creating the db
        match ty { // TODO: add missing core types
            type_ids::NEVER => Ok(Arc::new(TypeInfo {
                name: String::from("Core.Never"),
                id: type_ids::NEVER,
                definition: TypeDef::Never,
            })),
            type_ids::UNIT => Ok(Arc::new(TypeInfo {
                name: String::from("Core.Unit"),
                id: type_ids::UNIT,
                definition: TypeDef::Unit,
            })),
            type_ids::TYPE => Ok(Arc::new(TypeInfo {
                name: String::from("Core.Type"),
                id: type_ids::TYPE,
                definition: TypeDef::Product {
                    fields: vec![
                        (String::from("name"), type_ids::STR),
                        (String::from("id"), type_ids::U64),
                        (String::from("definition"), type_ids::TYPEDEF),
                    ]
                }
            })),
            type_ids::TYPEDEF => Ok(Arc::new(TypeInfo {
                name: String::from("Core.TypeDefinition"),
                id: type_ids::TYPEDEF,
                definition: TypeDef::Sum {
                    variants: vec![
                        (String::from("never"), type_ids::UNIT),
                        (String::from("unit"), type_ids::UNIT),
                        (String::from("u8"), type_ids::UNIT),
                        (String::from("u16"), type_ids::UNIT),
                        (String::from("u32"), type_ids::UNIT),
                        (String::from("u64"), type_ids::UNIT),
                        (String::from("i8"), type_ids::UNIT),
                        (String::from("i16"), type_ids::UNIT),
                        (String::from("i32"), type_ids::UNIT),
                        (String::from("i64"), type_ids::UNIT),
                        (String::from("f32"), type_ids::UNIT),
                        (String::from("f64"), type_ids::UNIT),
                        (String::from("array"), type_ids::TYPE_ID),
                        (String::from("sum"), type_ids::FIELD_ARRAY),
                        (String::from("product"), type_ids::FIELD_ARRAY),
                    ]
                }
            })),
            type_ids::FIELD_ARRAY => Ok(Arc::new(TypeInfo {
                name: String::from("[Core.Field]"),
                id: type_ids::FIELD_ARRAY,
                definition: TypeDef::Array(type_ids::FIELD),
            })),
            type_ids::FIELD => Ok(Arc::new(TypeInfo {
                name: String::from("Core.Field"),
                id: type_ids::FIELD,
                definition: TypeDef::Product {
                    fields: vec![
                        (String::from("name"), type_ids::STR),
                        (String::from("type"), type_ids::TYPE_ID),
                    ],
                },
            })),
            type_ids::TYPE_ID => Ok(Arc::new(TypeInfo {
                name: String::from("Core.TypeId"),
                id: type_ids::TYPE_ID,
                definition: TypeDef::U64,
            })),
            type_ids::STR => Ok(Arc::new(TypeInfo {
                name: String::from("Core.String"),
                id: type_ids::STR,
                definition: TypeDef::Array(type_ids::U8),
            })),
            type_ids::U8 => Ok(Arc::new(TypeInfo {
                name: String::from("Core.U8"),
                id: type_ids::U8,
                definition: TypeDef::U8,
            })),
            type_ids::U64 => Ok(Arc::new(TypeInfo {
                name: String::from("Core.U64"),
                id: type_ids::U64,
                definition: TypeDef::U64,
            })),
            _ => self.type_cache.get(&ty).map(Arc::clone).ok_or(Error::MissingTypeInfo(ty)),
        }
    }

    /// Fetches a block from the backend.
    ///
    /// If the block is present in the cache and `force_update` is false,
    /// it will not be re-read.
    fn fetch_block(&mut self, block_num: u64, force_update: bool) -> Result<&Block, Error> {
        if force_update || !self.blocks_cache.contains_key(&block_num) {
            let data_start = HEADER_SIZE + self.block_count * 8 * 2;
            let block_start = data_start + (block_num * self.block_size);
            let mut buf = vec![0; self.block_size as usize];
            self.io.read(block_start, &mut buf)?;
            self.blocks_cache.insert(block_num, Block {
                buffer: buf,
            });
        }
        Ok(self.blocks_cache.get(&block_num).unwrap())
    }

    /// Iterates over all the objects of a given type.
    pub fn iter_type<'a>(&'a mut self, ty: TypeId) -> TypeIterator<'a, I> {
        let type_info = self.get_type_info(ty).unwrap();
        let blocks = self.type_table.iter().enumerate().filter(|(_, x)| **x == ty).map(|(i, _)| i as u64).collect();
        TypeIterator {
            db: self,
            type_info,
            blocks,
            current_block: None,
        }
    }

    /// List all the type IDs that are present in the database.
    pub fn all_type_ids(&self) -> Vec<TypeId> {
        let mut types = self.type_table.clone();
        types.sort_by_key(|x| x.0);
        types.dedup();
        types
    }

    /// Finds a free block in the database.
    ///
    /// A free block is a block that currently stores the never type (ID `0`).
    ///
    /// If no free block is available, `None` is returned.
    fn find_free_block(&self) -> Option<usize> {
        self.type_table.iter()
            .enumerate()
            .find(|(_, x)| x.0 == 0)
            .map(|(i, _)| i)
    }

    /// Persists the type table.
    fn write_type_table(&mut self) -> Result<(), Error> {
        let mut tt = Vec::with_capacity(self.block_count as usize * 8);
        for ty in &self.type_table {
            let bytes = ty.0.to_be_bytes();
            for byte in bytes {
                tt.push(byte)
            }
        }
        self.io.write(HEADER_SIZE, &tt)?;
        self.io.write(HEADER_SIZE + tt.len() as u64, &tt)
    }

    /// Tries to find a free block and assigns it a type.
    ///
    /// # Returns
    ///
    /// `Ok((block_index, block_start_offset))` if everything went well.
    fn allocate_block(&mut self, ty: TypeId) -> Result<(u64, u64), Error> {
        if let Some(free_idx) = self.find_free_block() {
            self.type_table[free_idx] = ty;
            self.write_type_table()?;
            self.blocks_cache.insert(free_idx as u64, Block { buffer: vec![0; self.block_size as usize] });
            Ok((free_idx as u64, HEADER_SIZE + (self.block_count * 2 * 8) + (free_idx as u64 * self.block_size)))
        } else {
            return Err(Error::NoSpaceLeft);
        }
    }

    /// Persists a [`DbObject`].
    pub fn write_object(&mut self, obj: DbObject) -> Result<(), Error> {
        let size = obj.size(&self);

        // allocate a new block for the object
        let (block_id, block_start) = self.allocate_block(obj.type_info.id)?; // TODO: look for blocks with some space left
        let buff = &mut self.blocks_cache.get_mut(&block_id).unwrap().buffer;

        // write a 1 at the start of the block, since it will only contain one object
        for (i, byte) in 1u64.to_be_bytes().iter().enumerate() {
            buff[i] = *byte;
        }

        // write the size occupied by the single object of the block
        for (i, byte) in size.to_be_bytes().iter().enumerate() {
            buff[8 + i] = *byte;
        }

        // write the pointer to the object
        let start = self.block_size as usize - size;
        for (i, byte) in start.to_be_bytes().iter().enumerate() {
            buff[16 + i] = *byte;
        }

        // write the value of the object at the end of the block
        obj.value.write(&mut buff[start..])?;
        self.io.write(block_start, buff)?;

        // if the type of the object is not yet in the database itself, write it too
        if self.get_type_info(obj.type_info.id).is_err() {
            self.type_cache.insert(obj.type_info.id, Arc::clone(&obj.type_info));
            let type_info = obj.type_info.into_runtime();
            let type_info_obj = DbObject {
                type_info: Arc::new(TypeInfo::type_info()),
                value: Arc::clone(&type_info),
            };
            self.write_object(type_info_obj)?;
        }

        Ok(())
    }

    /// Defines the logger to use.
    pub fn set_logger(&mut self, logger: fn(core::fmt::Arguments)) {
        self.logger = Some(logger);
    }

    /// Logs a message using the logger, if it is defined.
    fn log(&self, args: core::fmt::Arguments) {
        if let Some(log) = self.logger {
            log(args);
        }
    }
}

/// Iterator over all the object of a given type.
#[derive(Debug)]
pub struct TypeIterator<'a, I: Io> {
    db: &'a mut Db<I>,
    type_info: Arc<TypeInfo>,
    blocks: Vec<u64>,
    current_block: Option<BlockIterator>,
}

impl<'a, I: Io> TypeIterator<'a, I> {
    /// Information about the type of this iterator.
    pub fn ty(&self) -> Arc<TypeInfo> {
        Arc::clone(&self.type_info)
    }
}

impl<'a, I: Io> Iterator for TypeIterator<'a, I> {
    type Item = DbObject;

    fn next(&mut self) -> Option<Self::Item> {
        let next = match self.current_block {
            Some(ref mut x) => x.next(),
            None => None,
        };
        if let Some(data) = next {
            deser_value(&data, Arc::clone(&self.type_info), self.db).map(|x| x.0)
        } else {
            if let Some(next_block) = self.blocks.pop() {
                let block = self.db.fetch_block(next_block, true).ok().clone();
                self.current_block = block.map(|b| b.iter());
                self.next()
            } else {
                None
            }
        }
    }
}

/// Reads an object from a buffer.
///
/// # Parameters
///
/// - `data`: the buffer containing the object
/// - `type_info`: the type of the object
/// - `db`: a reference to the database, required to query more type information
///
/// # Returns
///
/// `Some((object, number_of_bytes))` if everything went well. `number_of_bytes` is the number
/// of bytes that were read from the buffer to deserialize this object.
///
/// # Panics
///
/// This function panics if a value of type `!` (never) is built.
fn deser_value<I: Io>(data: &[u8], type_info: Arc<TypeInfo>, db: &Db<I>) -> Option<(DbObject, usize)> {
    match type_info.definition {
        TypeDef::Never => panic!("Tried to construct the '!' type"),
        TypeDef::Unit => Some((type_info.construct(DbValue::Unit), 0)),
        TypeDef::U8 => Some((type_info.construct(DbValue::U8(
            data[0]
        )), 1)),
        TypeDef::U16 => Some((type_info.construct(DbValue::U64(
            u64::from_be_bytes([0, 0, 0, 0, 0, 0, data[0], data[1]])
        )), 2)),
        TypeDef::U32 => Some((type_info.construct(DbValue::U64(
            u64::from_be_bytes([0, 0, 0, 0, data[0], data[1], data[2], data[3]])
        )), 4)),
        TypeDef::U64 => Some((type_info.construct(DbValue::U64(
            u64::from_be_bytes(data[0..8].try_into().unwrap())
        )), 8)),
        TypeDef::I8 => Some((type_info.construct(DbValue::U64(
            data[0] as u64
        )), 1)),
        TypeDef::I16 => Some((type_info.construct(DbValue::U64(
            u64::from_be_bytes([0, 0, 0, 0, 0, 0, data[0], data[1]])
        )), 2)),
        TypeDef::I32 => Some((type_info.construct(DbValue::U64(
            u64::from_be_bytes([0, 0, 0, 0, data[0], data[1], data[2], data[3]])
        )), 4)),
        TypeDef::I64 => Some((type_info.construct(DbValue::U64(
            u64::from_be_bytes(data[0..8].try_into().unwrap())
        )), 8)),
        TypeDef::F32 => Some((type_info.construct(DbValue::F64(
            f64::from_be_bytes([0, 0, 0, 0, data[0], data[1], data[2], data[3]])
        )), 4)),
        TypeDef::F64 => Some((type_info.construct(DbValue::F64(
            f64::from_be_bytes(data[0..8].try_into().unwrap())
        )), 8)),
        TypeDef::Array(inner_type) => {
            let inner_type = db.get_type_info(inner_type).ok()?;
            let len = u64::from_be_bytes(data[0..8].try_into().unwrap()) as usize;
            let mut vec = Vec::with_capacity(len);
            let mut start = 8;
            for _ in 0..len {
                let (obj, size) = deser_value(&data[start..], Arc::clone(&inner_type), db)?;
                start += size;
                vec.push(obj.value);
            }
            Some((type_info.construct(DbValue::Array(vec)), start))
        },
        TypeDef::Sum { ref variants } => {
            let tag = u64::from_be_bytes(data[0..8].try_into().unwrap());
            let data_type = db.get_type_info(variants[tag as usize].1).ok()?;
            let (data, size) = deser_value(&data[8..], data_type, db)?;
            Some((type_info.construct(DbValue::Sum {
                variant: tag,
                data: data.value,
            }), 8 + size))
        },
        TypeDef::Product { ref fields } => {
            let mut field_values = Vec::with_capacity(fields.len());
            let mut total_size = 0;
            for (_, field_type_id) in fields {
                let field_type = db.get_type_info(*field_type_id).unwrap();
                let (field_val, size) = deser_value(&data[total_size..], field_type, db)?;
                total_size += size;
                field_values.push(field_val.value);
            }

            Some((type_info.construct(DbValue::Product {
                fields: field_values,
            }), total_size))
        },
    }
}

/// Reads an UTF-8 encoded string from a buffer.
fn read_string(buffer: &[u8]) -> String {
    let len = u64::from_be_bytes(buffer[0..8].try_into().unwrap()) as usize;
    let buf = &buffer[8..(8 + len)];
    let string = core::str::from_utf8(buf).unwrap_or("ERROR").to_owned();
    string
}

