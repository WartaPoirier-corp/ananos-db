#![cfg_attr(feature = "no_std", no_std)]

extern crate alloc;

use alloc::sync::Arc;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use alloc::vec;
use alloc::string::String;
use crate::alloc::borrow::ToOwned;
use core::convert::TryInto;
use alloc::string::ToString;

#[derive(Debug)]
pub enum Error {
    NotDb,
    IncompatibleVersion,
    ReadError,
    WriteError,
    MissingTypeInfo(TypeId),
    NoSpaceLeft,
}

pub trait Io: core::fmt::Debug {
    fn read(&mut self, position: u64, buffer: &mut [u8]) -> Result<(), Error>;
    
    fn write(&mut self, position: u64, buffer: &[u8]) -> Result<(), Error>;

    fn read_u16(&mut self, position: u64) -> Result<u16, Error> {
        let mut buf = [0; 2];
        self.read(position, &mut buf)?;
        Ok(u16::from_be_bytes(buf))
    }

    fn read_u64(&mut self, position: u64) -> Result<u64, Error> {
        let mut buf = [0; 8];
        self.read(position, &mut buf)?;
        Ok(u64::from_be_bytes(buf))
    }
}

#[derive(Debug)]
pub struct Block {
    buffer: Vec<u8>,
}

impl Block {
    fn iter(&self) -> BlockIterator {
        BlockIterator {
            buffer: self.buffer.clone(),
            item_count: u64::from_be_bytes(self.buffer[0..8].try_into().unwrap()),
            current_item: 0,
        }
    }
}

#[derive(Debug, Clone)]
struct BlockIterator {
    buffer: Vec<u8>,
    item_count: u64,
    current_item: usize,
}

impl<'a> Iterator for BlockIterator {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.item_count <= (self.current_item as u64) {
            return None;
        }

        let pointer_start = 16 + (self.current_item * 8);
        let pointer_end = pointer_start + 8;
        let pointer = u64::from_be_bytes(self.buffer[pointer_start..pointer_end].try_into().unwrap());

        let size = if self.current_item == 0 {
            self.buffer.len() - (pointer as usize)
        } else {
            let prev_pointer_start = pointer_start - 8;
            let prev_pointer_end = pointer_start;
            let prev_pointer = u64::from_be_bytes(self.buffer[prev_pointer_start..prev_pointer_end].try_into().unwrap());
            (prev_pointer - pointer) as usize
        };

        let end = (pointer as usize) + size;

        self.current_item += 1;

        Some(self.buffer[(pointer as usize)..end].to_owned())
    }
}

pub struct Db<I: Io> {
    block_count: u64,
    block_size: u64,
    blocks_cache: BTreeMap<u64, Block>,
    type_cache: BTreeMap<TypeId, Arc<TypeInfo>>,
    type_table: Vec<TypeId>,
    io: I,
    logger: Option<fn(core::fmt::Arguments)>
}

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

const HEADER_SIZE: u64 = 2 + 6 + 8 + 8 + 64;

impl<I: Io> Db<I> {
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

    pub fn all_type_ids(&self) -> Vec<TypeId> {
        let mut types = self.type_table.clone();
        types.sort_by_key(|x| x.0);
        types.dedup();
        types
    }

    fn find_free_block(&self) -> Option<usize> {
        self.type_table.iter()
            .enumerate()
            .find(|(_, x)| x.0 == 0)
            .map(|(i, _)| i)
    }

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

    pub fn write_object(&mut self, obj: DbObject) -> Result<(), Error> {
        self.log(format_args!("Writing a {}", obj.type_info.name));
        let (block_id, block_start) = self.allocate_block(obj.type_info.id)?; // TODO: look for blocks with some space left
        let size = obj.size(&self);
        self.log(format_args!("Size of the object {}", size));
        let start = self.block_size as usize - size;
        self.log(format_args!("Start of buffer {}", start));
        let buff = &mut self.blocks_cache.get_mut(&block_id).unwrap().buffer;
        for (i, byte) in 1u64.to_be_bytes().iter().enumerate() {
            buff[i] = *byte;
        }
        for (i, byte) in size.to_be_bytes().iter().enumerate() {
            buff[8 + i] = *byte;
        }
        for (i, byte) in start.to_be_bytes().iter().enumerate() {
            buff[16 + i] = *byte;
        }
        obj.value.write(self.logger.clone().unwrap_or(|_| {}), &mut buff[start..])?;
        self.io.write(block_start, buff)?;
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

    pub fn set_logger(&mut self, logger: fn(core::fmt::Arguments)) {
        self.logger = Some(logger);
    }

    fn log(&self, args: core::fmt::Arguments) {
        if let Some(log) = self.logger {
            log(args);
        }
    }
}

#[derive(Debug)]
pub struct TypeIterator<'a, I: Io> {
    db: &'a mut Db<I>,
    type_info: Arc<TypeInfo>,
    blocks: Vec<u64>,
    current_block: Option<BlockIterator>,
}

impl<'a, I: Io> TypeIterator<'a, I> {
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

fn read_string(buffer: &[u8]) -> String {
    let len = u64::from_be_bytes(buffer[0..8].try_into().unwrap()) as usize;
    let buf = &buffer[8..(8 + len)];
    let string = core::str::from_utf8(buf).unwrap_or("ERROR").to_owned();
    string
}

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct TypeId(pub u64);

pub mod type_ids {
    use super::TypeId;

    pub const NEVER:       TypeId = TypeId(0x00);
    pub const UNIT:        TypeId = TypeId(0x01);
    pub const U8:          TypeId = TypeId(0x02);
    pub const U16:         TypeId = TypeId(0x03);
    pub const U32:         TypeId = TypeId(0x04);
    pub const U64:         TypeId = TypeId(0x05);
    pub const I8:          TypeId = TypeId(0x06);
    pub const I16:         TypeId = TypeId(0x07);
    pub const I32:         TypeId = TypeId(0x08);
    pub const I64:         TypeId = TypeId(0x09);
    pub const F32:         TypeId = TypeId(0x0a);
    pub const F64:         TypeId = TypeId(0x0b);
    pub const TYPE:        TypeId = TypeId(0x0c);
    pub const FUNCTION:    TypeId = TypeId(0x0d);
    pub const TRAIT:       TypeId = TypeId(0x0e);
    pub const STR:         TypeId = TypeId(0x0f);
    pub const TYPEDEF:     TypeId = TypeId(0x10);
    pub const TYPE_ID:     TypeId = TypeId(0x11);
    pub const FIELD:       TypeId = TypeId(0x12);
    pub const FIELD_ARRAY: TypeId = TypeId(0x13);
}

#[derive(Debug)]
pub enum TypeDef {
    // TODO: maybe Unit and Never could be empty Products/Sums
    Never,
    Unit,
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Array(TypeId),
    Product {
        fields: Vec<(String, TypeId)>,
    },
    Sum {
        variants: Vec<(String, TypeId)>,
    }
}

impl TypeDef {
}

#[derive(Debug)]
pub struct TypeInfo {
    pub name: String,
    pub id: TypeId,
    pub definition: TypeDef,
}

impl TypeInfo {
    fn construct(self: Arc<Self>, val: DbValue) -> DbObject {
        DbObject {
            type_info: self,
            value: Arc::new(val),
        }
    }

    fn type_info() -> Self {
        TypeInfo {
            name: "Core.Type".to_string(),
            id: type_ids::TYPE,
            definition: TypeDef::Product {
                fields: vec![
                    ("name".to_string(), type_ids::STR),
                    ("id".to_string(), type_ids::TYPE_ID),
                    ("definition".to_string(), type_ids::TYPEDEF),
                ]
            }
        }
    }

    fn into_runtime(self: Arc<Self>) -> Arc<DbValue> {
        Arc::new(DbValue::Product {
            fields: vec![
                Arc::new(DbValue::Array(self.name.bytes().map(|b| Arc::new(DbValue::U8(b))).collect())),
                Arc::new(DbValue::U64(self.id.0)),
                Arc::new(DbValue::Sum {
                    variant: match self.definition {
                        TypeDef::Never => 0,
                        TypeDef::Unit => 1,
                        TypeDef::U8 => 2,
                        TypeDef::U16 => 3,
                        TypeDef::U32 => 4,
                        TypeDef::U64 => 5,
                        TypeDef::I8 => 6,
                        TypeDef::I16 => 7,
                        TypeDef::I32 => 8,
                        TypeDef::I64 => 9,
                        TypeDef::F32 => 10,
                        TypeDef::F64 => 11,
                        TypeDef::Array(_) => 12,
                        TypeDef::Product { .. } => 13,
                        TypeDef::Sum { .. } => 14,
                    },
                    data: Arc::new(match self.definition {
                        TypeDef::Array(ref ty) => DbValue::U64(ty.0),
                        TypeDef::Product { fields: ref fields_or_variants } |
                        TypeDef::Sum { variants: ref fields_or_variants } => DbValue::Array(
                            fields_or_variants.iter()
                                .map(|(name, id)| Arc::new(DbValue::Product {
                                    fields: vec![
                                        Arc::new(DbValue::Array(name.as_bytes().iter().map(|b| Arc::new(DbValue::U8(*b))).collect())),
                                        Arc::new(DbValue::U64(id.0)),
                                    ]
                                }))
                                .collect()
                        ),
                        _ => DbValue::Unit,
                    }),
                }),
            ],
        })
    }
}

#[derive(Debug)]
pub enum DbValue {
    Unit,
    U8(u8),
    U64(u64),
    F64(f64),
    Array(Vec<Arc<DbValue>>),
    Product {
        fields: Vec<Arc<DbValue>>,
    },
    Sum {
        variant: u64,
        data: Arc<DbValue>,
    }
}

impl DbValue {
    fn write(&self, log: fn(core::fmt::Arguments), buff: &mut [u8]) -> Result<u64, Error> {
        match self {
            &DbValue::Unit => Ok(0),
            &DbValue::U8(x) => {
                log(format_args!("writing byte {}", x));
                buff[0] = x;
                Ok(1)
            },
            &DbValue::U64(x) => {
                log(format_args!("writing u64 {}", x));
                for (i, byte) in u64::to_be_bytes(x).iter().enumerate() {
                    buff[i] = *byte;
                }
                Ok(8)
            },
            &DbValue::F64(x) => {
                for (i, byte) in f64::to_be_bytes(x).iter().enumerate() {
                    buff[i] = *byte;
                }
                Ok(8)
            },
            &DbValue::Array(ref arr) => {
                for (i, byte) in u64::to_be_bytes(arr.len() as u64).iter().enumerate() {
                    buff[i] = *byte;
                }
                let mut offset = 8;
                for elem in arr {
                    offset += elem.write(log, &mut buff[offset as usize..])?;
                }
                log(format_args!("wrote array of size {}", offset));
                Ok(offset)
            },
            &DbValue::Product { ref fields } => {
                let mut offset = 0;
                for field in fields {
                    offset += field.write(log, &mut buff[offset as usize..])?;
                }
                log(format_args!("wrote product {}", offset));
                Ok(offset)
            }
            &DbValue::Sum { variant, ref data } => {
                for (i, byte) in u64::to_be_bytes(variant).iter().enumerate() {
                    buff[i] = *byte;
                }
                let res = 8 + data.write(log, &mut buff[8..])?;
                log(format_args!("wrote sum {}", res));
                Ok(res)
            }
        }
    }
}

#[derive(Debug)]
pub struct DbObject {
    pub type_info: Arc<TypeInfo>,
    pub value: Arc<DbValue>,
}

impl DbObject {
    fn size<I: Io>(&self, db: &Db<I>) -> usize {
        use TypeDef::*;

        match self.type_info.definition {
            Never | Unit => 0,
            U8 | I8 => 1,
            U16 | I16 => 2,
            U32 | I32 | F32 => 4,
            U64 | I64 | F64 => 8,
            Array(id) => {
                let inner_type = db.get_type_info(id).unwrap();
                if let DbValue::Array(ref arr) = *self.value {
                    8 + (arr.iter()
                        .map(|item| DbObject {
                            type_info: Arc::clone(&inner_type),
                            value: Arc::clone(item),
                        }.size(db))
                        .sum::<usize>() as usize)
                } else {
                    unreachable!()
                }
            },
            Product { ref fields } => {
                if let DbValue::Product { fields: ref vals } = *self.value {
                    let vals = vals.iter();
                    let mut total = 0;
                    for ((field_name, id), val) in fields.iter().zip(vals) {
                        let inner_type = db.get_type_info(*id).unwrap();
                        let field_size = DbObject {
                            type_info: inner_type,
                            value: Arc::clone(val),
                        }.size(db);
                        db.log(format_args!("size of {} = {}", field_name, field_size));
                        total += field_size;
                    }
                    total
                } else {
                    unreachable!()
                }
            },
            Sum { ref variants } => {
                if let DbValue::Sum { variant, ref data } = *self.value {
                    if let Some((_, id)) = variants.get(variant as usize) {
                        let inner_type = db.get_type_info(*id).unwrap();
                        8 + DbObject {
                            type_info: inner_type,
                            value: Arc::clone(data),
                        }.size(db)
                    } else {
                        panic!("Variant {} doesn't exist in {:?}", variant, variants)
                    }
                } else {
                    unreachable!()
                }
            }
        }
    }
}

#[cfg(not(feature = "no_std"))]
impl Io for std::fs::File {
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
