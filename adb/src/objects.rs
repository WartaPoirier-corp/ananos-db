//! Database objects that can be inspected at runtime.

use alloc::sync::Arc;
use crate::{Db, Error, Io, TypeInfo};

/// A value in the database.
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
    /// Writes the value to a buffer.
    pub(crate) fn write(&self, buff: &mut [u8]) -> Result<u64, Error> {
        match self {
            &DbValue::Unit => Ok(0),
            &DbValue::U8(x) => {
                buff[0] = x;
                Ok(1)
            },
            &DbValue::U64(x) => {
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
                    offset += elem.write(&mut buff[offset as usize..])?;
                }
                Ok(offset)
            },
            &DbValue::Product { ref fields } => {
                let mut offset = 0;
                for field in fields {
                    offset += field.write(&mut buff[offset as usize..])?;
                }
                Ok(offset)
            }
            &DbValue::Sum { variant, ref data } => {
                for (i, byte) in u64::to_be_bytes(variant).iter().enumerate() {
                    buff[i] = *byte;
                }
                let res = 8 + data.write(&mut buff[8..])?;
                Ok(res)
            }
        }
    }
}

/// An object of the database.
///
/// An object is composed of [`DbValue`] and of information
/// about the type of this value (in a [`TypeInfo`]).
#[derive(Debug)]
pub struct DbObject {
    /// Type of the object.
    pub type_info: Arc<TypeInfo>,
    /// Value of the object.
    pub value: Arc<DbValue>,
}

impl DbObject {
    /// Computes the size of an object.
    pub fn size<I: Io>(&self, db: &Db<I>) -> usize {
        use crate::TypeDef::*;

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

