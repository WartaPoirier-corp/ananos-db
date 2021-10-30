//! Database objects that can be inspected at runtime.

use crate::{Db, Error, Io, TypeInfo};
use alloc::sync::Arc;

/// A value in the database.
#[derive(Debug)]
#[cfg_attr(test, derive(PartialEq))]
pub enum DbValue {
    Unit,
    U8(u8),
    U64(u64),
    F64(f64),
    Array(Vec<Arc<DbValue>>),
    Product { fields: Vec<Arc<DbValue>> },
    Sum { variant: u64, data: Arc<DbValue> },
}

impl DbValue {
    /// Writes the value to a buffer.
    pub(crate) fn write(&self, buff: &mut [u8]) -> Result<u64, Error> {
        match self {
            &DbValue::Unit => Ok(0),
            &DbValue::U8(x) => {
                buff[0] = x;
                Ok(1)
            }
            &DbValue::U64(x) => {
                for (i, byte) in u64::to_be_bytes(x).iter().enumerate() {
                    buff[i] = *byte;
                }
                Ok(8)
            }
            &DbValue::F64(x) => {
                for (i, byte) in f64::to_be_bytes(x).iter().enumerate() {
                    buff[i] = *byte;
                }
                Ok(8)
            }
            &DbValue::Array(ref arr) => {
                for (i, byte) in u64::to_be_bytes(arr.len() as u64).iter().enumerate() {
                    buff[i] = *byte;
                }
                let mut offset = 8;
                for elem in arr {
                    offset += elem.write(&mut buff[offset as usize..])?;
                }
                Ok(offset)
            }
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
                    8 + (arr
                        .iter()
                        .map(|item| {
                            DbObject {
                                type_info: Arc::clone(&inner_type),
                                value: Arc::clone(item),
                            }
                            .size(db)
                        })
                        .sum::<usize>() as usize)
                } else {
                    unreachable!()
                }
            }
            Product { ref fields } => {
                if let DbValue::Product { fields: ref vals } = *self.value {
                    let vals = vals.iter();
                    let mut total = 0;
                    for ((_, id), val) in fields.iter().zip(vals) {
                        let inner_type = db.get_type_info(*id).unwrap();
                        let field_size = DbObject {
                            type_info: inner_type,
                            value: Arc::clone(val),
                        }
                        .size(db);
                        total += field_size;
                    }
                    total
                } else {
                    unreachable!()
                }
            }
            Sum { ref variants } => {
                if let DbValue::Sum { variant, ref data } = *self.value {
                    if let Some((_, id)) = variants.get(variant as usize) {
                        let inner_type = db.get_type_info(*id).unwrap();
                        8 + DbObject {
                            type_info: inner_type,
                            value: Arc::clone(data),
                        }
                        .size(db)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{type_ids, TypeDef, TypeId, TypeInfo};
    use alloc::sync::Arc;

    #[test]
    fn test_object_size() {
        let db = crate::tests::test_db();

        let pci_type = Arc::new(TypeInfo {
            name: "Os.Pci.Device".to_string(),
            id: TypeId(0xC1),
            definition: TypeDef::Product {
                fields: alloc::vec![
                    ("vendor".to_string(), type_ids::TYPE_ID),
                    ("device".to_string(), type_ids::TYPE_ID),
                    ("class".to_string(), type_ids::TYPE_ID),
                    ("subclass".to_string(), type_ids::TYPE_ID),
                ],
            },
        });

        let obj = DbObject {
            type_info: Arc::clone(&pci_type),
            value: Arc::new(DbValue::Product {
                fields: alloc::vec![
                    Arc::new(DbValue::U64(12)),
                    Arc::new(DbValue::U64(19)),
                    Arc::new(DbValue::U64(20)),
                    Arc::new(DbValue::U64(44)),
                ],
            }),
        };
        let size = obj.size(&db);
        let mut buff = vec![0; size];
        let written_size = obj.value.write(&mut buff).unwrap();
        assert_eq!(size as u64, written_size)
    }

    #[test]
    fn test_object_write() {
        let mut db = crate::tests::test_db();

        let pci_type = Arc::new(TypeInfo {
            name: "Os.Pci.Device".to_string(),
            id: TypeId(0xC1),
            definition: TypeDef::Product {
                fields: alloc::vec![
                    ("vendor".to_string(), type_ids::TYPE_ID),
                    ("device".to_string(), type_ids::TYPE_ID),
                    ("class".to_string(), type_ids::TYPE_ID),
                    ("subclass".to_string(), type_ids::TYPE_ID),
                ],
            },
        });

        let obj = DbObject {
            type_info: Arc::clone(&pci_type),
            value: Arc::new(DbValue::Product {
                fields: alloc::vec![
                    Arc::new(DbValue::U64(12)),
                    Arc::new(DbValue::U64(19)),
                    Arc::new(DbValue::U64(20)),
                    Arc::new(DbValue::U64(44)),
                ],
            }),
        };

        db.write_object(obj).unwrap();

        let mut count = 0;
        for obj in db.iter_type(TypeId(0xC1)) {
            match *obj.value {
                DbValue::Product { ref fields } => {
                    assert_eq!(fields.len(), 4);
                    assert_eq!(*fields[0], DbValue::U64(12));
                    assert_eq!(*fields[1], DbValue::U64(19));
                    assert_eq!(*fields[2], DbValue::U64(20));
                    assert_eq!(*fields[3], DbValue::U64(44));
                }
                _ => panic!("0xC1 is a product type"),
            }
            count += 1;
        }
        assert_eq!(count, 1)
    }
}
