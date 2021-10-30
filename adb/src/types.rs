//! Typing system for database objects.

use alloc::sync::Arc;
use crate::{type_ids, DbObject, DbValue};

/// A type ID.
///
/// Each type in a database has a single type ID.
#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct TypeId(pub u64);

/// Represents how a type is defined.
#[derive(Debug)]
pub enum TypeDef {
    // TODO: maybe Unit and Never could be empty Products/Sums
    
    /// This type is `!`.
    Never,
    /// This type is `()`.
    Unit,
    /// This type is `u8`.
    U8,
    /// This type is `u16`.
    U16,
    /// This type is `u32`.
    U32,
    /// This type is `u64`.
    U64,
    /// This type is `i8`.
    I8,
    /// This type is `i16`.
    I16,
    /// This type is `i32`.
    I32,
    /// This type is `i64`.
    I64,
    /// This type is `f32`.
    F32,
    /// This type is `f64`.
    F64,
    /// This type is a array. The `TypeId` is the type ID
    /// of the elements of the array.
    Array(TypeId),
    /// This type is a product type (aka tuple or struct).
    Product {
        /// A list of fields for this type. Each field
        /// is defined by a name and a type (represented as type ID).
        fields: Vec<(String, TypeId)>,
    },
    /// This type is a sum type (aka enum).
    Sum {
        /// A list of variants for this type. Each variant
        /// is defined by a name and a type for associated data (represented as type ID).
        variants: Vec<(String, TypeId)>,
    }
}

/// Information about a type.
#[derive(Debug)]
pub struct TypeInfo {
    /// The name of the type.
    pub name: String,
    /// The ID of the type.
    pub id: TypeId,
    /// The definition of the type.
    pub definition: TypeDef,
}

impl TypeInfo {
    /// Creates a [`DbObject`] by associating this type with a value (that should be
    /// of this type).
    pub(crate) fn construct(self: Arc<Self>, val: DbValue) -> DbObject {
        DbObject {
            type_info: self,
            value: Arc::new(val),
        }
    }

    /// Returns `TypeInfo` about `TypeInfo`.
    pub(crate) fn type_info() -> Self {
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

    /// Transforms a `TypeInfo` into a runtime value, that can then be written
    /// to the database (for instance).
    pub(crate) fn into_runtime(self: Arc<Self>) -> Arc<DbValue> {
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

