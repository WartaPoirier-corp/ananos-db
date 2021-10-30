//! A collection of predefined type IDs.

use crate::TypeId;

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
