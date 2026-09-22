//! Frozen serialization surface of the original authored nonterminal enum.
use mettail_grammar_core::AuthoredNonTerminalKind;
use serde::ser::{Impossible, Serialize, Serializer};
use std::fmt;

#[derive(Debug)]
struct UnexpectedSerialization;
impl fmt::Display for UnexpectedSerialization {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("expected unit variant")
    }
}
impl std::error::Error for UnexpectedSerialization {}
impl serde::ser::Error for UnexpectedSerialization {
    fn custom<T: fmt::Display>(_: T) -> Self {
        Self
    }
}

/// Observe Serde's complete unit-variant call, not only postcard's index bytes.
struct VariantMetadata;
macro_rules! reject_other_shapes {
    ($($method:ident($($arg:ident : $ty:ty),*) -> $result:ty;)+) => {$(
        fn $method(self, $($arg: $ty),*) -> Result<$result, Self::Error> {
            Err(UnexpectedSerialization)
        }
    )+};
}
impl Serializer for VariantMetadata {
    type Ok = (&'static str, u32, &'static str);
    type Error = UnexpectedSerialization;
    type SerializeSeq = Impossible<Self::Ok, Self::Error>;
    type SerializeTuple = Impossible<Self::Ok, Self::Error>;
    type SerializeTupleStruct = Impossible<Self::Ok, Self::Error>;
    type SerializeTupleVariant = Impossible<Self::Ok, Self::Error>;
    type SerializeMap = Impossible<Self::Ok, Self::Error>;
    type SerializeStruct = Impossible<Self::Ok, Self::Error>;
    type SerializeStructVariant = Impossible<Self::Ok, Self::Error>;

    fn serialize_unit_variant(
        self,
        name: &'static str,
        index: u32,
        variant: &'static str,
    ) -> Result<Self::Ok, Self::Error> {
        Ok((name, index, variant))
    }
    reject_other_shapes! {
        serialize_bool(_value: bool) -> Self::Ok;
        serialize_i8(_value: i8) -> Self::Ok;
        serialize_i16(_value: i16) -> Self::Ok;
        serialize_i32(_value: i32) -> Self::Ok;
        serialize_i64(_value: i64) -> Self::Ok;
        serialize_u8(_value: u8) -> Self::Ok;
        serialize_u16(_value: u16) -> Self::Ok;
        serialize_u32(_value: u32) -> Self::Ok;
        serialize_u64(_value: u64) -> Self::Ok;
        serialize_f32(_value: f32) -> Self::Ok;
        serialize_f64(_value: f64) -> Self::Ok;
        serialize_char(_value: char) -> Self::Ok;
        serialize_str(_value: &str) -> Self::Ok;
        serialize_bytes(_value: &[u8]) -> Self::Ok;
        serialize_none() -> Self::Ok;
        serialize_unit() -> Self::Ok;
        serialize_unit_struct(_name: &'static str) -> Self::Ok;
        serialize_seq(_length: Option<usize>) -> Self::SerializeSeq;
        serialize_tuple(_length: usize) -> Self::SerializeTuple;
        serialize_tuple_struct(_name: &'static str, _length: usize) -> Self::SerializeTupleStruct;
        serialize_tuple_variant(_name: &'static str, _index: u32, _variant: &'static str, _length: usize) -> Self::SerializeTupleVariant;
        serialize_map(_length: Option<usize>) -> Self::SerializeMap;
        serialize_struct(_name: &'static str, _length: usize) -> Self::SerializeStruct;
        serialize_struct_variant(_name: &'static str, _index: u32, _variant: &'static str, _length: usize) -> Self::SerializeStructVariant;
    }
    fn serialize_some<T: ?Sized + Serialize>(self, _value: &T) -> Result<Self::Ok, Self::Error> {
        Err(UnexpectedSerialization)
    }
    fn serialize_newtype_struct<T: ?Sized + Serialize>(
        self,
        _name: &'static str,
        _value: &T,
    ) -> Result<Self::Ok, Self::Error> {
        Err(UnexpectedSerialization)
    }
    fn serialize_newtype_variant<T: ?Sized + Serialize>(
        self,
        _name: &'static str,
        _index: u32,
        _variant: &'static str,
        _value: &T,
    ) -> Result<Self::Ok, Self::Error> {
        Err(UnexpectedSerialization)
    }
}

#[test]
fn original_authored_enum_metadata_and_postcard_bytes_are_exact() {
    for (index, (kind, variant)) in [
        (AuthoredNonTerminalKind::Var, "Var"),
        (AuthoredNonTerminalKind::Integer, "Integer"),
        (AuthoredNonTerminalKind::Boolean, "Boolean"),
        (AuthoredNonTerminalKind::StringLiteral, "StringLiteral"),
        (AuthoredNonTerminalKind::FloatLiteral, "FloatLiteral"),
        (AuthoredNonTerminalKind::Ident, "Ident"),
        (AuthoredNonTerminalKind::Category, "Category"),
    ]
    .into_iter()
    .enumerate()
    {
        assert_eq!(
            kind.serialize(VariantMetadata)
                .expect("unit variant metadata"),
            ("AuthoredNonTerminalKind", index as u32, variant)
        );
        let bytes = postcard::to_allocvec(&kind).expect("original enum wire");
        assert_eq!(bytes, vec![index as u8]);
        assert_eq!(
            postcard::from_bytes::<AuthoredNonTerminalKind>(&bytes).expect("roundtrip"),
            kind
        );
    }
    assert!(postcard::from_bytes::<AuthoredNonTerminalKind>(&[7]).is_err());
}
