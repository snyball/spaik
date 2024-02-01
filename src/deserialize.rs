//! Ser(de)serialization for runtime SPAIK values

use std::marker::PhantomData;

use serde::Deserialize;
use serde::de::{
    self, DeserializeSeed, EnumAccess, MapAccess, SeqAccess,
    VariantAccess, Visitor,
};

use crate::builtins::Builtin;
use crate::error::Error;

pub type Result<T> = std::result::Result<T, Error>;
use crate::nkgc::PV;

pub struct Deserializer<'de> {
    // This string starts with the input data and characters are truncated off
    // the beginning as data is parsed.
    input: PV,
    _phantom: PhantomData<&'de str>
}

impl<'de> Deserializer<'de> {
    // By convention, `Deserializer` constructors are named like `from_xyz`.
    // That way basic use cases are satisfied by something like
    // `serde_json::from_str(...)` while advanced use cases that require a
    // deserializer can make one with `serde_json::Deserializer::from_str(...)`.
    pub fn from_pv(input: PV) -> Self {
        Deserializer { input, _phantom: Default::default() }
    }
}

// By convention, the public API of a Serde deserializer is one or more
// `from_xyz` methods such as `from_str`, `from_bytes`, or `from_reader`
// depending on what Rust types the deserializer is able to consume as input.
//
// This basic deserializer supports only `from_str`.
pub fn from_pv<'a, 'de: 'a, T>(s: PV) -> Result<T>
where
    T: Deserialize<'a>,
{
    let mut deserializer = Deserializer::from_pv(s);
    let t = T::deserialize(&mut deserializer)?;
    Ok(t)
}

// SERDE IS NOT A PARSING LIBRARY. This impl block defines a few basic parsing
// functions from scratch. More complicated formats may wish to use a dedicated
// parsing library to help implement their Serde deserializer.
impl<'de> Deserializer<'de> {
}

impl<'de, 'a> de::Deserializer<'de> for &'a mut Deserializer<'de> {
    type Error = Error;

    // Look at the input data to decide what Serde data model type to
    // deserialize as. Not all data formats are able to support this operation.
    // Formats that support `deserialize_any` are known as self-describing.
    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        match self.input {
            PV::Ref(_) => todo!(),
            PV::Sym(_) => self.deserialize_identifier(visitor),
            PV::Int(_) => self.deserialize_i32(visitor),
            PV::UInt(_) => self.deserialize_u64(visitor),
            PV::Real(_) => self.deserialize_f32(visitor),
            PV::Bool(_) => self.deserialize_bool(visitor),
            PV::Char(_) => self.deserialize_char(visitor),
            PV::Id(_) => self.deserialize_u64(visitor),
            #[cfg(feature = "math")]
            PV::Vec2(_) => self.deserialize_tuple(2, visitor),
            #[cfg(feature = "math")]
            PV::Vec3(_) => self.deserialize_tuple(3, visitor),
            PV::Nil => self.deserialize_unit(visitor),
        }
    }

    // Uses the `parse_bool` parsing function defined above to read the JSON
    // identifier `true` or `false` from the input.
    //
    // Parsing refers to looking at the input and deciding that it contains the
    // JSON value `true` or `false`.
    //
    // Deserialization refers to mapping that JSON value into Serde's data
    // model by invoking one of the `Visitor` methods. In the case of JSON and
    // bool that mapping is straightforward so the distinction may seem silly,
    // but in other cases Deserializers sometimes perform non-obvious mappings.
    // For example the TOML format has a Datetime type and Serde's data model
    // does not. In the `toml` crate, a Datetime in the input is deserialized by
    // mapping it to a Serde data model "struct" type with a special name and a
    // single field containing the Datetime represented as a string.
    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_bool(self.input.into())
    }

    // The `parse_signed` function is generic over the integer type `T` so here
    // it is invoked with `T=i8`. The next 8 methods are similar.
    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_i8(self.input.try_into()?)
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_i16(self.input.try_into()?)
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_i32(self.input.try_into()?)
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_i64(self.input.try_into()?)
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_u8(self.input.try_into()?)
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_u16(self.input.try_into()?)
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_u32(self.input.try_into()?)
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_u64(self.input.try_into()?)
    }

    // Float parsing is stupidly hard.
    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_f32(self.input.try_into()?)
    }

    // Float parsing is stupidly hard.
    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_f64(self.input.try_into()?)
    }

    // The `Serializer` implementation on the previous page serialized chars as
    // single-character strings so handle that representation here.
    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        // Parse a string, check that it is one character, call `visit_char`.
        visitor.visit_char(self.input.try_into()?)
    }

    // Refer to the "Understanding deserializer lifetimes" page for information
    // about the three deserialization flavors of strings in Serde.
    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        with_ref!(self.input, String(s) => { visitor.visit_borrowed_str((*s).as_ref()) })
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_str(visitor)
    }

    // The `Serializer` implementation on the previous page serialized byte
    // arrays as JSON arrays of bytes. Handle that representation here.
    fn deserialize_bytes<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!()
    }

    fn deserialize_byte_buf<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        unimplemented!()
    }

    // An absent optional is represented as the JSON `null` and a present
    // optional is represented as just the contained value.
    //
    // As commented in `Serializer` implementation, this is a lossy
    // representation. For example the values `Some(())` and `None` both
    // serialize as just `null`. Unfortunately this is typically what people
    // expect when working with JSON. Other formats are encouraged to behave
    // more intelligently if possible.
    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if self.input == PV::Nil {
            visitor.visit_none()
        } else {
            visitor.visit_some(self)
        }
    }

    // In Serde, unit means an anonymous value containing no data.
    fn deserialize_unit<V>(self, _visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        todo!()
    }

    // Unit struct means a named value containing no data.
    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        _visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        todo!()
    }

    // As is done here, serializers are encouraged to treat newtype structs as
    // insignificant wrappers around the data they contain. That means not
    // parsing anything other than the contained value.
    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        _visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        todo!()
    }

    // Deserialization of compound types like sequences and maps happens by
    // passing the visitor an "Access" object that gives it the ability to
    // iterate through the data contained in the sequence.
    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_seq(CommaSeparated::new(self))
    }

    // Tuples look just like sequences in JSON. Some formats may be able to
    // represent tuples more efficiently.
    //
    // As indicated by the length parameter, the `Deserialize` implementation
    // for a tuple in the Serde data model is required to know the length of the
    // tuple before even looking at the input data.
    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_seq(CommaSeparated::new(self))
    }

    // Tuple structs look just like sequences in JSON.
    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_seq(CommaSeparated::new(self))
    }

    // Much like `deserialize_seq` but calls the visitors `visit_map` method
    // with a `MapAccess` implementation, rather than the visitor's `visit_seq`
    // method with a `SeqAccess` implementation.
    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_map(CommaSeparated::new(self))
    }

    // Structs look just like maps in JSON.
    //
    // Notice the `fields` parameter - a "struct" in the Serde data model means
    // that the `Deserialize` implementation is required to know what the fields
    // are before even looking at the input data. Any key-value pairing in which
    // the fields cannot be known ahead of time is probably a map.
    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_map(CommaSeparated::new(self))
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_enum(Enum::new(self))
    }

    // An identifier in Serde is the type that identifies a field of a struct or
    // the variant of an enum. In JSON, struct fields and enum variants are
    // represented as strings. In other formats they may be represented as
    // numeric indices.
    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        if let Some(sym) = self.input.op() {
            visitor.visit_str(sym.as_ref())
        } else if let PV::Sym(sym) = self.input {
            if let Some(ident) = sym.as_ref().strip_prefix(':') {
                visitor.visit_str(ident)
            } else {
                Err(error!(TypeError,
                     expect: Builtin::Keyword,
                     got: Builtin::Symbol))
            }
        } else {
            Err(error!(TypeError,
                 expect: Builtin::Symbol,
                 got: self.input.bt_type_of()))
        }
    }

    // Like `deserialize_any` but indicates to the `Deserializer` that it makes
    // no difference which `Visitor` method is called because the data is
    // ignored.
    //
    // Some deserializers are able to implement this more efficiently than
    // `deserialize_any`, for example by rapidly skipping over matched
    // delimiters without paying close attention to the data in between.
    //
    // Some formats are not able to implement this at all. Formats that can
    // implement `deserialize_any` and `deserialize_ignored_any` are known as
    // self-describing.
    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }
}

// In order to handle commas correctly when deserializing a JSON array or map,
// we need to track whether we are on the first element or past the first
// element.
struct CommaSeparated<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
}

impl<'a, 'de> CommaSeparated<'a, 'de> {
    fn new(de: &'a mut Deserializer<'de>) -> Self {
        CommaSeparated {
            de,
        }
    }
}

// `SeqAccess` is provided to the `Visitor` to give it the ability to iterate
// through elements of the sequence.
impl<'de, 'a> SeqAccess<'de> for CommaSeparated<'a, 'de> {
    type Error = Error;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>>
    where
        T: DeserializeSeed<'de>,
    {
        // Check if there are no more elements.
        if self.de.input == PV::Nil {
            return Ok(None);
        }
        // Deserialize an array element.
        let mut head = Deserializer::from_pv(self.de.input.car().unwrap());
        let res = seed.deserialize(&mut head).map(Some);
        self.de.input = self.de.input.cdr().unwrap();
        res
    }
}

// `MapAccess` is provided to the `Visitor` to give it the ability to iterate
// through entries of the map.
impl<'de, 'a> MapAccess<'de> for CommaSeparated<'a, 'de> {
    type Error = Error;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: DeserializeSeed<'de>,
    {
        // Check if there are no more elements.
        if self.de.input == PV::Nil {
            return Ok(None);
        }
        // Deserialize an array element.
        let mut head = Deserializer::from_pv(self.de.input.car().unwrap());
        let res = seed.deserialize(&mut head).map(Some);
        self.de.input = self.de.input.cdr().unwrap();
        res
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: DeserializeSeed<'de>,
    {
        let mut head = Deserializer::from_pv(self.de.input.car().unwrap());
        let res = seed.deserialize(&mut head);
        self.de.input = self.de.input.cdr().unwrap();
        res
    }
}

struct Enum<'a, 'de: 'a> {
    de: &'a mut Deserializer<'de>,
}

impl<'a, 'de> Enum<'a, 'de> {
    fn new(de: &'a mut Deserializer<'de>) -> Self {
        Enum { de }
    }
}

// `EnumAccess` is provided to the `Visitor` to give it the ability to determine
// which variant of the enum is supposed to be deserialized.
//
// Note that all enum deserialization methods in Serde refer exclusively to the
// "externally tagged" enum representation.
impl<'de, 'a> EnumAccess<'de> for Enum<'a, 'de> {
    type Error = Error;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant)>
    where
        V: DeserializeSeed<'de>,
    {
        // The `deserialize_enum` method parsed a `{` character so we are
        // currently inside of a map. The seed will be deserializing itself from
        // the key of the map.
        let val = seed.deserialize(&mut *self.de)?;
        Ok((val, self))
    }
}

// `VariantAccess` is provided to the `Visitor` to give it the ability to see
// the content of the single variant that it decided to deserialize.
impl<'de, 'a> VariantAccess<'de> for Enum<'a, 'de> {
    type Error = Error;

    // If the `Visitor` expected this variant to be a unit variant, the input
    // should have been the plain string case handled in `deserialize_enum`.
    fn unit_variant(self) -> Result<()> {
        Ok(())
    }

    // Newtype variants are represented in JSON as `{ NAME: VALUE }` so
    // deserialize the value here.
    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value>
    where
        T: DeserializeSeed<'de>,
    {
        seed.deserialize(self.de)
    }

    // Tuple variants are represented in JSON as `{ NAME: [DATA...] }` so
    // deserialize the sequence of data here.
    fn tuple_variant<V>(self, _len: usize, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let inner = self.de.input;
        let mut nde = Deserializer::from_pv(inner.cdr().unwrap_or(PV::Nil));
        de::Deserializer::deserialize_seq(&mut nde, visitor)
    }

    // Struct variants are represented in JSON as `{ NAME: { K: V, ... } }` so
    // deserialize the inner map here.
    fn struct_variant<V>(
        self,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let inner = self.de.input;
        let mut nde = Deserializer::from_pv(inner.cdr().unwrap_or(PV::Nil));
        de::Deserializer::deserialize_map(&mut nde, visitor)
    }
}

#[cfg(test)]
mod tests {
    use serde::Serialize;

    use crate::{r8vm::R8VM, nkgc::SymID, logging::setup_logging};

    use super::*;

    #[test]
    fn deser_basic_types() {
        let mut vm = R8VM::no_std();

        let s = vm.eval(r#" "test" "#).unwrap();
        let out_s: String = from_pv(s).unwrap();
        assert_eq!(out_s, "test");

        let s = vm.eval(r#" 123 "#).unwrap();
        let out_s: u32 = from_pv(s).unwrap();
        assert_eq!(out_s, 123);

        let s = vm.eval(r#" -123 "#).unwrap();
        let out_s = from_pv::<u32>(s);
        assert!(out_s.is_err());

        let sigma = 0.000001;
        let s = vm.eval(r#" 123.0 "#).unwrap();
        let out_s: f32  = from_pv(s).unwrap();
        assert!(out_s - 123.0 < sigma);

        let sigma = 0.000001;
        let s = vm.eval(r#" 123.0 "#).unwrap();
        let out_s: f64  = from_pv(s).unwrap();
        assert!(out_s - 123.0 < sigma);
    }

    #[test]
    fn test_enum_type() {
        let mut vm = R8VM::no_std();
        #[derive(Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd)]
        #[serde(rename_all = "kebab-case")]
        enum U {
            A(u32, u32),
            B(String, u32),
            #[serde(rename_all = "kebab-case")]
            C { key: String,
                key_2: u32 },
            D { sym: SymID },
        }

        let s = vm.eval(r#" '(a 10 12) "#).unwrap();
        let u = from_pv::<U>(s).unwrap();
        assert_eq!(u, U::A(10, 12));

        let s = vm.eval(r#" '(b "brittany was here" 12) "#).unwrap();
        let u = from_pv::<U>(s).unwrap();
        assert_eq!(u, U::B("brittany was here".to_string(), 12));

        let s = vm.eval(r#" '(c :key "brittany was here" :key-2 12) "#).unwrap();
        let u = from_pv::<U>(s).unwrap();
        assert_eq!(u, U::C { key: "brittany was here".to_string(), key_2: 12 });

        let s = vm.eval(r#" ((lambda (x y) `(c :key ,y :key-2 ,x)) 123 "ayy lmao") "#)
                  .unwrap();
        let u = from_pv::<U>(s).unwrap();
        assert_eq!(u, U::C { key: "ayy lmao".to_string(), key_2: 123 });
    }

    #[test]
    fn unit_variants() {
        #[derive(Debug, Serialize, Deserialize, PartialEq, Eq, PartialOrd)]
        #[serde(rename_all = "kebab-case")]
        enum Abc {
            Qwerty,
            Asdfgh,
        }

        let mut vm = R8VM::no_std();
        let s = vm.eval(r#" '(qwerty) "#).unwrap();
        let u = from_pv::<Abc>(s).unwrap();
        assert_eq!(u, Abc::Qwerty);

        let mut vm = R8VM::no_std();
        let s = vm.eval(r#" '(asdfgh) "#).unwrap();
        let u = from_pv::<Abc>(s).unwrap();
        assert_eq!(u, Abc::Asdfgh);
    }

    #[cfg(feature="math")]
    #[test]
    fn tuples() {
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        #[serde(rename_all = "kebab-case")]
        enum Abc {
            Qwerty { k: glam::Vec2 },
            Asdfgh,
        }

        let mut vm = R8VM::no_std();
        let s = vm.eval(r#" '(qwerty :k (1 0)) "#).unwrap();
        let u = from_pv::<Abc>(s).unwrap();
        assert_eq!(u, Abc::Qwerty { k: glam::vec2(1.0, 0.0) });

        let mut vm = R8VM::no_std();
        let s = vm.eval(r#" '(asdfgh) "#).unwrap();
        let u = from_pv::<Abc>(s).unwrap();
        assert_eq!(u, Abc::Asdfgh);
    }

    #[test]
    fn min_cons_use_after_free() {
        let mut vm = R8VM::no_std();
        vm.eval(r#"'(qwerty :k (1 0))"#).unwrap();
    }
}
