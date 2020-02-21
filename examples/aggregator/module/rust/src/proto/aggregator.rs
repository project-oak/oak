// This file is generated by rust-protobuf 2.10.1. Do not edit
// @generated

// https://github.com/rust-lang/rust-clippy/issues/702
#![allow(unknown_lints)]
#![allow(clippy::all)]

#![cfg_attr(rustfmt, rustfmt_skip)]

#![allow(box_pointers)]
#![allow(dead_code)]
#![allow(missing_docs)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(trivial_casts)]
#![allow(unsafe_code)]
#![allow(unused_imports)]
#![allow(unused_results)]
//! Generated file from `aggregator.proto`

use protobuf::Message as Message_imported_for_functions;
use protobuf::ProtobufEnum as ProtobufEnum_imported_for_functions;

/// Generated files are compatible only with the same version
/// of protobuf runtime.
// const _PROTOBUF_VERSION_CHECK: () = ::protobuf::VERSION_2_10_1;

#[derive(PartialEq,Clone,Default)]
pub struct SubmitSampleRequest {
    // message fields
    pub values: ::std::vec::Vec<u64>,
    // special fields
    pub unknown_fields: ::protobuf::UnknownFields,
    pub cached_size: ::protobuf::CachedSize,
}

impl<'a> ::std::default::Default for &'a SubmitSampleRequest {
    fn default() -> &'a SubmitSampleRequest {
        <SubmitSampleRequest as ::protobuf::Message>::default_instance()
    }
}

impl SubmitSampleRequest {
    pub fn new() -> SubmitSampleRequest {
        ::std::default::Default::default()
    }

    // repeated uint64 values = 1;


    pub fn get_values(&self) -> &[u64] {
        &self.values
    }
    pub fn clear_values(&mut self) {
        self.values.clear();
    }

    // Param is passed by value, moved
    pub fn set_values(&mut self, v: ::std::vec::Vec<u64>) {
        self.values = v;
    }

    // Mutable pointer to the field.
    pub fn mut_values(&mut self) -> &mut ::std::vec::Vec<u64> {
        &mut self.values
    }

    // Take field
    pub fn take_values(&mut self) -> ::std::vec::Vec<u64> {
        ::std::mem::replace(&mut self.values, ::std::vec::Vec::new())
    }
}

impl ::protobuf::Message for SubmitSampleRequest {
    fn is_initialized(&self) -> bool {
        true
    }

    fn merge_from(&mut self, is: &mut ::protobuf::CodedInputStream<'_>) -> ::protobuf::ProtobufResult<()> {
        while !is.eof()? {
            let (field_number, wire_type) = is.read_tag_unpack()?;
            match field_number {
                1 => {
                    ::protobuf::rt::read_repeated_uint64_into(wire_type, is, &mut self.values)?;
                },
                _ => {
                    ::protobuf::rt::read_unknown_or_skip_group(field_number, wire_type, is, self.mut_unknown_fields())?;
                },
            };
        }
        ::std::result::Result::Ok(())
    }

    // Compute sizes of nested messages
    #[allow(unused_variables)]
    fn compute_size(&self) -> u32 {
        let mut my_size = 0;
        for value in &self.values {
            my_size += ::protobuf::rt::value_size(1, *value, ::protobuf::wire_format::WireTypeVarint);
        };
        my_size += ::protobuf::rt::unknown_fields_size(self.get_unknown_fields());
        self.cached_size.set(my_size);
        my_size
    }

    fn write_to_with_cached_sizes(&self, os: &mut ::protobuf::CodedOutputStream<'_>) -> ::protobuf::ProtobufResult<()> {
        for v in &self.values {
            os.write_uint64(1, *v)?;
        };
        os.write_unknown_fields(self.get_unknown_fields())?;
        ::std::result::Result::Ok(())
    }

    fn get_cached_size(&self) -> u32 {
        self.cached_size.get()
    }

    fn get_unknown_fields(&self) -> &::protobuf::UnknownFields {
        &self.unknown_fields
    }

    fn mut_unknown_fields(&mut self) -> &mut ::protobuf::UnknownFields {
        &mut self.unknown_fields
    }

    fn as_any(&self) -> &dyn (::std::any::Any) {
        self as &dyn (::std::any::Any)
    }
    fn as_any_mut(&mut self) -> &mut dyn (::std::any::Any) {
        self as &mut dyn (::std::any::Any)
    }
    fn into_any(self: Box<Self>) -> ::std::boxed::Box<dyn (::std::any::Any)> {
        self
    }

    fn descriptor(&self) -> &'static ::protobuf::reflect::MessageDescriptor {
        Self::descriptor_static()
    }

    fn new() -> SubmitSampleRequest {
        SubmitSampleRequest::new()
    }

    fn descriptor_static() -> &'static ::protobuf::reflect::MessageDescriptor {
        static mut descriptor: ::protobuf::lazy::Lazy<::protobuf::reflect::MessageDescriptor> = ::protobuf::lazy::Lazy {
            lock: ::protobuf::lazy::ONCE_INIT,
            ptr: 0 as *const ::protobuf::reflect::MessageDescriptor,
        };
        unsafe {
            descriptor.get(|| {
                let mut fields = ::std::vec::Vec::new();
                fields.push(::protobuf::reflect::accessor::make_vec_accessor::<_, ::protobuf::types::ProtobufTypeUint64>(
                    "values",
                    |m: &SubmitSampleRequest| { &m.values },
                    |m: &mut SubmitSampleRequest| { &mut m.values },
                ));
                ::protobuf::reflect::MessageDescriptor::new::<SubmitSampleRequest>(
                    "SubmitSampleRequest",
                    fields,
                    file_descriptor_proto()
                )
            })
        }
    }

    fn default_instance() -> &'static SubmitSampleRequest {
        static mut instance: ::protobuf::lazy::Lazy<SubmitSampleRequest> = ::protobuf::lazy::Lazy {
            lock: ::protobuf::lazy::ONCE_INIT,
            ptr: 0 as *const SubmitSampleRequest,
        };
        unsafe {
            instance.get(SubmitSampleRequest::new)
        }
    }
}

impl ::protobuf::Clear for SubmitSampleRequest {
    fn clear(&mut self) {
        self.values.clear();
        self.unknown_fields.clear();
    }
}

impl ::std::fmt::Debug for SubmitSampleRequest {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        ::protobuf::text_format::fmt(self, f)
    }
}

impl ::protobuf::reflect::ProtobufValue for SubmitSampleRequest {
    fn as_ref(&self) -> ::protobuf::reflect::ProtobufValueRef {
        ::protobuf::reflect::ProtobufValueRef::Message(self)
    }
}

#[derive(PartialEq,Clone,Default)]
pub struct GetAggregationResponse {
    // message fields
    pub success: bool,
    pub values: ::std::vec::Vec<u64>,
    // special fields
    pub unknown_fields: ::protobuf::UnknownFields,
    pub cached_size: ::protobuf::CachedSize,
}

impl<'a> ::std::default::Default for &'a GetAggregationResponse {
    fn default() -> &'a GetAggregationResponse {
        <GetAggregationResponse as ::protobuf::Message>::default_instance()
    }
}

impl GetAggregationResponse {
    pub fn new() -> GetAggregationResponse {
        ::std::default::Default::default()
    }

    // bool success = 1;


    pub fn get_success(&self) -> bool {
        self.success
    }
    pub fn clear_success(&mut self) {
        self.success = false;
    }

    // Param is passed by value, moved
    pub fn set_success(&mut self, v: bool) {
        self.success = v;
    }

    // repeated uint64 values = 2;


    pub fn get_values(&self) -> &[u64] {
        &self.values
    }
    pub fn clear_values(&mut self) {
        self.values.clear();
    }

    // Param is passed by value, moved
    pub fn set_values(&mut self, v: ::std::vec::Vec<u64>) {
        self.values = v;
    }

    // Mutable pointer to the field.
    pub fn mut_values(&mut self) -> &mut ::std::vec::Vec<u64> {
        &mut self.values
    }

    // Take field
    pub fn take_values(&mut self) -> ::std::vec::Vec<u64> {
        ::std::mem::replace(&mut self.values, ::std::vec::Vec::new())
    }
}

impl ::protobuf::Message for GetAggregationResponse {
    fn is_initialized(&self) -> bool {
        true
    }

    fn merge_from(&mut self, is: &mut ::protobuf::CodedInputStream<'_>) -> ::protobuf::ProtobufResult<()> {
        while !is.eof()? {
            let (field_number, wire_type) = is.read_tag_unpack()?;
            match field_number {
                1 => {
                    if wire_type != ::protobuf::wire_format::WireTypeVarint {
                        return ::std::result::Result::Err(::protobuf::rt::unexpected_wire_type(wire_type));
                    }
                    let tmp = is.read_bool()?;
                    self.success = tmp;
                },
                2 => {
                    ::protobuf::rt::read_repeated_uint64_into(wire_type, is, &mut self.values)?;
                },
                _ => {
                    ::protobuf::rt::read_unknown_or_skip_group(field_number, wire_type, is, self.mut_unknown_fields())?;
                },
            };
        }
        ::std::result::Result::Ok(())
    }

    // Compute sizes of nested messages
    #[allow(unused_variables)]
    fn compute_size(&self) -> u32 {
        let mut my_size = 0;
        if self.success != false {
            my_size += 2;
        }
        for value in &self.values {
            my_size += ::protobuf::rt::value_size(2, *value, ::protobuf::wire_format::WireTypeVarint);
        };
        my_size += ::protobuf::rt::unknown_fields_size(self.get_unknown_fields());
        self.cached_size.set(my_size);
        my_size
    }

    fn write_to_with_cached_sizes(&self, os: &mut ::protobuf::CodedOutputStream<'_>) -> ::protobuf::ProtobufResult<()> {
        if self.success != false {
            os.write_bool(1, self.success)?;
        }
        for v in &self.values {
            os.write_uint64(2, *v)?;
        };
        os.write_unknown_fields(self.get_unknown_fields())?;
        ::std::result::Result::Ok(())
    }

    fn get_cached_size(&self) -> u32 {
        self.cached_size.get()
    }

    fn get_unknown_fields(&self) -> &::protobuf::UnknownFields {
        &self.unknown_fields
    }

    fn mut_unknown_fields(&mut self) -> &mut ::protobuf::UnknownFields {
        &mut self.unknown_fields
    }

    fn as_any(&self) -> &dyn (::std::any::Any) {
        self as &dyn (::std::any::Any)
    }
    fn as_any_mut(&mut self) -> &mut dyn (::std::any::Any) {
        self as &mut dyn (::std::any::Any)
    }
    fn into_any(self: Box<Self>) -> ::std::boxed::Box<dyn (::std::any::Any)> {
        self
    }

    fn descriptor(&self) -> &'static ::protobuf::reflect::MessageDescriptor {
        Self::descriptor_static()
    }

    fn new() -> GetAggregationResponse {
        GetAggregationResponse::new()
    }

    fn descriptor_static() -> &'static ::protobuf::reflect::MessageDescriptor {
        static mut descriptor: ::protobuf::lazy::Lazy<::protobuf::reflect::MessageDescriptor> = ::protobuf::lazy::Lazy {
            lock: ::protobuf::lazy::ONCE_INIT,
            ptr: 0 as *const ::protobuf::reflect::MessageDescriptor,
        };
        unsafe {
            descriptor.get(|| {
                let mut fields = ::std::vec::Vec::new();
                fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeBool>(
                    "success",
                    |m: &GetAggregationResponse| { &m.success },
                    |m: &mut GetAggregationResponse| { &mut m.success },
                ));
                fields.push(::protobuf::reflect::accessor::make_vec_accessor::<_, ::protobuf::types::ProtobufTypeUint64>(
                    "values",
                    |m: &GetAggregationResponse| { &m.values },
                    |m: &mut GetAggregationResponse| { &mut m.values },
                ));
                ::protobuf::reflect::MessageDescriptor::new::<GetAggregationResponse>(
                    "GetAggregationResponse",
                    fields,
                    file_descriptor_proto()
                )
            })
        }
    }

    fn default_instance() -> &'static GetAggregationResponse {
        static mut instance: ::protobuf::lazy::Lazy<GetAggregationResponse> = ::protobuf::lazy::Lazy {
            lock: ::protobuf::lazy::ONCE_INIT,
            ptr: 0 as *const GetAggregationResponse,
        };
        unsafe {
            instance.get(GetAggregationResponse::new)
        }
    }
}

impl ::protobuf::Clear for GetAggregationResponse {
    fn clear(&mut self) {
        self.success = false;
        self.values.clear();
        self.unknown_fields.clear();
    }
}

impl ::std::fmt::Debug for GetAggregationResponse {
    fn fmt(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        ::protobuf::text_format::fmt(self, f)
    }
}

impl ::protobuf::reflect::ProtobufValue for GetAggregationResponse {
    fn as_ref(&self) -> ::protobuf::reflect::ProtobufValueRef {
        ::protobuf::reflect::ProtobufValueRef::Message(self)
    }
}

static file_descriptor_proto_data: &'static [u8] = b"\
    \n\x10aggregator.proto\x12\x17oak.examples.aggregator\x1a\x1bgoogle/prot\
    obuf/empty.proto\"-\n\x13SubmitSampleRequest\x12\x16\n\x06values\x18\x01\
    \x20\x03(\x04R\x06values\"J\n\x16GetAggregationResponse\x12\x18\n\x07suc\
    cess\x18\x01\x20\x01(\x08R\x07success\x12\x16\n\x06values\x18\x02\x20\
    \x03(\x04R\x06values2\xbd\x01\n\nAggregator\x12T\n\x0cSubmitSample\x12,.\
    oak.examples.aggregator.SubmitSampleRequest\x1a\x16.google.protobuf.Empt\
    y\x12Y\n\x0eGetAggregation\x12\x16.google.protobuf.Empty\x1a/.oak.exampl\
    es.aggregator.GetAggregationResponseb\x06proto3\
";

static mut file_descriptor_proto_lazy: ::protobuf::lazy::Lazy<::protobuf::descriptor::FileDescriptorProto> = ::protobuf::lazy::Lazy {
    lock: ::protobuf::lazy::ONCE_INIT,
    ptr: 0 as *const ::protobuf::descriptor::FileDescriptorProto,
};

fn parse_descriptor_proto() -> ::protobuf::descriptor::FileDescriptorProto {
    ::protobuf::parse_from_bytes(file_descriptor_proto_data).unwrap()
}

pub fn file_descriptor_proto() -> &'static ::protobuf::descriptor::FileDescriptorProto {
    unsafe {
        file_descriptor_proto_lazy.get(|| {
            parse_descriptor_proto()
        })
    }
}
