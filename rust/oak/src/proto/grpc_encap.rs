// This file is generated by rust-protobuf 2.8.0. Do not edit
// @generated

// https://github.com/Manishearth/rust-clippy/issues/702
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
//! Generated file from `grpc_encap.proto`

use protobuf::Message as Message_imported_for_functions;
use protobuf::ProtobufEnum as ProtobufEnum_imported_for_functions;

/// Generated files are compatible only with the same version
/// of protobuf runtime.
const _PROTOBUF_VERSION_CHECK: () = ::protobuf::VERSION_2_8_0;

#[derive(PartialEq,Clone,Default)]
pub struct GrpcRequest {
    // message fields
    pub stream_id: i32,
    pub method_name: ::std::string::String,
    pub req_msg: ::std::vec::Vec<u8>,
    pub last: bool,
    // special fields
    pub unknown_fields: ::protobuf::UnknownFields,
    pub cached_size: ::protobuf::CachedSize,
}

impl<'a> ::std::default::Default for &'a GrpcRequest {
    fn default() -> &'a GrpcRequest {
        <GrpcRequest as ::protobuf::Message>::default_instance()
    }
}

impl GrpcRequest {
    pub fn new() -> GrpcRequest {
        ::std::default::Default::default()
    }

    // int32 stream_id = 1;


    pub fn get_stream_id(&self) -> i32 {
        self.stream_id
    }
    pub fn clear_stream_id(&mut self) {
        self.stream_id = 0;
    }

    // Param is passed by value, moved
    pub fn set_stream_id(&mut self, v: i32) {
        self.stream_id = v;
    }

    // string method_name = 2;


    pub fn get_method_name(&self) -> &str {
        &self.method_name
    }
    pub fn clear_method_name(&mut self) {
        self.method_name.clear();
    }

    // Param is passed by value, moved
    pub fn set_method_name(&mut self, v: ::std::string::String) {
        self.method_name = v;
    }

    // Mutable pointer to the field.
    // If field is not initialized, it is initialized with default value first.
    pub fn mut_method_name(&mut self) -> &mut ::std::string::String {
        &mut self.method_name
    }

    // Take field
    pub fn take_method_name(&mut self) -> ::std::string::String {
        ::std::mem::replace(&mut self.method_name, ::std::string::String::new())
    }

    // bytes req_msg = 3;


    pub fn get_req_msg(&self) -> &[u8] {
        &self.req_msg
    }
    pub fn clear_req_msg(&mut self) {
        self.req_msg.clear();
    }

    // Param is passed by value, moved
    pub fn set_req_msg(&mut self, v: ::std::vec::Vec<u8>) {
        self.req_msg = v;
    }

    // Mutable pointer to the field.
    // If field is not initialized, it is initialized with default value first.
    pub fn mut_req_msg(&mut self) -> &mut ::std::vec::Vec<u8> {
        &mut self.req_msg
    }

    // Take field
    pub fn take_req_msg(&mut self) -> ::std::vec::Vec<u8> {
        ::std::mem::replace(&mut self.req_msg, ::std::vec::Vec::new())
    }

    // bool last = 4;


    pub fn get_last(&self) -> bool {
        self.last
    }
    pub fn clear_last(&mut self) {
        self.last = false;
    }

    // Param is passed by value, moved
    pub fn set_last(&mut self, v: bool) {
        self.last = v;
    }
}

impl ::protobuf::Message for GrpcRequest {
    fn is_initialized(&self) -> bool {
        true
    }

    fn merge_from(&mut self, is: &mut ::protobuf::CodedInputStream) -> ::protobuf::ProtobufResult<()> {
        while !is.eof()? {
            let (field_number, wire_type) = is.read_tag_unpack()?;
            match field_number {
                1 => {
                    if wire_type != ::protobuf::wire_format::WireTypeVarint {
                        return ::std::result::Result::Err(::protobuf::rt::unexpected_wire_type(wire_type));
                    }
                    let tmp = is.read_int32()?;
                    self.stream_id = tmp;
                },
                2 => {
                    ::protobuf::rt::read_singular_proto3_string_into(wire_type, is, &mut self.method_name)?;
                },
                3 => {
                    ::protobuf::rt::read_singular_proto3_bytes_into(wire_type, is, &mut self.req_msg)?;
                },
                4 => {
                    if wire_type != ::protobuf::wire_format::WireTypeVarint {
                        return ::std::result::Result::Err(::protobuf::rt::unexpected_wire_type(wire_type));
                    }
                    let tmp = is.read_bool()?;
                    self.last = tmp;
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
        if self.stream_id != 0 {
            my_size += ::protobuf::rt::value_size(1, self.stream_id, ::protobuf::wire_format::WireTypeVarint);
        }
        if !self.method_name.is_empty() {
            my_size += ::protobuf::rt::string_size(2, &self.method_name);
        }
        if !self.req_msg.is_empty() {
            my_size += ::protobuf::rt::bytes_size(3, &self.req_msg);
        }
        if self.last != false {
            my_size += 2;
        }
        my_size += ::protobuf::rt::unknown_fields_size(self.get_unknown_fields());
        self.cached_size.set(my_size);
        my_size
    }

    fn write_to_with_cached_sizes(&self, os: &mut ::protobuf::CodedOutputStream) -> ::protobuf::ProtobufResult<()> {
        if self.stream_id != 0 {
            os.write_int32(1, self.stream_id)?;
        }
        if !self.method_name.is_empty() {
            os.write_string(2, &self.method_name)?;
        }
        if !self.req_msg.is_empty() {
            os.write_bytes(3, &self.req_msg)?;
        }
        if self.last != false {
            os.write_bool(4, self.last)?;
        }
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

    fn new() -> GrpcRequest {
        GrpcRequest::new()
    }

    fn descriptor_static() -> &'static ::protobuf::reflect::MessageDescriptor {
        static mut descriptor: ::protobuf::lazy::Lazy<::protobuf::reflect::MessageDescriptor> = ::protobuf::lazy::Lazy {
            lock: ::protobuf::lazy::ONCE_INIT,
            ptr: 0 as *const ::protobuf::reflect::MessageDescriptor,
        };
        unsafe {
            descriptor.get(|| {
                let mut fields = ::std::vec::Vec::new();
                fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeInt32>(
                    "stream_id",
                    |m: &GrpcRequest| { &m.stream_id },
                    |m: &mut GrpcRequest| { &mut m.stream_id },
                ));
                fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeString>(
                    "method_name",
                    |m: &GrpcRequest| { &m.method_name },
                    |m: &mut GrpcRequest| { &mut m.method_name },
                ));
                fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeBytes>(
                    "req_msg",
                    |m: &GrpcRequest| { &m.req_msg },
                    |m: &mut GrpcRequest| { &mut m.req_msg },
                ));
                fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeBool>(
                    "last",
                    |m: &GrpcRequest| { &m.last },
                    |m: &mut GrpcRequest| { &mut m.last },
                ));
                ::protobuf::reflect::MessageDescriptor::new::<GrpcRequest>(
                    "GrpcRequest",
                    fields,
                    file_descriptor_proto()
                )
            })
        }
    }

    fn default_instance() -> &'static GrpcRequest {
        static mut instance: ::protobuf::lazy::Lazy<GrpcRequest> = ::protobuf::lazy::Lazy {
            lock: ::protobuf::lazy::ONCE_INIT,
            ptr: 0 as *const GrpcRequest,
        };
        unsafe {
            instance.get(GrpcRequest::new)
        }
    }
}

impl ::protobuf::Clear for GrpcRequest {
    fn clear(&mut self) {
        self.stream_id = 0;
        self.method_name.clear();
        self.req_msg.clear();
        self.last = false;
        self.unknown_fields.clear();
    }
}

impl ::std::fmt::Debug for GrpcRequest {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        ::protobuf::text_format::fmt(self, f)
    }
}

impl ::protobuf::reflect::ProtobufValue for GrpcRequest {
    fn as_ref(&self) -> ::protobuf::reflect::ProtobufValueRef {
        ::protobuf::reflect::ProtobufValueRef::Message(self)
    }
}

#[derive(PartialEq,Clone,Default)]
pub struct GrpcResponse {
    // message fields
    pub stream_id: i32,
    pub rsp_msg: ::std::vec::Vec<u8>,
    pub status: ::protobuf::SingularPtrField<super::status::Status>,
    pub last: bool,
    // special fields
    pub unknown_fields: ::protobuf::UnknownFields,
    pub cached_size: ::protobuf::CachedSize,
}

impl<'a> ::std::default::Default for &'a GrpcResponse {
    fn default() -> &'a GrpcResponse {
        <GrpcResponse as ::protobuf::Message>::default_instance()
    }
}

impl GrpcResponse {
    pub fn new() -> GrpcResponse {
        ::std::default::Default::default()
    }

    // int32 stream_id = 1;


    pub fn get_stream_id(&self) -> i32 {
        self.stream_id
    }
    pub fn clear_stream_id(&mut self) {
        self.stream_id = 0;
    }

    // Param is passed by value, moved
    pub fn set_stream_id(&mut self, v: i32) {
        self.stream_id = v;
    }

    // bytes rsp_msg = 2;


    pub fn get_rsp_msg(&self) -> &[u8] {
        &self.rsp_msg
    }
    pub fn clear_rsp_msg(&mut self) {
        self.rsp_msg.clear();
    }

    // Param is passed by value, moved
    pub fn set_rsp_msg(&mut self, v: ::std::vec::Vec<u8>) {
        self.rsp_msg = v;
    }

    // Mutable pointer to the field.
    // If field is not initialized, it is initialized with default value first.
    pub fn mut_rsp_msg(&mut self) -> &mut ::std::vec::Vec<u8> {
        &mut self.rsp_msg
    }

    // Take field
    pub fn take_rsp_msg(&mut self) -> ::std::vec::Vec<u8> {
        ::std::mem::replace(&mut self.rsp_msg, ::std::vec::Vec::new())
    }

    // .google.rpc.Status status = 3;


    pub fn get_status(&self) -> &super::status::Status {
        self.status.as_ref().unwrap_or_else(|| super::status::Status::default_instance())
    }
    pub fn clear_status(&mut self) {
        self.status.clear();
    }

    pub fn has_status(&self) -> bool {
        self.status.is_some()
    }

    // Param is passed by value, moved
    pub fn set_status(&mut self, v: super::status::Status) {
        self.status = ::protobuf::SingularPtrField::some(v);
    }

    // Mutable pointer to the field.
    // If field is not initialized, it is initialized with default value first.
    pub fn mut_status(&mut self) -> &mut super::status::Status {
        if self.status.is_none() {
            self.status.set_default();
        }
        self.status.as_mut().unwrap()
    }

    // Take field
    pub fn take_status(&mut self) -> super::status::Status {
        self.status.take().unwrap_or_else(|| super::status::Status::new())
    }

    // bool last = 4;


    pub fn get_last(&self) -> bool {
        self.last
    }
    pub fn clear_last(&mut self) {
        self.last = false;
    }

    // Param is passed by value, moved
    pub fn set_last(&mut self, v: bool) {
        self.last = v;
    }
}

impl ::protobuf::Message for GrpcResponse {
    fn is_initialized(&self) -> bool {
        for v in &self.status {
            if !v.is_initialized() {
                return false;
            }
        };
        true
    }

    fn merge_from(&mut self, is: &mut ::protobuf::CodedInputStream) -> ::protobuf::ProtobufResult<()> {
        while !is.eof()? {
            let (field_number, wire_type) = is.read_tag_unpack()?;
            match field_number {
                1 => {
                    if wire_type != ::protobuf::wire_format::WireTypeVarint {
                        return ::std::result::Result::Err(::protobuf::rt::unexpected_wire_type(wire_type));
                    }
                    let tmp = is.read_int32()?;
                    self.stream_id = tmp;
                },
                2 => {
                    ::protobuf::rt::read_singular_proto3_bytes_into(wire_type, is, &mut self.rsp_msg)?;
                },
                3 => {
                    ::protobuf::rt::read_singular_message_into(wire_type, is, &mut self.status)?;
                },
                4 => {
                    if wire_type != ::protobuf::wire_format::WireTypeVarint {
                        return ::std::result::Result::Err(::protobuf::rt::unexpected_wire_type(wire_type));
                    }
                    let tmp = is.read_bool()?;
                    self.last = tmp;
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
        if self.stream_id != 0 {
            my_size += ::protobuf::rt::value_size(1, self.stream_id, ::protobuf::wire_format::WireTypeVarint);
        }
        if !self.rsp_msg.is_empty() {
            my_size += ::protobuf::rt::bytes_size(2, &self.rsp_msg);
        }
        if let Some(ref v) = self.status.as_ref() {
            let len = v.compute_size();
            my_size += 1 + ::protobuf::rt::compute_raw_varint32_size(len) + len;
        }
        if self.last != false {
            my_size += 2;
        }
        my_size += ::protobuf::rt::unknown_fields_size(self.get_unknown_fields());
        self.cached_size.set(my_size);
        my_size
    }

    fn write_to_with_cached_sizes(&self, os: &mut ::protobuf::CodedOutputStream) -> ::protobuf::ProtobufResult<()> {
        if self.stream_id != 0 {
            os.write_int32(1, self.stream_id)?;
        }
        if !self.rsp_msg.is_empty() {
            os.write_bytes(2, &self.rsp_msg)?;
        }
        if let Some(ref v) = self.status.as_ref() {
            os.write_tag(3, ::protobuf::wire_format::WireTypeLengthDelimited)?;
            os.write_raw_varint32(v.get_cached_size())?;
            v.write_to_with_cached_sizes(os)?;
        }
        if self.last != false {
            os.write_bool(4, self.last)?;
        }
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

    fn new() -> GrpcResponse {
        GrpcResponse::new()
    }

    fn descriptor_static() -> &'static ::protobuf::reflect::MessageDescriptor {
        static mut descriptor: ::protobuf::lazy::Lazy<::protobuf::reflect::MessageDescriptor> = ::protobuf::lazy::Lazy {
            lock: ::protobuf::lazy::ONCE_INIT,
            ptr: 0 as *const ::protobuf::reflect::MessageDescriptor,
        };
        unsafe {
            descriptor.get(|| {
                let mut fields = ::std::vec::Vec::new();
                fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeInt32>(
                    "stream_id",
                    |m: &GrpcResponse| { &m.stream_id },
                    |m: &mut GrpcResponse| { &mut m.stream_id },
                ));
                fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeBytes>(
                    "rsp_msg",
                    |m: &GrpcResponse| { &m.rsp_msg },
                    |m: &mut GrpcResponse| { &mut m.rsp_msg },
                ));
                fields.push(::protobuf::reflect::accessor::make_singular_ptr_field_accessor::<_, ::protobuf::types::ProtobufTypeMessage<super::status::Status>>(
                    "status",
                    |m: &GrpcResponse| { &m.status },
                    |m: &mut GrpcResponse| { &mut m.status },
                ));
                fields.push(::protobuf::reflect::accessor::make_simple_field_accessor::<_, ::protobuf::types::ProtobufTypeBool>(
                    "last",
                    |m: &GrpcResponse| { &m.last },
                    |m: &mut GrpcResponse| { &mut m.last },
                ));
                ::protobuf::reflect::MessageDescriptor::new::<GrpcResponse>(
                    "GrpcResponse",
                    fields,
                    file_descriptor_proto()
                )
            })
        }
    }

    fn default_instance() -> &'static GrpcResponse {
        static mut instance: ::protobuf::lazy::Lazy<GrpcResponse> = ::protobuf::lazy::Lazy {
            lock: ::protobuf::lazy::ONCE_INIT,
            ptr: 0 as *const GrpcResponse,
        };
        unsafe {
            instance.get(GrpcResponse::new)
        }
    }
}

impl ::protobuf::Clear for GrpcResponse {
    fn clear(&mut self) {
        self.stream_id = 0;
        self.rsp_msg.clear();
        self.status.clear();
        self.last = false;
        self.unknown_fields.clear();
    }
}

impl ::std::fmt::Debug for GrpcResponse {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        ::protobuf::text_format::fmt(self, f)
    }
}

impl ::protobuf::reflect::ProtobufValue for GrpcResponse {
    fn as_ref(&self) -> ::protobuf::reflect::ProtobufValueRef {
        ::protobuf::reflect::ProtobufValueRef::Message(self)
    }
}

static file_descriptor_proto_data: &'static [u8] = b"\
    \n\x10grpc_encap.proto\x12\x03oak\x1a\x17google/rpc/status.proto\"x\n\
    \x0bGrpcRequest\x12\x1b\n\tstream_id\x18\x01\x20\x01(\x05R\x08streamId\
    \x12\x1f\n\x0bmethod_name\x18\x02\x20\x01(\tR\nmethodName\x12\x17\n\x07r\
    eq_msg\x18\x03\x20\x01(\x0cR\x06reqMsg\x12\x12\n\x04last\x18\x04\x20\x01\
    (\x08R\x04last\"\x84\x01\n\x0cGrpcResponse\x12\x1b\n\tstream_id\x18\x01\
    \x20\x01(\x05R\x08streamId\x12\x17\n\x07rsp_msg\x18\x02\x20\x01(\x0cR\
    \x06rspMsg\x12*\n\x06status\x18\x03\x20\x01(\x0b2\x12.google.rpc.StatusR\
    \x06status\x12\x12\n\x04last\x18\x04\x20\x01(\x08R\x04lastb\x06proto3\
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
