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
//! Generated file from `oak_api.proto`

use protobuf::Message as Message_imported_for_functions;
use protobuf::ProtobufEnum as ProtobufEnum_imported_for_functions;

/// Generated files are compatible only with the same version
/// of protobuf runtime.
// const _PROTOBUF_VERSION_CHECK: () = ::protobuf::VERSION_2_10_1;

#[derive(Clone,PartialEq,Eq,Debug,Hash)]
pub enum OakStatus {
    OAK_STATUS_UNSPECIFIED = 0,
    OK = 1,
    ERR_BAD_HANDLE = 2,
    ERR_INVALID_ARGS = 3,
    ERR_CHANNEL_CLOSED = 4,
    ERR_BUFFER_TOO_SMALL = 5,
    ERR_HANDLE_SPACE_TOO_SMALL = 6,
    ERR_OUT_OF_RANGE = 7,
    ERR_INTERNAL = 8,
    ERR_TERMINATED = 9,
    ERR_CHANNEL_EMPTY = 10,
}

impl ::protobuf::ProtobufEnum for OakStatus {
    fn value(&self) -> i32 {
        *self as i32
    }

    fn from_i32(value: i32) -> ::std::option::Option<OakStatus> {
        match value {
            0 => ::std::option::Option::Some(OakStatus::OAK_STATUS_UNSPECIFIED),
            1 => ::std::option::Option::Some(OakStatus::OK),
            2 => ::std::option::Option::Some(OakStatus::ERR_BAD_HANDLE),
            3 => ::std::option::Option::Some(OakStatus::ERR_INVALID_ARGS),
            4 => ::std::option::Option::Some(OakStatus::ERR_CHANNEL_CLOSED),
            5 => ::std::option::Option::Some(OakStatus::ERR_BUFFER_TOO_SMALL),
            6 => ::std::option::Option::Some(OakStatus::ERR_HANDLE_SPACE_TOO_SMALL),
            7 => ::std::option::Option::Some(OakStatus::ERR_OUT_OF_RANGE),
            8 => ::std::option::Option::Some(OakStatus::ERR_INTERNAL),
            9 => ::std::option::Option::Some(OakStatus::ERR_TERMINATED),
            10 => ::std::option::Option::Some(OakStatus::ERR_CHANNEL_EMPTY),
            _ => ::std::option::Option::None
        }
    }

    fn values() -> &'static [Self] {
        static values: &'static [OakStatus] = &[
            OakStatus::OAK_STATUS_UNSPECIFIED,
            OakStatus::OK,
            OakStatus::ERR_BAD_HANDLE,
            OakStatus::ERR_INVALID_ARGS,
            OakStatus::ERR_CHANNEL_CLOSED,
            OakStatus::ERR_BUFFER_TOO_SMALL,
            OakStatus::ERR_HANDLE_SPACE_TOO_SMALL,
            OakStatus::ERR_OUT_OF_RANGE,
            OakStatus::ERR_INTERNAL,
            OakStatus::ERR_TERMINATED,
            OakStatus::ERR_CHANNEL_EMPTY,
        ];
        values
    }

    fn enum_descriptor_static() -> &'static ::protobuf::reflect::EnumDescriptor {
        static mut descriptor: ::protobuf::lazy::Lazy<::protobuf::reflect::EnumDescriptor> = ::protobuf::lazy::Lazy {
            lock: ::protobuf::lazy::ONCE_INIT,
            ptr: 0 as *const ::protobuf::reflect::EnumDescriptor,
        };
        unsafe {
            descriptor.get(|| {
                ::protobuf::reflect::EnumDescriptor::new("OakStatus", file_descriptor_proto())
            })
        }
    }
}

impl ::std::marker::Copy for OakStatus {
}

impl ::std::default::Default for OakStatus {
    fn default() -> Self {
        OakStatus::OAK_STATUS_UNSPECIFIED
    }
}

impl ::protobuf::reflect::ProtobufValue for OakStatus {
    fn as_ref(&self) -> ::protobuf::reflect::ProtobufValueRef {
        ::protobuf::reflect::ProtobufValueRef::Enum(self.descriptor())
    }
}

#[derive(Clone,PartialEq,Eq,Debug,Hash)]
pub enum ChannelReadStatus {
    NOT_READY = 0,
    READ_READY = 1,
    INVALID_CHANNEL = 2,
    ORPHANED = 3,
}

impl ::protobuf::ProtobufEnum for ChannelReadStatus {
    fn value(&self) -> i32 {
        *self as i32
    }

    fn from_i32(value: i32) -> ::std::option::Option<ChannelReadStatus> {
        match value {
            0 => ::std::option::Option::Some(ChannelReadStatus::NOT_READY),
            1 => ::std::option::Option::Some(ChannelReadStatus::READ_READY),
            2 => ::std::option::Option::Some(ChannelReadStatus::INVALID_CHANNEL),
            3 => ::std::option::Option::Some(ChannelReadStatus::ORPHANED),
            _ => ::std::option::Option::None
        }
    }

    fn values() -> &'static [Self] {
        static values: &'static [ChannelReadStatus] = &[
            ChannelReadStatus::NOT_READY,
            ChannelReadStatus::READ_READY,
            ChannelReadStatus::INVALID_CHANNEL,
            ChannelReadStatus::ORPHANED,
        ];
        values
    }

    fn enum_descriptor_static() -> &'static ::protobuf::reflect::EnumDescriptor {
        static mut descriptor: ::protobuf::lazy::Lazy<::protobuf::reflect::EnumDescriptor> = ::protobuf::lazy::Lazy {
            lock: ::protobuf::lazy::ONCE_INIT,
            ptr: 0 as *const ::protobuf::reflect::EnumDescriptor,
        };
        unsafe {
            descriptor.get(|| {
                ::protobuf::reflect::EnumDescriptor::new("ChannelReadStatus", file_descriptor_proto())
            })
        }
    }
}

impl ::std::marker::Copy for ChannelReadStatus {
}

impl ::std::default::Default for ChannelReadStatus {
    fn default() -> Self {
        ChannelReadStatus::NOT_READY
    }
}

impl ::protobuf::reflect::ProtobufValue for ChannelReadStatus {
    fn as_ref(&self) -> ::protobuf::reflect::ProtobufValueRef {
        ::protobuf::reflect::ProtobufValueRef::Enum(self.descriptor())
    }
}

static file_descriptor_proto_data: &'static [u8] = b"\
    \n\roak_api.proto\x12\x03oak*\xfe\x01\n\tOakStatus\x12\x1a\n\x16OAK_STAT\
    US_UNSPECIFIED\x10\0\x12\x06\n\x02OK\x10\x01\x12\x12\n\x0eERR_BAD_HANDLE\
    \x10\x02\x12\x14\n\x10ERR_INVALID_ARGS\x10\x03\x12\x16\n\x12ERR_CHANNEL_\
    CLOSED\x10\x04\x12\x18\n\x14ERR_BUFFER_TOO_SMALL\x10\x05\x12\x1e\n\x1aER\
    R_HANDLE_SPACE_TOO_SMALL\x10\x06\x12\x14\n\x10ERR_OUT_OF_RANGE\x10\x07\
    \x12\x10\n\x0cERR_INTERNAL\x10\x08\x12\x12\n\x0eERR_TERMINATED\x10\t\x12\
    \x15\n\x11ERR_CHANNEL_EMPTY\x10\n*U\n\x11ChannelReadStatus\x12\r\n\tNOT_\
    READY\x10\0\x12\x0e\n\nREAD_READY\x10\x01\x12\x13\n\x0fINVALID_CHANNEL\
    \x10\x02\x12\x0c\n\x08ORPHANED\x10\x03b\x06proto3\
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
