//
// Copyright 2020 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

/// Generic Oak error.
#[derive(Debug)]
pub enum OakError {
    ProtobufDecodeError(Option<prost::DecodeError>),
    ProtobufEncodeError(Option<prost::EncodeError>),
    OakStatus(oak_abi::OakStatus),
    IoError(std::io::Error),
}

impl std::fmt::Display for OakError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OakError::ProtobufDecodeError(e) => write!(f, "protobuf decode error: {:?}", e),
            OakError::ProtobufEncodeError(e) => write!(f, "protobuf encode error: {:?}", e),
            OakError::OakStatus(e) => write!(f, "Oak status value: {:?}", e),
            OakError::IoError(e) => write!(f, "I/O error: {}", e),
        }
    }
}

impl std::error::Error for OakError {}

impl From<prost::DecodeError> for OakError {
    fn from(err: prost::DecodeError) -> Self {
        OakError::ProtobufDecodeError(Some(err))
    }
}

impl From<prost::EncodeError> for OakError {
    fn from(err: prost::EncodeError) -> Self {
        OakError::ProtobufEncodeError(Some(err))
    }
}

impl From<std::io::Error> for OakError {
    fn from(err: std::io::Error) -> Self {
        OakError::IoError(err)
    }
}

impl From<oak_abi::OakStatus> for OakError {
    fn from(status: oak_abi::OakStatus) -> Self {
        OakError::OakStatus(status)
    }
}
