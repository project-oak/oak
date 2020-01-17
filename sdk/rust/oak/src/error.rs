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
    ProtobufError(protobuf::ProtobufError),
    OakStatus(crate::OakStatus),
    IoError(std::io::Error),
}

impl From<protobuf::ProtobufError> for OakError {
    fn from(err: protobuf::ProtobufError) -> Self {
        OakError::ProtobufError(err)
    }
}

impl From<std::io::Error> for OakError {
    fn from(err: std::io::Error) -> Self {
        OakError::IoError(err)
    }
}

impl From<crate::OakStatus> for OakError {
    fn from(status: crate::OakStatus) -> Self {
        OakError::OakStatus(status)
    }
}
