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

//! Helper methods for creating common [`NodeConfiguration`] instances.

use oak_abi::proto::oak::application::{
    node_configuration::ConfigType, GrpcClientConfiguration, GrpcServerConfiguration,
    HttpServerConfiguration, LogConfiguration, NodeConfiguration, WebAssemblyConfiguration,
};

pub fn grpc_client(address: &str) -> NodeConfiguration {
    NodeConfiguration {
        name: "grpc_client".to_string(),
        config_type: Some(ConfigType::GrpcClientConfig(GrpcClientConfiguration {
            uri: address.to_string(),
        })),
    }
}

pub fn grpc_server(address: &str) -> NodeConfiguration {
    NodeConfiguration {
        name: "grpc_server".to_string(),
        config_type: Some(ConfigType::GrpcServerConfig(GrpcServerConfiguration {
            address: address.to_string(),
        })),
    }
}

pub fn http_server(address: &str) -> NodeConfiguration {
    NodeConfiguration {
        name: "http_server".to_string(),
        config_type: Some(ConfigType::HttpServerConfig(HttpServerConfiguration {
            address: address.to_string(),
        })),
    }
}

pub fn wasm(module_name: &str, entrypoint_name: &str) -> NodeConfiguration {
    NodeConfiguration {
        name: format!("wasm.{}.{}", module_name, entrypoint_name),
        config_type: Some(ConfigType::WasmConfig(WebAssemblyConfiguration {
            wasm_module_name: module_name.to_string(),
            wasm_entrypoint_name: entrypoint_name.to_string(),
        })),
    }
}

pub fn log() -> NodeConfiguration {
    NodeConfiguration {
        name: "log".to_string(),
        config_type: Some(ConfigType::LogConfig(LogConfiguration {})),
    }
}
