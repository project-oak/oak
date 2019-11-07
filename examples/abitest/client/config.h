//
// Copyright 2019 The Project Oak Authors
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

#ifndef OAK_EXAMPLES_ABITEST_CLIENT_CONFIG_H_
#define OAK_EXAMPLES_ABITEST_CLIENT_CONFIG_H_

// Application config as text proto. Deliberately use non-default names for
// nodes and ports to confirm that nothing has been accidentally hard-coded.
static const char* app_config_textproto = R"raw(
nodes {
  node_name: "frontend"
  web_assembly_node {
    wasm_contents_name: "frontend-code"
    ports {
      name: "gRPC_input"
      type: IN
    }
    ports {
      name: "logging_port"
      type: OUT
    }
    ports {
      name: "to_backend_0"
      type: OUT
    }
    ports {
      name: "from_backend_0"
      type: IN
    }
    ports {
      name: "to_backend_1"
      type: OUT
    }
    ports {
      name: "from_backend_1"
      type: IN
    }
    ports {
      name: "to_backend_2"
      type: OUT
    }
    ports {
      name: "from_backend_2"
      type: IN
    }
  }
}
nodes {
  node_name: "backend_0"
  web_assembly_node {
    wasm_contents_name: "backend-code"
    ports {
      name: "be_logging_port"
      type: OUT
    }
    ports {
      name: "from_frontend"
      type: IN
    }
    ports {
      name: "to_frontend"
      type: OUT
    }
  }
}
nodes {
  node_name: "backend_1"
  web_assembly_node {
    wasm_contents_name: "backend-code"
    ports {
      name: "be_logging_port"
      type: OUT
    }
    ports {
      name: "from_frontend"
      type: IN
    }
    ports {
      name: "to_frontend"
      type: OUT
    }
  }
}
nodes {
  node_name: "backend_2"
  web_assembly_node {
    wasm_contents_name: "backend-code"
    ports {
      name: "be_logging_port"
      type: OUT
    }
    ports {
      name: "from_frontend"
      type: IN
    }
    ports {
      name: "to_frontend"
      type: OUT
    }
  }
}
nodes {
  node_name: "grpc_server"
  grpc_server_node {}
}
nodes {
  node_name: "logging_node"
  log_node {}
}
wasm_contents {
  name: "frontend-code"
  module_bytes: "<filled in later>"
}
wasm_contents {
  name: "backend-code"
  module_bytes: "<filled in later>"
}
channels {
  source_endpoint {
    node_name: "grpc_server"
    port_name: "request"
  }
  destination_endpoint {
    node_name: "frontend"
    port_name: "gRPC_input"
  }
}
channels {
  source_endpoint {
    node_name: "frontend"
    port_name: "logging_port"
  }
  destination_endpoint {
    node_name: "logging_node"
    port_name: "in"
  }
}
channels {
  source_endpoint {
    node_name: "backend_0"
    port_name: "be_logging_port"
  }
  destination_endpoint {
    node_name: "logging_node"
    port_name: "in"
  }
}
channels {
  source_endpoint {
    node_name: "backend_1"
    port_name: "be_logging_port"
  }
  destination_endpoint {
    node_name: "logging_node"
    port_name: "in"
  }
}
channels {
  source_endpoint {
    node_name: "backend_2"
    port_name: "be_logging_port"
  }
  destination_endpoint {
    node_name: "logging_node"
    port_name: "in"
  }
}
channels {
  source_endpoint {
    node_name: "frontend"
    port_name: "to_backend_0"
  }
  destination_endpoint {
    node_name: "backend_0"
    port_name: "from_frontend"
  }
}
channels {
  source_endpoint {
    node_name: "backend_0"
    port_name: "to_frontend"
  }
  destination_endpoint {
    node_name: "frontend"
    port_name: "from_backend_0"
  }
}
channels {
  source_endpoint {
    node_name: "frontend"
    port_name: "to_backend_1"
  }
  destination_endpoint {
    node_name: "backend_1"
    port_name: "from_frontend"
  }
}
channels {
  source_endpoint {
    node_name: "backend_1"
    port_name: "to_frontend"
  }
  destination_endpoint {
    node_name: "frontend"
    port_name: "from_backend_1"
  }
}
channels {
  source_endpoint {
    node_name: "frontend"
    port_name: "to_backend_2"
  }
  destination_endpoint {
    node_name: "backend_2"
    port_name: "from_frontend"
  }
}
channels {
  source_endpoint {
    node_name: "backend_2"
    port_name: "to_frontend"
  }
  destination_endpoint {
    node_name: "frontend"
    port_name: "from_backend_2"
  }
}

)raw";

#endif  // OAK_EXAMPLES_ABITEST_CLIENT_CONFIG_H_
