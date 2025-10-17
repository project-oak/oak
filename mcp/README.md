# Private Attested Agent with MCP

This document describes how to set up and run a private, attested AI agent. The
agent uses the [Model Context Protocol (MCP)](https://modelcontextprotocol.io/)
to securely interact with tools and is secured by
[Oak Proxy](../../oak_proxy/README.md) for end-to-end encrypted communication.

The project consists of several key components:

- **Python Agent (`./agent`):** An agent built with the
  [Agent Development Kit (ADK)](https://google.github.io/adk-docs/get-started/quickstart/)
  that can answer questions about weather by using external tools.
- **Oak Proxy (`../../oak_proxy`):** A dual-proxy system that provides a
  transparent, end-to-end encrypted, and attested tunnel for communication.
- **Rust MCP Server (`./server`):** A server that exposes tools to the agent via
  the Model Context Protocol.
- **Oak Functions Tool (`../../oak_functions_standalone`):** A Wasm application
  that serves as a simple weather lookup tool.
- **Terraform Configuration (`./terraform`):** Infrastructure-as-code scripts to
  deploy the entire stack to Google Cloud.
- **Python Client (`./client`):** A command-line application for interacting
  with the agent.

## Running Locally

This setup allows you to run all components on your local machine for
development and testing.

### Prerequisites

- Python 3.12+ and `venv`
- [Nix](https://nixos.org/download.html)
- [Bazel](https://bazel.build/install)

### 1. Install Dependencies

Create and activate a Python virtual environment, then install the required
packages.

```bash
python -m venv .venv
source .venv/bin/activate
pip install -r ./agent/requirements.txt
```

### 2. Start the Oak Functions Weather Tool

This tool acts as a simple database, mapping locations to weather data. The MCP
server will connect to it.

```bash
nix develop
bazel run //oak_functions_standalone:oak_functions_standalone
```

This will start the server, typically on port `8080`.

### 3. Start the Rust MCP Server

In a new terminal, start the MCP server. This server connects to the Oak
Functions tool and exposes it to the agent.

```bash
nix develop
bazel run //mcp/server:mcp_server -- --oak-functions-url http://localhost:8080
```

This will start the MCP server, typically on port `8082`.

### 4. Start the Python Agent

In a new terminal, start the agent. It will connect to the MCP server to use its
tools.

```bash
python mcp/agent/main.py --mcp-server-url http://127.0.0.1:8082/mcp
```

This will start the agent's A2A server on its default port, `8081`.

### 5. Run the Client

Finally, in another terminal, run the client to interact with the agent.

```bash
python mcp/client/main.py --agent-url http://127.0.0.1:8081
```

You can now chat with the agent. For example:

```bash
User: What's the weather at my current location?
```

## Deploying to Google Cloud with Terraform

The Terraform configuration automates the deployment of the entire agent stack,
including all necessary infrastructure and services, to a Google Cloud project.

### Terraform Configuration Overview

The main configuration is defined in `mcp/terraform/main.tf`. It deploys the
following modules:

- **`google_compute_firewall`**: Creates a firewall rule named
  `allow-private-agent-infra` to allow TCP traffic on the `exposed_port`
  (default `8080`) for all deployed instances.
- **`module "model"`**: Deploys a Confidential VM running the Model, which will
  be used by the agent.
- **`module "oak_functions"`**: Deploys the Oak Functions weather tool.
- **`module "mcp_server"`**: Deploys the Rust MCP server. It is configured with
  the internal IP of the Oak Functions instance.
- **`module "agent"`**: Deploys the main Python agent. It is configured with the
  internal IPs of the Model and MCP server instances, ensuring private and
  secure communication within the GCP network.

All configuration variables are defined in `mcp/terraform/variables.tf` with
sensible defaults. You can override these as needed.

### Deployment Steps

1. **Initialize Terraform:** Navigate to the Terraform directory and initialize
   the backend.

   ```bash
   cd mcp/terraform
   terraform init
   ```

2. **Apply the Configuration:** Deploy the resources to your GCP project. You
   may need to provide your GCP Project ID if it differs from the default.

   ```bash
   # Recommended: Specify your project ID
   terraform apply -var="gcp_project_id=your-gcp-project-id"

   # Or, if you have gcloud configured, it will use the default project
   terraform apply
   ```

3. **Get the Public IP:** After the deployment is complete, Terraform will
   output the public IP address of the agent instance. You will need this for
   the next step.

   ```bash
   Outputs:

   agent_public_ip = "136.117.59.5"
   ```

### Running the Client against the Cloud Deployment

To interact with your deployed agent, you must run the `oak_proxy_client`
locally. This client creates a secure, end-to-end encrypted tunnel to the
`oak_proxy_server` running on your GCP instance.

1. **Build the Oak Proxy Client:** If you haven't already, build the client
   binary from the root of the `oak` repository.

   ```bash
   nix develop
   bazel build //oak_proxy/client
   ```

   The binary will be located at `bazel-bin/oak_proxy/client/client`.

2. **Configure the Local Proxy Client:** Create a configuration file named
   `agent_client.toml` with the following content, replacing `<AGENT_PUBLIC_IP>`
   with the IP address from the Terraform output.

   ```toml
   # agent_client.toml
   listen_address = "127.0.0.1:8080"
   server_proxy_url = "ws://<AGENT_PUBLIC_IP>:8080"
   attestation_generators = []
   attestation_verifiers = []
   ```

3. **Run the Local Proxy Client:** Start the local proxy in a terminal.

   ```bash
   RUST_LOG=info ./bazel-bin/oak_proxy/client/client --config agent_client.toml
   ```

   You should see the output: `[Client] Listening on 127.0.0.1:8080`.

4. **Run the Python A2A Client:** In a new terminal, run the Python client,
   ensuring it points to your **local proxy's address**.

   ```bash
   python mcp/client/main.py --agent-url http://127.0.0.1:8080
   ```

You can now interact with your secure, cloud-deployed agent through the
encrypted local proxy.
