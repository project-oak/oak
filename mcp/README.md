# MCP Experiment

## Install Agent Development Kit

Instruction is taken from: https://google.github.io/adk-docs/get-started/quickstart/

Create & Activate Virtual Environment:

```bash
python -m venv .venv
source .venv/bin/activate
```

Install ADK:

```bash
pip install google-adk
```

Get an API key from [Google AI Studio](https://aistudio-preprod.corp.google.com/apikey).

```bash
export GOOGLE_GENAI_USE_VERTEXAI=FALSE
export GOOGLE_API_KEY=YOUR_API_KEY_HERE
```

## Running the Agent

To start an agent in an interactive environment run:

```bash
adk run gemini_mcp
```

Example output:

```bash
Running agent weather_agent, type exit to exit.
[user]: What's the weather at my current location?
[weather_agent]: The weather is sunny with a temperature of 30 degrees Celsius.
```

## Running the Server

MCP Server is implemented using Rust MCP SDK: https://github.com/modelcontextprotocol/rust-sdk

To build the server run:

```bash
cd server
cargo build -p mcp_server
```

You can also inspect the server using the [MCP Inspector tool](https://github.com/modelcontextprotocol/inspector), which requires installing NPX:

```bash
sudo apt install nodejs npm
```

To interact with the server run the MCP Inspector tool from the same directory:

```bash
npx @modelcontextprotocol/inspector cargo run -p mcp_server
```
