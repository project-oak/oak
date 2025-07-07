# MCP Experiment

## Agent Development Kit

### Install Agent Development Kit

Instructions taken from:
https://google.github.io/adk-docs/get-started/quickstart/

Create & Activate Virtual Environment:

```bash
python -m venv .venv
source .venv/bin/activate
```

Install ADK:

```bash
pip install google-adk
```

Get an API key from
[Google AI Studio](https://aistudio-preprod.corp.google.com/apikey).

```bash
export GOOGLE_GENAI_USE_VERTEXAI=FALSE
export GOOGLE_API_KEY=YOUR_API_KEY_HERE
```

### Run the Agent

To start an agent in an interactive environment run:

```bash
adk run mcp/agent
```

Example output:

```txt
Running agent weather_agent, type exit to exit.
[user]: What's the weather at my current location?
[weather_agent]: The weather is sunny with a temperature of 30 degrees Celsius.
```

### Run the Tool

The weather tool is implemented as an
[Oak Functions](../oak_functions_standalone/README.md) Wasm application. The
Rust MCP server uses [Oak Session](../oak_session/README.md) to connect to the
tool with an attested end-to-end encrypted channel. In order to start the tool,
run the following command:

```bash
nix develop
bazel run //oak_functions_standalone:oak_functions_standalone
```

By default, the application provides a lookup from location (lat, long) to
temperature in Celsius. To lookup the temperature in any of those locations, the
location must be specified as `(<lat>,<long>)` where `<lat>` and `<long>` must
have two decimals of precision and (if necessary) include a leading 0.

For example, for London has latitude 51.51 degrees North and longitude .13
degrees West. To lookup the weather there, we pass the key `"(51.51,-0.13)"`.

A full list of the data can be viewed on the
[Oak Functions standalone testdata page](../oak_functions_standalone/testdata/README.md).

+### Run the Server

MCP Server is implemented using Rust MCP SDK:
https://github.com/modelcontextprotocol/rust-sdk

The agent already automatically starts the server, but you can also run it
manually for inspecting. To build the server run:

```bash
nix develop
bazel build //mcp/server:mcp_server
```

You can also inspect the server using the
[MCP Inspector tool](https://github.com/modelcontextprotocol/inspector), which
requires installing NPX:

```bash
sudo apt install nodejs npm
```

To interact with the server run the MCP Inspector tool from the same directory:

```bash
npx @modelcontextprotocol/inspector nix develop --command sh -c 'cd .. && bazel run //mcp/server:mcp_server'
```

## Gemini CLI

- [demo](https://asciinema.googleplex.com/5682939312472064)
- [docs](https://github.com/google-gemini/gemini-cli/blob/main/docs/tools/mcp-server.md)

- Install Gemini CLI.
- Create a `.gemini/settings.json` config pointing to the locally built server.
  - see the [one](./.gemini/settings.json) in this repository
- Build the server

  ```console
  bazel build mcp/server:mcp_server
  ```

- There is no need to manually run the server, it will be run by gemini itself
- Run `gemini` from the command line
  - It should say "Using 1 MCP server" when it starts
  - Press `ctrl+t` to see the current status of the server, it should show a
    green circle next to its name
