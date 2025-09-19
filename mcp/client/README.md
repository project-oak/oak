# A2A Client for Cloud Agent

This directory contains an interactive A2A (Agent-to-Agent) client to
communicate with the cloud agent running in Confidential Space.

## Prerequisites

- Python 3.8+
- The cloud agent must be running and accessible from where you run the client.

## Installation

1. Install the required Python packages:

```bash
pip install -r requirements.txt
```

## Usage

Run the client from your terminal:

```bash
python main.py --agent-url <URL_OF_THE_AGENT>
```

- `--agent-url`: The URL where the agent is listening. If the agent is running
  locally inside the container setup, this will likely be
  `http://1227.0.0.1:8080`. If omitted, it defaults to `http://127.0.0.1:8080`.

Once the client is running, you can type messages and press Enter to send them
to the agent. The agent's responses will be printed in the console.

To exit the client, type `exit` or `quit`.
