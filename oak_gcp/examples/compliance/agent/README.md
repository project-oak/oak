# Sovereign Compliance ADK Agent

The **Compliance ADK Agent** is an autonomous AI agent powered by **Google ADK
(Agent Development Kit)** and **Gemini 3.6 Flash**. It inspects sensitive
datasets, audits privacy risks, and coordinates transformations across attested
TEE enclaves.

## Architecture

- `agent.py`: Constructs the `root_agent` equipped with enclave tools
  (`evaluate_compliance`, `anonymize_dataset`, `apply_differential_privacy`,
  `generate_synthetic_data`) and local file I/O tools (`read_file`,
  `write_file`).
- `tools.py`: Wraps remote attested Confidential Space enclaves as callable
  Python tools. Supports path-based data references, preventing large Base64
  payload bloat in LLM contexts.
- `main.py`: Interactive command-line runner and Agent-to-Agent (A2A)
  Starlette/Uvicorn server.

## Usage

### 1. Execute via ADK CLI

Ensure your Gemini API key is set in the environment or in `agent/.env`:

```bash
export GEMINI_API_KEY="your-api-key"
# or export GOOGLE_API_KEY="your-api-key"
```

#### One-Off Single Turn Execution

```bash
adk run agent "Audit the dataset at sample_medical_records.csv and remediate any privacy violations."
```

#### Interactive Multi-Turn Chat

```bash
adk run agent
```

### 2. Interactive Web UI

```bash
adk web agent
```

### 3. Serving over Agent-to-Agent (A2A) Protocol

```bash
python agent/main.py --serve --port=8080
```
