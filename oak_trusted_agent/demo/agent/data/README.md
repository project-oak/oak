# Trusted Medical Agent Demo Data

Lookup data and MCP tool configurations for the two clinic MCP servers in the
medical agent demo:

- Downtown Walk-In Clinic (`walk_in_clinic`): holds walk-in visit records,
  including `JOHN_SMITH`'s post-training blood panel (`04-10-2026`) with
  Hemoglobin at `13.2 g/dL` (marked `NORMAL` against the `13.0 - 17.0 g/dL`
  adult male reference range).
- City General Practice (`gp_clinic`): holds primary care checkups (`2024-2026`)
  where `JOHN_SMITH`'s personal baseline Hemoglobin is `16.9 - 17.1 g/dL`.

## Files

- `walk_in_clinic_data.textproto` and `gp_clinic_data.textproto`:
  `LookupDataChunk` textproto files keyed by `"FIRSTNAME_LASTNAME"` (visit
  index) and `"FIRSTNAME_LASTNAME:DD-MM-YYYY"` (lab results and clinician
  notes).
- `walk_in_clinic_mcp.json` and `gp_clinic_mcp.json`: MCP `ToolConfig`
  definitions for the `query_walk_in_clinic` and `query_gp_clinic` tools.

## Generating `.binarypb` and uploading to GCS

Convert `.textproto` to binary `LookupDataChunk` (`.binarypb`):

```bash
protoc --encode=oak.functions.LookupDataChunk \
  proto/oak_functions/service/oak_functions.proto \
  < oak_trusted_agent/demo/agent/data/walk_in_clinic_data.textproto \
  > /tmp/walk_in_clinic_data.binarypb

protoc --encode=oak.functions.LookupDataChunk \
  proto/oak_functions/service/oak_functions.proto \
  < oak_trusted_agent/demo/agent/data/gp_clinic_data.textproto \
  > /tmp/gp_clinic_data.binarypb
```

Upload `.binarypb` and `ToolConfig` JSON files to the GCS bucket:

```bash
gcloud storage cp \
  /tmp/walk_in_clinic_data.binarypb \
  /tmp/gp_clinic_data.binarypb \
  gs://oak-trusted-agent/demo/agent/lookup_data/

gcloud storage cp \
  oak_trusted_agent/demo/agent/data/walk_in_clinic_mcp.json \
  oak_trusted_agent/demo/agent/data/gp_clinic_mcp.json \
  gs://oak-trusted-agent/demo/agent/tool_config/
```
