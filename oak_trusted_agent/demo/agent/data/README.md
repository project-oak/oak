# Trusted Medical Agent Demo Data

This directory contains the sample lookup data and MCP tool configurations for
the two attested healthcare provider MCP servers used in the Trusted Agent demo:

- **Downtown Walk-In Clinic (`walk_in_clinic`):** Holds urgent / walk-in visit
  records, including `JOHN_SMITH`'s post-training blood panel (`04-10-2026`)
  showing Hemoglobin at `13.2 g/dL` (marked `NORMAL` against the generic
  `13.0 - 17.0 g/dL` adult male reference range).
- **City General Practice (`gp_clinic`):** Holds multi-year primary care
  checkups (`2024–2026`), showing `JOHN_SMITH`'s personal baseline Hemoglobin is
  consistently `~17.0 g/dL` (`16.9 - 17.1 g/dL`).

## Files

- **`walk_in_clinic_data.textproto` / `gp_clinic_data.textproto`**:
  Human-readable `LookupDataChunk` textproto files keyed by
  `"FIRSTNAME_LASTNAME"` (visit index) and `"FIRSTNAME_LASTNAME:DD-MM-YYYY"`
  (detailed lab results and clinician notes).
- **`walk_in_clinic_mcp.json` / `gp_clinic_mcp.json`**: MCP `ToolConfig`
  definitions exposing the `query_walk_in_clinic` and `query_gp_clinic` tools.

## Generating `.binarypb` and Uploading to GCS

1. **Convert `.textproto` to binary `LookupDataChunk` (`.binarypb`):**

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

2. **Upload `.binarypb` and `ToolConfig` JSON files to the GCS bucket:**

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
