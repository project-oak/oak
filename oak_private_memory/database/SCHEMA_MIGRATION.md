# Icing Database Schema Migration Guide

## How to make a schema change

1. **Modify `create_schema()`** in [`icing.rs`](icing.rs) — add/change
   properties on `schema_type_builder` (Memory) or
   `memory_view_schema_type_builder` (LlmView).

2. **Update document builders** — if the new field needs data, update
   `PendingMetadata::new()` or `PendingLlmViewMetadata::new()`.

3. **Run the golden snapshot test** to verify backward compatibility:

   ```bash
   bazel test //database:database_test \
       --test_filter="import_golden_snapshot_preserves_data"
   ```

   This imports a checked-in snapshot
   ([`testdata/golden_icing_export.pb`](testdata/golden_icing_export.pb))
   exported under a previous schema and verifies lookups, searches, and writes
   still work. If it fails, the change is not backward-compatible.

4. **Update read/query code** if you added new indexed fields.

5. **Add tests** for the new field in `icing.rs`.

6. **Regenerate the golden snapshot** and check it in:

   ```bash
   bazel run //database:update_golden_snapshot
   ```

   This custom target runs the generator and copies the output directly to the
   source tree at `database/testdata/golden_icing_export.pb`. It does not run a
   test in CI, avoiding failures due to binary non-determinism.

   If you added new fields, also update the generator
   ([`tools/generate_golden_export.rs`](tools/generate_golden_export.rs)) to
   populate them before running the generator.

7. **Run the full test suite**: `bazel test //database:database_test`

## Background

The code always defines the latest schema in `create_schema()`. On import,
`set_schema` is called after restoring the ground truth files — Icing
automatically migrates the old data (adding new fields, re-indexing, etc.).
Incompatible changes (renaming/removing fields, changing data types) cause
`set_schema` to fail, which the `ensure!()` in `import()` catches.
