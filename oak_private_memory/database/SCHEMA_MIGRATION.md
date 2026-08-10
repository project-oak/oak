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

## Invariant: a query must match its property's tokenizer

Every indexed string property — `name`, `tag`, `memoryId`, `viewId`, `viewType`
— uses the `Verbatim` tokenizer, so every query over one is written the same
way: quoted, as `name:"foo"`, with `VERBATIM_SEARCH` enabled.

`Verbatim` terms are indexed **as-is**, skipping Icing's normalizer. `Plain`
terms are put through it, which lower-cases them, splits them on separators and
truncates them to `max_token_length`. The query side is normalized by the same
normalizer, and quoting a value (with `VERBATIM_SEARCH` enabled) is what
suppresses that.

So the two sides have to agree, and **a mismatch fails silently** — the lookup
returns "not found" rather than an error:

- A `Verbatim` property queried unquoted has its query term normalized while the
  index term was not, so a name longer than `max_token_length`, or one
  containing a space or an upper-case letter, can never match. That is what
  broke `GetMemoryByName` for the 31-byte `auris.explicit_deletion_tracker` in
  <https://b/543257785>.
- A `Plain` property queried quoted has the inverse problem.

Do not hand-roll a property-equality query string. Use
`build_property_equals_clause()` and take `enabled_features` from
`query_features()`.

### Why every indexed string property is `Verbatim`

All of them hold client-supplied values: ids and names are chosen by the caller
(the server only generates an id when the field is left empty), and `viewType`
is documented as client-provided in `LLMView.type`. Normalizing such a value is
not just unnecessary but actively wrong — two values differing only in case, or
only past a separator or `max_token_length`, collapse to the same index term, so
a lookup for one resolves to the **other** record.

`Verbatim` also makes the values safe to query. A quoted term can be escaped, so
a client-supplied value stays inside its string literal; an unquoted one cannot
be escaped at all and is parsed as query syntax.

Adding a `Plain` property would reintroduce both problems, and would need its
own validation, since `build_property_equals_clause()` always quotes.

### `max_token_length`

`MAX_TOKEN_LENGTH` in [`src/icing/lib.rs`](../src/icing/lib.rs) raises the
normalizer's term limit from Icing's 30-byte default. It only affects `Plain`
properties, of which there are now none. It is kept as a safety margin for any
future `Plain` property.

Note that changing this value does not re-index existing data — it is an
`IcingSearchEngineOptions` field, not part of the schema — so terms written
before a change keep their old truncation.

## Cost of a tokenizer change

Changing a property's tokenizer is not an incompatible change — `set_schema`
accepts it — but it does force Icing to re-index that property. `import()` calls
`set_schema` on every session load, so the first session a user opens after such
a change pays a full re-index. It degrades latency, not correctness.
