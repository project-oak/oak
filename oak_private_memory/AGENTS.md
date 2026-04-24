# Agent Instructions

See the root [AGENTS.md](../AGENTS.md) for general repo-wide instructions (build
system, style guide, version control, etc.). This file covers
`oak_private_memory`-specific instructions.

## Verification Checklist

After making **any** code change, you **must** run all three of the following
commands (from the `oak_private_memory` directory) and confirm they pass before
claiming the work is done:

```bash
nix develop --command just build-and-test
nix develop --command just format-all
nix develop --command just style
```

- **`just build-and-test`** — Builds all targets and runs all tests
  (`bazel test -c opt //...:all`). All 11+ tests must pass.
- **`just format-all`** — Runs all formatters (rustfmt, buildifier,
  clang-format, prettier, etc.) across the entire repo. All checks must pass.
- **`just style`** — Runs rustfmt diff checks and clippy lints. Must complete
  with zero errors.

If any of these fail, fix the issues and re-run until all three pass. Do not
commit or push until all three are green.

## Commit Management

When updating an existing commit, **always amend** the change into the original
commit instead of creating a new commit. If the commit has child commits on top,
you must rebase them afterward so the entire stack stays clean.

**Workflow for amending a non-HEAD commit:**

1. Stash any uncommitted changes: `git stash`
2. Start an interactive rebase, marking the target commit as `edit`:

   ```bash
   GIT_SEQUENCE_EDITOR="sed -i '1s/^pick/edit/'" git rebase -i <parent_sha>
   ```

3. Apply your changes (e.g. `git stash pop`), stage them, and amend:

   ```bash
   git add <files>
   git commit --amend --no-edit
   ```

4. Continue the rebase to replay child commits:

   ```bash
   git rebase --continue
   ```

5. Force-push the entire stack: `git push origin HEAD:refs/for/main --force`

**For amending the HEAD commit**, simply use `git commit --amend` directly.

Never create a new "fixup" commit for changes that belong to an existing commit.

**Critical: Preserve Gerrit Change-Id.** Every commit pushed to Gerrit contains
a `Change-Id:` trailer in its commit message. Gerrit uses this to match pushes
to existing CLs. When amending a commit:

- **Use `--no-edit`** to keep the existing message (and its Change-Id) intact.
- **Never use `--amend -m "new message"`** — this replaces the entire message
  and drops the Change-Id, causing Gerrit to create a duplicate CL instead of
  updating the original.
- If you must change the commit message, use `git commit --amend` (without `-m`)
  which opens an editor pre-filled with the existing message including the
  Change-Id. Edit the message but leave the `Change-Id:` line untouched.

### jj (Jujutsu) Users

If the repo uses jj (check for `.jj` at the repo root — see the root AGENTS.md
for detection), use jj commands instead of git:

- **Amend the working copy into its parent**: `jj squash`
- **Edit a specific change**: `jj edit <change_id>` to move the working copy to
  that change, make edits, then `jj new` to return to a new working copy.
- **Update a commit message**: `jj describe -m "new message"` (for the current
  change) or `jj describe <change_id> -m "message"` (for any change).
- **Rebase children**: jj handles this automatically — child commits are rebased
  when their parent is modified.

Do not run `jj git push`, `jj git fetch`, or `jj gerrit upload` unless
explicitly asked.

## Project Structure

- `app/` — Application layer (gRPC handlers, service, persistence worker)
- `database/` — Icing database wrapper, in-memory cache, encryption
- `src/` — Core library (encryption, attestation, session binding, metrics)
- `proto/` — Protocol Buffer definitions
- `test/` — Integration and e2e tests
- `analysis/` — Benchmarks and analysis binaries (not run by `build-and-test`)

## Key Architecture Details

### Icing Database

The database layer wraps Google's Icing search engine via FFI. Key things to
know:

- **Two schemas**: `SCHEMA_NAME` (Memory documents) and `LLM_VIEW_SCHEMA_NAME`
  (LLM View documents with embeddings). Embedding search must target the LLM
  View schema (`search_views = true`).
- **`num_to_score`**: Set to `i32::MAX` to remove the default 30k scoring cap.
  Do not revert this — the default causes silent truncation of older documents
  from search results.
- **Database size limit**: `MAX_DATABASE_SIZE` (250 MB) for metadata blobs,
  `MAX_GRPC_DECODE_SIZE` (100 MB) for gRPC messages. Streaming RPCs bypass the
  gRPC limit.

### Persistence (KeySync)

- Export/import uses `IcingGroundTruthFiles` proto serialized as a single blob.
- The blob is streamed via `add_metadata_blob_stream` /
  `get_metadata_blob_stream` to bypass gRPC message size limits.
- After import, call `optimize()` to compact the database.
