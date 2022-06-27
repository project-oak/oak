# Per-Commmit Provenances for Oak Trusted Runtime Binaries.

The files and folders in this branch are organized as follows:

```
.
|-- [BINARY_HASH_1]
|   |-- [COMMIT_HASH_A].json
|   |-- [COMMIT_HASH_B].json
|   |-- ...
|-- [BINARY_HASH_2]
|   |-- [COMMIT_HASH_C].json
|   |-- [COMMIT_HASH_D].json
|   |-- ...
|-- [BINARY_HASH_3]
|-- ...
```

The following questions can be answered using this structure:

1. Which commits produced a binary with a given hash?

```
$ git checkout provenance 
$ ls [BINARY_HASH]
```

2. Which binaries were produced from a given Git commit hash?

```
$ git diff provenance-[COMMIT_HASH]
```

3. Which binary hashes changed between commit A and B?

```
$ git diff provenance-[COMMIT_HASH_A] provenance-[COMMIT_HASH_B]
```
