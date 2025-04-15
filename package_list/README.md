# Package Listing Tool

The package listing tool reads a published package list and prints the packages
and related versions.

## Example

Run the following from the workspace root:

```bash
bazel build //package_list
./bazel-bin/package_list/package_list --file-path=package_list/test_data/packages.binarypb
```
