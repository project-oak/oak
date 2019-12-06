#include <memory>

#include "oak/server/wasm_node.h"

// See https://llvm.org/docs/LibFuzzer.html#fuzz-target.
extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
  std::string module(reinterpret_cast<char const*>(data), size);
  // Build a WasmNode instance treating the fuzzing input as Wasm module code.
  // No need to pass in an owning runtime instance (first argument) since the
  // built Node is never run.
  std::unique_ptr<oak::WasmNode> node = oak::WasmNode::Create(nullptr, "test", module);
  return 0;
}
