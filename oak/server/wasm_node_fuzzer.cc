#include <memory>

#include "oak/server/wasm_node.h"

// See https://llvm.org/docs/LibFuzzer.html#fuzz-target.
extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t size) {
  std::string module(reinterpret_cast<char const*>(data), size);
  std::unique_ptr<oak::WasmNode> node = oak::WasmNode::Create("test", module);
  return 0;
}
