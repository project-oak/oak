#include "asylo/util/logging.h"

#include <fstream>

namespace oak {
namespace utils {

// Reads a binary file and returns its contents as a std::string.
std::string read_file(const std::string &module_path) {
  std::ifstream t(module_path, std::ifstream::in);
  if (!t.is_open()) {
    LOG(QFATAL) << "Could not open module " << module_path;
  }
  std::stringstream buffer;
  buffer << t.rdbuf();
  return buffer.str();
}

}  // namespace utils
}  // namespace oak
