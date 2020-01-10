#include <fstream>

#include "asylo/util/logging.h"

namespace oak {
namespace utils {

// Reads a binary file and returns its contents as a std::string.
std::string read_file(const std::string& module_path) {
  std::ifstream t(module_path, std::ifstream::in);
  if (!t.is_open()) {
    LOG(QFATAL) << "Could not open module " << module_path;
  }
  std::stringstream buffer;
  buffer << t.rdbuf();
  return buffer.str();
}

// Writes `data` string into a binary `file`.
void write_file(const std::string& data, const std::string& file) {
  std::ofstream t(file, std::ofstream::out);
  if (!t.is_open()) {
    LOG(QFATAL) << "Could not open file " << file;
  }
  t.rdbuf() << data;
}

}  // namespace utils
}  // namespace oak
