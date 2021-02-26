#include <cstdarg>
#include <cstdint>
#include <cstdlib>
#include <new>
#include <ostream>

namespace oak {

extern "C" {

void generate(const uint8_t* private_key_path_ptr, uintptr_t private_key_path_len,
              const uint8_t* public_key_path_ptr, uintptr_t public_key_path_len);

void sign(const uint8_t* private_key_path_ptr, uintptr_t private_key_path_len,
          const uint8_t* input_string_ptr, uintptr_t input_string_len,
          const uint8_t* signature_file_ptr, uintptr_t signature_file_len);

}  // extern "C"

}  // namespace oak
