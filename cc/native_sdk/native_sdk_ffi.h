#ifndef THIRD_PARTY_OAK_CC_NATIVE_SDK_NATIVE_SDK_FFI_H_
#define THIRD_PARTY_OAK_CC_NATIVE_SDK_NATIVE_SDK_FFI_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// This is for use with bindgen.  Note that only basic types that work in
// both C and Rust.  The char type is complicated and uint8_t is used instead.
void register_callbacks(
    const uint8_t* (*read_request_cb)(size_t* len),
    bool (*write_response_cb)(const uint8_t* data, size_t len),
    bool (*log_cb)(const uint8_t* data, size_t len),
    uint8_t* (*storage_get_item_cb)(const uint8_t* key, size_t key_len,
                                    size_t* item_len),
    const uint8_t* (*read_error_cb)(uint32_t* status_code, size_t* len));

void oak_main();

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // THIRD_PARTY_OAK_CC_NATIVE_SDK_NATIVE_SDK_FFI_H_
