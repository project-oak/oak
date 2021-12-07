# v0.11.3

Bugfixes:
- Fix panic while decoding some images, has no precise cause in the file.
- Warn about `set_extensions` being unimplemented...

Features:
- Added `StreamingDecoder::version` to query the precise version of the
  standard used for encoding the file. This is merely a hint.
- Added `DecodeOptions::allow_unknown_blocks` to skip over unknown or
  unspecified block kinds.

Optimization:
- `Frame::from_rgba` now recognizes when less than 256 colors are being used,
  dynamically skipping the quantization phase.
- Encoding image chunks is faster and simpler 


# v0.11.2

- Fix panic when LZW code size is invalid
- Added option to omit check for lzw end code

# v0.11.1

- Frames out-of-bounds of the screen descriptor are again accepted by default.
- Added `DecodeOptions::check_frame_consistency` to turn this validation on.

# v0.11

- Rename `Reader` to `Decoder`.
- Reworked `Decoder` into `DecodeOptions`.
- The decoding error is now opaque and no longer allocates a string. Adding
  more information or more error conditions is forward compatible.
- Replace the lzw decoder with `weezl`, up to +350% throughput.
- The dysfunctional C-API has been (temporarily?) removed
  - It may get reintroduced as a separate crate at some point
- Added a `std` feature. It must be active for now.
