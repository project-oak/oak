# Steps to reproduce boringssl.patch

## bindgen.rs

Make sure you have the dependencies needed to build
[bssl-sys](https://boringssl.googlesource.com/boringssl/+/refs/heads/master/rust/bssl-sys/README.md)

```shell
sudo apt install bindgen
sudo apt install cmake
sudo apt install ninja-build
cargo install cargo-deny
```

Download boringssl repo and build bssl-sys

```shell
git clone https://boringssl.googlesource.com/boringssl
cd boringssl
cmake -GNinja -B build -DRUST_BINDINGS=x86_64-unknown-linux-gnu
ninja -C build
```

This will generate the bindgen.rs file seen in the boringssl.patch file

## rest of files

The rest of the files (3) can just be manually created(bssl-crypto/BUILD, bssl-sys/BUILD) and edited(bssl-sys/src/lib.rs)

The BUILD files will not change (neither will the lib.rs file). The bindgen.rs file may need to be re-generated if the
boringssl commit in WORKSPACE is updated (ideally we will have upstreamed this patch to boringssl before then
[b/354710816](b/354710816)).
