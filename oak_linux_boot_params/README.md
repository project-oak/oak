# Linux boot data structures

This crate contains (a subset of) the data structures needed to boot the Linux
kernel, which are of interest to someone who wants to implement a bootloader (or
a kernel compatbile with the Linux boot protocol).

The data structures themselves were first generated with `bindgen` as follows:

```shell
bindgen /usr/include/asm/bootparam.h
```

and then hand-modified to make then more Rust-y (fix names, use `bitfield!`
etc).
