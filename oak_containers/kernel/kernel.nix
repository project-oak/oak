{ pkgs ? import <nixpkgs> { } }:
with { common = import ./kernel-common.nix; };
pkgs.linuxManualConfig {
  version = common.version;
  src = common.src;
  configfile = common.configfile;
  extraMakeFlags = common.extraMakeFlags;
  kernelPatches = [{
    name = "virtio-dma";
    patch = ./patches/virtio-dma.patch;
  }
    {
      name = "tdx-skip-probe-roms";
      patch = ./patches/tdx-probe-roms.patch;
    }
    {
      name = "rtmr-enabling";
      patch = ./patches/rtmr-enable.patch;
    }];
}
