{ pkgs ? import <nixpkgs> { } }:
with { common = import ./kernel-common.nix; };
pkgs.linuxManualConfig {
  version = common.version;
  src = common.src;
  configfile = common.configfile;
  extraMakeFlags = common.extraMakeFlags;
}
