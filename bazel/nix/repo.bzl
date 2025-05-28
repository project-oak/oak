"""Load nix package repositories"""

load("@io_tweag_rules_nixpkgs//nixpkgs:nixpkgs.bzl", "nixpkgs_local_repository")

def create_nix_flake_repo():
    nixpkgs_local_repository(
        name = "nixpkgs",
        nix_file_deps = ["//:flake.lock"],
        nix_flake_lock_file = "//:flake.lock",
    )
