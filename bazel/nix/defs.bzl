"""Setup nixpkgs"""

load("@io_tweag_rules_nixpkgs//nixpkgs:repositories.bzl", "rules_nixpkgs_dependencies")

def setup_nixpkgs_dependencies():
    rules_nixpkgs_dependencies()
