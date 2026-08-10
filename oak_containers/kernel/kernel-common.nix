with { pkgs = import <nixpkgs> { }; };
with { untrimmed_version = (builtins.readFile ./kernel_version.txt); };
with { linux_version = pkgs.lib.removeSuffix "\n" untrimmed_version; };
{
  version = linux_version;
  src = builtins.fetchurl {
    url = "https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-${linux_version}.tar.xz";
    sha256 = "f143aaade8877ba5616e788b4482576db28481bcf557ef537f4fcc3938fc3176";
  };
  # To allow reproducibility, the following options need to be configured:
  # - CONFIG_MODULE_SIG is not set
  # - CONFIG_MODULE_SIG_ALL is not set
  # - CONFIG_DEBUG_INFO_DWARF_TOOLCHAIN_DEFAULT is not set
  configfile = ./configs/${linux_version}/minimal.config;
  # And also the following build variables.
  # See https://docs.kernel.org/kbuild/reproducible-builds.html.
  extraMakeFlags = [
    "KBUILD_BUILD_USER=user"
    "KBUILD_BUILD_HOST=host"
  ];
}
