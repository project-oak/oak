"""Helpers to download the rust std lib source and build it to make it available to a rust toolchain."""

def _stdlibs_impl(repository_ctx):
    repository_ctx.download_and_extract(
        url = "https://static.rust-lang.org/dist/" + repository_ctx.attr.nightly_date + "/rustc-nightly-src.tar.gz",
        type = "tar.gz",
        sha256 = repository_ctx.attr.sha256,
        stripPrefix = "rustc-nightly-src",
    )

    repository_ctx.file(
        "BUILD",
        content = repository_ctx.read(repository_ctx.attr.build_file),
    )

stdlibs = repository_rule(
    implementation = _stdlibs_impl,
    attrs = {
        "nightly_date": attr.string(mandatory = True, doc = "The date of the nightly rust std libs to download."),
        "sha256": attr.string(mandatory = False, doc = "The expected SHA2-256 digest of the nightly rust std libs archive."),
        "build_file": attr.label(mandatory = True, doc = "The BUILD file to use for building the rust std libs."),
    },
)
