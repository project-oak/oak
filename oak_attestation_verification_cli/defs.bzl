"""Bazel macro for generating attestation verification reports.

This file provides a macro for use in BUILD files to generate a report from attestation verification.
"""

def attestation_verification_report(name, attestation, reference_values):
    out = name + ".txt"

    native.genrule(
        name = name,
        testonly = True,
        outs = [out],
        srcs = [
            attestation,
            reference_values,
        ],
        cmd = """
        $(location //oak_attestation_verification_cli) \
            --attestation=$(location {}) \
            --reference-values=$(location {}) > $(location :{})
        """.format(attestation, reference_values, out),
        tools = ["//oak_attestation_verification_cli"],
    )
