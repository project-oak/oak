<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-functions-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-functions.svg?sanitize=true"><img alt="Project Oak Functions Logo" src="/docs/oak-logo/svgs/oak-functions.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

`no_std` compatible implementation of the business logic of the Oak Functions
enclave binary.

The interface of the service is defined via microRPC in
[`oak_functions.proto`](/oak_functions_service/proto/oak_functions.proto).
