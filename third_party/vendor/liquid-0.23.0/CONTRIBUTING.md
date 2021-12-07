Thanks for wanting to contribute! :snowman:

Feel free to create issues or make pull requests, we'll try to quickly review them.

If you need assistance, you can join the `#cobalt` channel on `irc.mozilla.org` or the Gitter chat [![Gitter](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/cobalt-org/cobalt.rs)

We want you to feel safe and welcome and will enforce the **[The Rust Code of Conduct](https://www.rust-lang.org/conduct.html)** on all communication platforms of this project.
Please contact [@johannhof](https://github.com/johannhof) for questions or in cases of violation.

# Issues

This project aims to be a Rust implementation of [Liquid](https://shopify.github.io/liquid/).
- Notice that we deviate from shopify/liquid? Please, open an issue if there isn't an [existing one](https://github.com/cobalt-org/liquid-rust/labels/shopify-compatibility)
- Want a new tag or filter? Check for an [existing issue](https://github.com/cobalt-org/liquid-rust/labels/enhancement) and open one if needed.

Some helpful pieces of information when reporting issues
* liquid-rust version
* rust version
* OS and version

# Pull Requests

## Project Ideas

If you're looking for things to do check out the [open issues](https://github.com/cobalt-org/cobalt.rs/issues), especially those with the
[easy](https://github.com/cobalt-org/liquid-rust/issues?q=is%3Aissue+is%3Aopen+label%3Aeasy) and [help wanted](https://github.com/cobalt-org/liquid-rust/issues?q=is%3Aissue+is%3Aopen+label%3A%22help+wanted%22) flags.
Or take a grep through [all TODO comments](https://github.com/cobalt-org/liquid-rust/search?q=TODO) in the code and feel free to help us out there!

## Best Practices

We appreciate your help as-is.  We'd love to help you through the process for contributing.  We have some suggestions to help make things go more smoothly.

🌈 **Here's a checklist for the perfect pull request:**
- [ ] Make sure existing tests still work by running `cargo test` locally.
- [ ] Add new tests for any new feature or regression tests for bugfixes.
- [ ] Install [Clippy](https://github.com/Manishearth/rust-clippy) and run `rustup run nightly cargo clippy` to catch common mistakes (will be checked by Travis)
- [ ] Install [Rustfmt](https://github.com/rust-lang-nursery/rustfmt) and run `cargo fmt` to format your code (will also be checked by Travis)

For commit messages, we use [Conventional](https://www.conventionalcommits.org)
style.  If you already wrote your commits and don't feel comfortable changing
them, don't worry and go ahead and create your PR.  We'll work with you on the
best route forward. You can check your branch locally with
[`committed`](https://github.com/crate-ci/committed).

For new tags or filters, we recommend
- Open an RFC Issue for discussing what the API should be.  We'd like to avoid disrupting people once they start using a feature.
- Consider incubating it in your code first to so it can be iterated on to find what works well.
- Checkout prior art with [Shopify's proprietary extensions](https://help.shopify.com/themes/liquid) or [Jekyll's extensions](https://jekyllrb.com/docs/templates/).
- Putting all non-standard features behind feature flags.

If you're interested in benchmarking your changes
- Be sure to get some before and afters on the same machine
- Rust nightly is required.  You'll need to run `rustup run nightly -- cargo bench`

Hopefully we get this integrated into your CI process.

# Releasing

When we're ready to release, a project owner should do the following
- Determine what the next version is, according to semver
- Bump version in a commit
  - Run `clog --setversion <X>.<Y>.<Z>`, touch up the log
  - Update the version in `Cargo.toml`
- Tag the commit via `git tag -a v<X>.<Y>.<Z>`
- `git push upstream master --tag v<X>.<Y>.<Z>`
- Run `cargo publish` (run `cargo login` first if needed)
- Update README.md to list the new version for Cargo.toml
