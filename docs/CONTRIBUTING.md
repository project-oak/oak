# How to Contribute

We'd love to accept your patches and contributions to this project. There are
just a few small guidelines you need to follow.

## Contributor License Agreement

Contributions to this project must be accompanied by a Contributor License
Agreement. You (or your employer) retain the copyright to your contribution;
this simply gives us permission to use and redistribute your contributions as
part of the project. Head over to <https://cla.developers.google.com/> to see
your current agreements on file or to sign a new one.

You generally only need to submit a CLA once, so if you've already submitted one
(even if it was for a different project), you probably don't need to do it
again.

## Code reviews

All submissions, including submissions by project members, require review. We
use GitHub Pull Requests (PR) for this purpose. Consult
[GitHub Help](https://docs.github.com/en/github/collaborating-with-issues-and-pull-requests/about-pull-requests)
for more information on using PRs.

For a new review, the author works on a new branch on their own fork of the
repository (we don't create additional branches on the main repository).

Once the changes are made locally, the author creates a new commit on their
newly created branch based on the main branch, then pushes to their own fork,
and creates a PR from the GitHub UI. The author then selects one or more
reviewers.

The commit / PR description should follow
[standard Git commit conventions](https://chris.beams.io/posts/git-commit/).

During a review, the author of the change addresses review comments by adding
new commits to the same branch / PR and then pushing again (note: we discourage
force-pushing to any branch, even during review). The message of these
additional commits is unimportant (it can just be "FIXUP" or similar) as these
commits will most likely be squashed just before merging, and only the message
of the original commit will be kept.

It is _not_ recommended to use the
["Applying suggested changes"](https://docs.github.com/en/github/collaborating-with-issues-and-pull-requests/incorporating-feedback-in-your-pull-request#applying-suggested-changes)
functionality in the GitHub UI, as this may result in the changes being
associated with the wrong user email address, and it also creates a separate
commit, which is not necessarily what we want.

In most cases the author expects a single commit out of a PR; once approved, the
PR is merged via the
["Squash and merge"](https://docs.github.com/en/github/collaborating-with-issues-and-pull-requests/about-pull-request-merges#squash-and-merge-your-pull-request-commits)
button in the GitHub UI. The UI will suggest a final commit message composed of
the PR title, and individual commit messages as a bullet point list; the author
should then reword the final commit message in the UI, usually discarding the
message of any additional fixup commit.

In some cases the author intends to keep multiple commits as part of the same
PR, in which case they would use the
["Rebase and merge"](https://docs.github.com/en/github/collaborating-with-issues-and-pull-requests/about-pull-request-merges#rebase-and-merge-your-pull-request-commits)
button. Note in this case it is up to the author to make sure that any fixups
are squashed against the correct commit if necessary.

## Style Guide

### Rust

- Make sure code is [`cargo clippy`](https://crates.io/crates/clippy) clean.
- Use the `./scripts/runner format` command to keep Rust code formatted
  consistently, according to our [`rustfmt` configuration](/.rustfmt.toml).
- Use the [`scripts/check_docs`](/scripts/check_docs) script to check for
  warnings from
  [`cargo doc`](https://doc.rust-lang.org/cargo/commands/cargo-doc.html) and
  [`cargo deadlinks`](https://crates.io/crates/cargo-deadlinks).

### C++

- Follow https://google.github.io/styleguide/cppguide.html
- Follow https://abseil.io/tips/
- Use [`clang-format`](https://clang.llvm.org/docs/ClangFormat.html) to keep C++
  code formatted consistently.
- Use fully qualified names (leading `::`) for `using` declarations and
  namespace aliases, and avoid fully qualified names for everything else, unless
  it is necessary to make the code compile.

  ```C++
  namespace oak {
    ...
    Node n;
    grpc::Status s;
    ...
  }
  ```

  or

  ```C++
  namespace oak {
    using ::grpc::Status;
    ...
    Node n;
    Status s;
    ...
  }
  ```

## Community Guidelines

This project follows
[Google's Open Source Community Guidelines](https://opensource.google.com/conduct/).
