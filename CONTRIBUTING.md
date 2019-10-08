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
[GitHub Help](https://help.github.com/articles/about-pull-requests/) for more
information on using PRs.

During a review, the author of the change addresses review comments by adding
new commits to the same branch / PR and then pushing again (note: we discourage
force-pushing to any branch, even during review).

Once approved, each PR is merged via the
["Squash and merge"](https://help.github.com/en/articles/about-pull-request-merges#squash-and-merge-your-pull-request-commits)
button in the GitHub UI. The final commit message is taken from the PR
description, and individual commit messages are discarded; for this reason, we
do not expect commits to have meaningful messages during a review; the PR
description should follow
[standard git commit conventions](https://chris.beams.io/posts/git-commit/).

## Style Guide

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
