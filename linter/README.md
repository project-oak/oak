# Oak Project Linter Tool Runner

This is a small tool designed to quickly and easily run a variety of lint tools
on the repository.

Key Features:

- Ignore file handling: .gitignore file is respected by default, along with an
  additional .lintignore file.

- Fast! It runs the entire suite of linters in under 5 seconds. Lint early, lint
  often.

- Concise output: By default, the output focuses only on issues, and doesn't
  fill the screen with unnecessary information.

- Easily extensible: To add new linters, you can just define a new struct.
