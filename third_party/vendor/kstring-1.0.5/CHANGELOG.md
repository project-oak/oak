# Change Log
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/)
and this project adheres to [Semantic Versioning](http://semver.org/).

<!-- next-header -->
## [Unreleased] - ReleaseDate

## [1.0.5] - 2021-09-24

#### Features

- Add `max_inline` feature which is slower for smaller strings but faster for intermediate-length strings
- Added `arc` feature which is slower for smaller strings but, presumably, faster for large-enough strings

#### Fixes

- Ensure the size of KString matches String on 32-bit systems

## [1.0.4] - 2021-07-09

#### Features

- Add missing `impl From<&String> for KString`

## [1.0.3] - 2021-07-08

#### Performance

- Sped up `KString::clone()`

## [1.0.2] - 2021-07-06

#### Features

- `serde` support is now optional (still on by default)

#### Performance

- Sped up `KString::from_string` / `KStringCow::from_string`

## [1.0.1] - 2021-01-29


## [1.0.0] - 2020-07-07

<!-- next-url -->
[Unreleased]: https://github.com/cobalt-org/kstring/compare/v1.0.5...HEAD
[1.0.5]: https://github.com/cobalt-org/kstring/compare/v1.0.4...v1.0.5
[1.0.4]: https://github.com/cobalt-org/kstring/compare/v1.0.3...v1.0.4
[1.0.3]: https://github.com/cobalt-org/kstring/compare/v1.0.2...v1.0.3
[1.0.2]: https://github.com/cobalt-org/kstring/compare/v1.0.1...v1.0.2
[1.0.1]: https://github.com/cobalt-org/kstring/compare/v1.0.0...v1.0.1
