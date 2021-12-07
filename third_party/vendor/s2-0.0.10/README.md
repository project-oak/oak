# rust-s2

Rust port of Google S2 geometry library.

[![Build Status](https://travis-ci.org/yjh0502/rust-s2.svg?branch=master)](https://travis-ci.org/yjh0502/rust-s2)
[![docs](https://docs.rs/s2/badge.svg)](docs)

# Status of the Go Library

This library is principally a port of [the Golang S2
library](https://github.com/golang/geo), adapting to Rust idioms where it makes sense.
We detail the progress of this port below relative to that Go library.

## [ℝ¹](https://docs.rs/s2/~0/s2/r1/) - One-dimensional Cartesian coordinates

Full parity with Go.

## [ℝ²](https://docs.rs/s2/~0/s2/r2/) - Two-dimensional Cartesian coordinates

Full parity with Go.

## [ℝ³](https://docs.rs/s2/~0/s2/r3/) - Three-dimensional Cartesian coordinates

Full parity with Go.

## [S¹](https://docs.rs/s2/~0/s2/s1/) - Circular Geometry

Full parity with Go.

## [S²](https://docs.rs/s2/~0/s2/s2/) - Spherical Geometry

**complete**

 - Cell, CellID, LatLng, Point, Region, stuv

**in progress**

 - CellUnion, edgeutil, metric, predicates, Rect

**pending**

 - loop, paddedcell, polygon, polyline, shapeindex
