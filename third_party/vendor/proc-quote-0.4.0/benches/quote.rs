#![feature(test)]
#![recursion_limit = "512"]

extern crate quote;
extern crate test;

use quote::quote;
use test::Bencher;

mod bench;
