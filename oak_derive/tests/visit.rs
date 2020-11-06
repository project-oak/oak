//
// Copyright 2020 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use oak_io::{handle::HandleVisit, Handle};

#[derive(Default)]
struct Visited(Handle);

impl HandleVisit for Visited {
    fn fold<B>(&mut self, init: B, f: fn(B, &mut Handle) -> B) -> B {
        f(init, &mut self.0)
    }
}

#[test]
fn named() {
    #[derive(Default, HandleVisit)]
    struct Named {
        a: Visited,
        b: u64,
    }

    assert_visit(Named::default(), 1);
}

#[test]
fn unnamed() {
    #[derive(Default, HandleVisit)]
    struct Unnamed(u64, Visited);

    assert_visit(Unnamed::default(), 1);
}

#[test]
fn unit() {
    #[derive(HandleVisit)]
    struct Unit;

    assert_visit(Unit, 0);
}

#[test]
fn multiple() {
    #[derive(Default, HandleVisit)]
    struct Multiple {
        a: Visited,
        b: Visited,
        c: Visited,
        d: u64,
    }

    assert_visit(Multiple::default(), 3);
}

#[test]
fn nested() {
    #[derive(Default, HandleVisit)]
    struct Inner {
        a: Visited,
        b: u64,
    }

    #[derive(Default, HandleVisit)]
    struct Outer {
        a: Inner,
        b: Visited,
        c: u64,
    }

    assert_visit(Outer::default(), 2);
}

mod enums {
    use super::*;
    #[derive(HandleVisit)]
    enum Enum {
        Named { a: Visited, b: u64 },
        Unnamed(u64, Visited),
        Unit,
    }

    #[derive(HandleVisit)]
    enum Numeric {
        One = 1,
        Two = 2,
    }

    #[test]
    fn named() {
        assert_visit(
            Enum::Named {
                a: Visited::default(),
                b: 0,
            },
            1,
        );
    }

    #[test]
    fn unnamed() {
        assert_visit(Enum::Unnamed(0, Visited::default()), 1);
    }

    #[test]
    fn unit() {
        assert_visit(Enum::Unit, 0);
    }

    #[test]
    fn numeric() {
        assert_visit(Numeric::One, 0);
        assert_visit(Numeric::Two, 0);
    }
}

// Asserts that `t` is visited exactly `expected` times when calling [`HandleVisit::fold`].
fn assert_visit<T: HandleVisit>(mut t: T, expected: usize) {
    let count = t.fold(0, |count, _| count + 1);

    assert_eq!(count, expected);
}
