Educe
====================

[![CI](https://github.com/magiclen/educe/actions/workflows/ci.yml/badge.svg)](https://github.com/magiclen/educe/actions/workflows/ci.yml)

This crate provides procedural macros to help you implement Rust-built-in traits quickly.

## Features

By default, every trait this crate supports will be enabled. You can disable all of them by disabling the default features and enable only the traits that you want to use by adding them to `features` explictly.

For example,

```toml
[dependencies.educe]
version = "*"
features = ["Debug", "Default", "Hash", "Clone", "Copy"]
default-features = false
```

## Debug

Use `#[derive(Educe)]` and `#[educe(Debug)]` to implement the `Debug` trait for a struct, an enum, or a union. It supports to change the name of your types, variants and fields. You can also ignore some fields, or set a trait and/or a method to replace the `Debug` trait used by default. Also, you can even format a struct to a tuple, and vice versa.

#### Basic Usage

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Debug)]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(Debug)]
enum Enum {
    V1,
    V2 {
        f1: u8,
    },
    V3(u8),
}
```

#### Change the Name of a Type, a Variant or a Field

The `name` attribute can help you rename a type, a variant or a field.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Debug(name = "Struct2"))]
struct Struct {
    #[educe(Debug(name = "f"))]
    f1: u8
}

#[derive(Educe)]
#[educe(Debug(name = true))]
enum Enum {
    #[educe(Debug(name = false))]
    V1,
    #[educe(Debug(name = "V"))]
    V2 {
        #[educe(Debug(name = "f"))]
        f1: u8,
    },
    #[educe(Debug(name = false))]
    V3(u8),
}
```

#### Ignore Fields

The `ignore` attribute can ignore specific fields.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Debug)]
struct Struct {
    #[educe(Debug(ignore))]
    f1: u8
}

#[derive(Educe)]
#[educe(Debug)]
enum Enum {
    V1,
    V2 {
        #[educe(Debug(ignore))]
        f1: u8,
    },
    V3(
        #[educe(Debug(ignore))]
        u8
    ),
}
```

#### Fake Structs and Tuples

With the `named_field` attribute, structs can be formatted as tuples and tuples can be formatted as structs.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Debug(named_field = false))]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(Debug)]
enum Enum {
    V1,
    #[educe(Debug(named_field = false))]
    V2 {
        f1: u8,
    },
    #[educe(Debug(named_field = true))]
    V3(
        u8,
        #[educe(Debug(name = "value"))]
        i32
    ),
}
```

#### Use Another Method or Trait to Do the Format Thing

The `trait` and `method` attributes can be used to replace the `Debug` trait for fields. If you only set the `trait` parameter, the `method` will be set to `fmt` automatically by default.

```rust
#[macro_use] extern crate educe;

use std::fmt::{self, Formatter};

fn fmt(_s: &u8, f: &mut Formatter) -> fmt::Result {
    f.write_str("Hi")
}

trait A {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("Hi")
    }
}

impl A for i32 {};
impl A for u64 {};

#[derive(Educe)]
#[educe(Debug)]
enum Enum<T: A> {
    V1,
    V2 {
        #[educe(Debug(method = "fmt"))]
        f1: u8,
    },
    V3(
        #[educe(Debug(trait = "std::fmt::UpperHex"))]
        u8,
        #[educe(Debug(trait = "A"))]
        T
    ),
}
```

#### Generic Parameters Bound to the `Debug` Trait or Others

The `#[educe(Debug(bound))]` attribute can be used to add the `Debug` trait bound to all generic parameters for the `Debug` implementation.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Debug(bound))]
enum Enum<T, K> {
    V1,
    V2 {
        f1: K,
    },
    V3(
        T
    ),
}
```

Or you can set the where predicates by yourself.

```rust
#[macro_use] extern crate educe;

use std::fmt::{self, Formatter};

fn fmt(_s: &u8, f: &mut Formatter) -> fmt::Result {
    f.write_str("Hi")
}

trait A {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str("Hi")
    }
}

impl A for i32 {};
impl A for u64 {};

#[derive(Educe)]
#[educe(Debug(bound = "T: std::fmt::Debug, K: A"))]
enum Enum<T, K> {
    V1,
    V2 {
        #[educe(Debug(trait = "A"))]
        f1: K,
    },
    V3(
        T
    ),
}
```

#### Union

A union will be formatted to a `u8` slice, because we don't know it's field at runtime. The fields of a union cannot be ignored, renamed or formated with other methods or traits.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Debug)]
struct Union {
    f1: u8,
    f2: i32,
}
```

## PartialEq

Use `#[derive(Educe)]` and `#[educe(ParitalEq)]` to implement the `ParitalEq` trait for a struct or an enum. It supports to ignore some fields, or set a trait and/or a method to replace the `ParitalEq` trait used by default.

#### Basic Usage

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq)]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(PartialEq)]
enum Enum {
    V1,
    V2 {
        f1: u8,
    },
    V3(u8),
}
```

#### Ignore Fields

The `ignore` attribute can ignore specific fields.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq)]
struct Struct {
    #[educe(PartialEq(ignore))]
    f1: u8
}

#[derive(Educe)]
#[educe(PartialEq)]
enum Enum {
    V1,
    V2 {
        #[educe(PartialEq(ignore))]
        f1: u8,
    },
    V3(
        #[educe(PartialEq(ignore))]
        u8
    ),
}
```

#### Use Another Method or Trait to Do Comparing

The `trait` and `method` attributes can be used to replace the `PartialEq` trait for fields. If you only set the `trait` parameter, the `method` will be set to `eq` automatically by default.

```rust
#[macro_use] extern crate educe;

fn eq(a: &u8, b: &u8) -> bool {
    a + 1 == *b
}

trait A {
    fn eq(&self, b: &Self) -> bool;
}

impl A for i32 {
    fn eq(&self, b: &i32) -> bool {
        self + 1 == *b
    }
}

impl A for u64 {
    fn eq(&self, b: &u64) -> bool {
        self + 1 == *b
    }
}

#[derive(Educe)]
#[educe(PartialEq)]
enum Enum<T: A> {
    V1,
    V2 {
        #[educe(PartialEq(method = "eq"))]
        f1: u8,
    },
    V3(
        #[educe(PartialEq(trait = "A"))]
        T
    ),
}
```

#### Generic Parameters Bound to the `PartialEq` Trait or Others

The `#[educe(PartialEq(bound))]` attribute can be used to add the `PartialEq` trait bound to all generic parameters for the `PartialEq` implementation.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq(bound))]
enum Enum<T, K> {
    V1,
    V2 {
        f1: K,
    },
    V3(
        T
    ),
}
```

Or you can set the where predicates by yourself.

```rust
#[macro_use] extern crate educe;

trait A {
    fn eq(&self, b: &Self) -> bool;
}

impl A for i32 {
    fn eq(&self, b: &i32) -> bool {
        self + 1 == *b
    }
}

impl A for u64 {
    fn eq(&self, b: &u64) -> bool {
        self + 1 == *b
    }
}

#[derive(Educe)]
#[educe(PartialEq(bound = "T: std::cmp::PartialEq, K: A"))]
enum Enum<T, K> {
    V1,
    V2 {
        #[educe(PartialEq(trait = "A"))]
        f1: K,
    },
    V3(
        T
    ),
}
```

## Eq

Use `#[derive(Educe)]` and `#[educe(Eq)]` to implement the `Eq` trait for a struct, an enum or a union.

#### Basic Usage

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq, Eq)]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(PartialEq, Eq)]
enum Enum {
    V1,
    V2 {
        f1: u8,
    },
    V3(u8),
}
```

#### Generic Parameters Bound to the `Eq` Trait or Others

The `#[educe(Eq(bound))]` attribute can be used to add the `Eq` trait bound to all generic parameters for the `Eq` implementation.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq(bound), Eq(bound))]
enum Enum<T, K> {
    V1,
    V2 {
        f1: K,
    },
    V3(
        T
    ),
}
```

Or you can set the where predicates by yourself. (NOTE: The `Eq` trait depends on the `PartialEq` (`PartialEq<Self>`) trait.)

```rust
#[macro_use] extern crate educe;

trait A {
    fn eq(&self, b: &Self) -> bool;
}

impl A for i32 {
    fn eq(&self, b: &i32) -> bool {
        self + 1 == *b
    }
}

impl A for u64 {
    fn eq(&self, b: &u64) -> bool {
        self + 1 == *b
    }
}

#[derive(Educe)]
#[educe(PartialEq(bound = "T: std::cmp::PartialEq, K: A"), Eq(bound = "T: std::cmp::PartialEq, K: A"))]
enum Enum<T, K> {
    V1,
    V2 {
        #[educe(PartialEq(trait = "A"))]
        f1: K,
    },
    V3(
        T
    ),
}
```

## PartialOrd

Use `#[derive(Educe)]` and `#[educe(PartialOrd)]` to implement the `PartialOrd` trait for a struct or an enum. It supports to ignore some fields, or set a trait and/or a method to replace the `PartialOrd` trait used by default. The rank of variants and fields can also be modified.

#### Basic Usage

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq, PartialOrd)]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(PartialEq, PartialOrd)]
enum Enum {
    V1,
    V2 {
        f1: u8,
    },
    V3(u8),
}
```

#### Ignore Fields

The `ignore` attribute can ignore specific fields.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq, PartialOrd)]
struct Struct {
    #[educe(PartialOrd(ignore))]
    f1: u8
}

#[derive(Educe)]
#[educe(PartialEq, PartialOrd)]
enum Enum {
    V1,
    V2 {
        #[educe(PartialOrd(ignore))]
        f1: u8,
    },
    V3(
        #[educe(PartialOrd(ignore))]
        u8
    ),
}
```

#### Use Another Method or Trait to Do Comparing

The `trait` and `method` attributes can be used to replace the `PartialOrd` trait for fields. If you only set the `trait` parameter, the `method` will be set to `partial_cmp` automatically by default.

```rust
#[macro_use] extern crate educe;

use std::cmp::Ordering;

fn partial_cmp(a: &u8, b: &u8) -> Option<Ordering> {
    if a > b {
        Some(Ordering::Less)
    } else if a < b {
        Some(Ordering::Greater)
    } else {
        Some(Ordering::Equal)
    }
}

trait A {
    fn partial_cmp(&self, b: &Self) -> Option<Ordering>;
}

impl A for i32 {
    fn partial_cmp(&self, b: &i32) -> Option<Ordering> {
        if self > b {
            Some(Ordering::Less)
        } else if self < b {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

#[derive(Educe)]
#[educe(PartialEq, PartialOrd)]
enum Enum<T: std::cmp::PartialEq + A> {
    V1,
    V2 {
        #[educe(PartialOrd(method = "partial_cmp"))]
        f1: u8,
    },
    V3(
        #[educe(PartialOrd(trait = "A"))]
        T
    ),
}
```

#### Generic Parameters Bound to the `PartialOrd` Trait or Others

The `#[educe(PartialOrd(bound))]` attribute can be used to add the `PartialOrd` trait bound to all generic parameters for the `PartialOrd` implementation.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq(bound), PartialOrd(bound))]
enum Enum<T, K> {
    V1,
    V2 {
        f1: K,
    },
    V3(
        T
    ),
}
```

Or you can set the where predicates by yourself. (NOTE: The `PartialOrd` trait depends on the `PartialEq` (`PartialEq<Self>`) trait.)

```rust
#[macro_use] extern crate educe;

use std::cmp::Ordering;

trait A {
    fn partial_cmp(&self, b: &Self) -> Option<Ordering>;
}

impl A for i32 {
    fn partial_cmp(&self, b: &i32) -> Option<Ordering> {
        if self > b {
            Some(Ordering::Less)
        } else if self < b {
            Some(Ordering::Greater)
        } else {
            Some(Ordering::Equal)
        }
    }
}

#[derive(Educe)]
#[educe(PartialEq(bound), PartialOrd(bound = "T: std::cmp::PartialOrd, K: std::cmp::PartialOrd + A"))]
enum Enum<T, K> {
    V1,
    V2 {
        #[educe(PartialOrd(trait = "A"))]
        f1: K,
    },
    V3(
        T
    ),
}
```

#### Ranking

Each field can add a `#[educe(PartialOrd(rank = priority_value))]` attribute where `priority_value` is a positive integer value to determine their comparing precedence (lower `priority_value` leads to higher priority). The default `priority_value` for a field dependends on its ordinal (the lower the front) and is always lower than any custom `priority_value`.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq, PartialOrd)]
struct Struct {
    #[educe(PartialOrd(rank = 1))]
    f1: u8,
    #[educe(PartialOrd(rank = 0))]
    f2: u8,
}
```

Each variant can add a `#[educe(PartialOrd(rank = comparison_value))]` attribute where `comparison_value` is a positive integer value to override the value or the ordinal of a variant for comparison.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq, PartialOrd)]
enum Enum {
    #[educe(PartialOrd(rank = 2))]
    Two,
    #[educe(PartialOrd(rank = 1))]
    One,
}
```

## Ord

Use `#[derive(Educe)]` and `#[educe(Ord)]` to implement the `Ord` trait for a struct or an enum. It supports to ignore some fields, or set a trait and/or a method to replace the `Ord` trait used by default. The rank of variants and fields can also be modified.

#### Basic Usage

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq, Eq, PartialOrd, Ord)]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(PartialEq, Eq, PartialOrd, Ord)]
enum Enum {
    V1,
    V2 {
        f1: u8,
    },
    V3(u8),
}
```

#### Ignore Fields

The `ignore` attribute can ignore specific fields.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq, Eq, PartialOrd, Ord)]
struct Struct {
    #[educe(Ord(ignore))]
    f1: u8
}

#[derive(Educe)]
#[educe(PartialEq, Eq, PartialOrd, Ord)]
enum Enum {
    V1,
    V2 {
        #[educe(Ord(ignore))]
        f1: u8,
    },
    V3(
        #[educe(Ord(ignore))]
        u8
    ),
}
```

#### Use Another Method or Trait to Do Comparing

The `trait` and `method` attributes can be used to replace the `Ord` trait for fields. If you only set the `trait` parameter, the `method` will be set to `cmp` automatically by default.

```rust
#[macro_use] extern crate educe;

use std::cmp::Ordering;

fn cmp(a: &u8, b: &u8) -> Ordering {
    if a > b {
        Ordering::Less
    } else if a < b {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

trait A {
    fn cmp(&self, b: &Self) -> Ordering;
}

impl A for i32 {
    fn cmp(&self, b: &i32) -> Ordering {
        if self > b {
            Ordering::Less
        } else if self < b {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

#[derive(Educe)]
#[educe(PartialEq, Eq, PartialOrd, Ord)]
enum Enum<T: std::cmp::PartialOrd + A> {
    V1,
    V2 {
        #[educe(Ord(method = "cmp"))]
        f1: u8,
    },
    V3(
        #[educe(Ord(trait = "A"))]
        T
    ),
}
```

#### Generic Parameters Bound to the `Ord` Trait or Others

The `#[educe(Ord(bound))]` attribute can be used to add the `Ord` trait bound to all generic parameters for the `Ord` implementation.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq(bound), Eq(bound), PartialOrd(bound), Ord(bound))]
enum Enum<T, K> {
    V1,
    V2 {
        f1: K,
    },
    V3(
        T
    ),
}
```

Or you can set the where predicates by yourself. (NOTE: The `Ord` trait depends on the `PartialOrd` (`PartialOrd<Self>`) trait and the `Eq` trait.)

```rust
#[macro_use] extern crate educe;

use std::cmp::Ordering;

trait A {
    fn cmp(&self, b: &Self) -> Ordering;
}

impl A for i32 {
    fn cmp(&self, b: &i32) -> Ordering {
        if self > b {
            Ordering::Less
        } else if self < b {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

#[derive(Educe)]
#[educe(PartialEq(bound), Eq(bound), PartialOrd(bound), Ord(bound = "T: std::cmp::Ord, K: std::cmp::Ord + A"))]
enum Enum<T, K> {
    V1,
    V2 {
        #[educe(Ord(trait = "A"))]
        f1: K,
    },
    V3(
        T
    ),
}
```

#### Ranking

Each field can add a `#[educe(Ord(rank = priority_value))]` attribute where `priority_value` is a positive integer value to determine their comparing precedence (lower `priority_value` leads to higher priority). The default `priority_value` for a field dependends on its ordinal (the lower the front) and is always lower than any custom `priority_value`.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq, Eq, PartialOrd, Ord)]
struct Struct {
    #[educe(Ord(rank = 1))]
    f1: u8,
    #[educe(Ord(rank = 0))]
    f2: u8,
}
```

Each variant can add a `#[educe(Ord(rank = comparison_value))]` attribute where `comparison_value` is a positive integer value to override the value or the ordinal of a variant for comparison.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(PartialEq, Eq, PartialOrd, Ord)]
enum Enum {
    #[educe(Ord(rank = 2))]
    Two,
    #[educe(Ord(rank = 1))]
    One,
}
```

## Hash

Use `#[derive(Educe)]` and `#[educe(Hash)]` to implement the `Hash` trait for a struct or an enum. It supports to ignore some fields, or set a trait and/or a method to replace the `Hash` trait used by default.

#### Basic Usage

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Hash)]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(Hash)]
enum Enum {
    V1,
    V2 {
        f1: u8,
    },
    V3(u8),
}
```

#### Ignore Fields

The `ignore` attribute can ignore specific fields.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Hash)]
struct Struct {
    #[educe(Hash(ignore))]
    f1: u8
}

#[derive(Educe)]
#[educe(Hash)]
enum Enum {
    V1,
    V2 {
        #[educe(Hash(ignore))]
        f1: u8,
    },
    V3(
        #[educe(Hash(ignore))]
        u8
    ),
}
```

#### Use Another Method or Trait to Do Hashing

The `trait` and `method` attributes can be used to replace the `Hash` trait for fields. If you only set the `trait` parameter, the `method` will be set to `hash` automatically by default.

```rust
#[macro_use] extern crate educe;

use std::hash::{Hash, Hasher};

fn hash<H: Hasher>(_s: &u8, state: &mut H) {
    Hash::hash(&100, state)
}

trait A {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&100, state)
    }
}

impl A for i32 {};
impl A for u64 {};

#[derive(Educe)]
#[educe(Hash)]
enum Enum<T: A> {
    V1,
    V2 {
        #[educe(Hash(method = "hash"))]
        f1: u8,
    },
    V3(
        #[educe(Hash(trait = "A"))]
        T
    ),
}
```

#### Generic Parameters Bound to the `Hash` Trait or Others

The `#[educe(Hash(bound))]` attribute can be used to add the `Hash` trait bound to all generic parameters for the `Hash` implementation.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Hash(bound))]
enum Enum<T, K> {
    V1,
    V2 {
        f1: K,
    },
    V3(
        T
    ),
}
```

Or you can set the where predicates by yourself.

```rust
#[macro_use] extern crate educe;

use std::hash::{Hash, Hasher};

fn hash<H: Hasher>(_s: &u8, state: &mut H) {
    Hash::hash(&100, state)
}

trait A {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&100, state)
    }
}

impl A for i32 {};
impl A for u64 {};

#[derive(Educe)]
#[educe(Hash(bound = "T: std::hash::Hash, K: A"))]
enum Enum<T, K> {
    V1,
    V2 {
        #[educe(Hash(trait = "A"))]
        f1: K,
    },
    V3(
        T
    ),
}
```

## Default

Use `#[derive(Educe)]` and `#[educe(Default)]` to implement the `Default` trait for a struct, an enum, or a union. It supports to set the default value for your type directly, or set the default values for specific fields.

#### Basic Usage

For enums and unions, you need to assign a variant (of a enum) and a field (of a union) as default unless the number of variants of an enum or the number of fields of a union is exactly one.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Default)]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(Default)]
enum Enum {
    V1,
    #[educe(Default)]
    V2 {
        f1: u8,
    },
    V3(u8),
}

#[derive(Educe)]
#[educe(Default)]
union Union {
    f1: u8,
    #[educe(Default)]
    f2: f64,
}
```

#### The Default Value for the Whole Type

The `#[educe(Default(expression = "expression"))]` attribute can be used to set the default value for your type by an expression.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Default(expression = "Struct { f1: 1 }"))]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(Default(expression = "Enum::Struct { f1: 1 }"))]
enum Enum {
    Unit,
    Struct {
        f1: u8
    },
    Tuple(u8),
}

#[derive(Educe)]
#[educe(Default(expression = "Union { f1: 1 }"))]
union Union {
    f1: u8,
    f2: f64,
}
```

#### The Default Values for Specific Fields

The `#[educe(Default = literal)]` attribute or the `#[educe(Default(expression = "expression"))]` attribute can be used to set the default value for a specific field by a literal value or an expression.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Default)]
struct Struct {
    #[educe(Default = 1)]
    f1: u8,
    #[educe(Default = 11111111111111111111111111111)]
    f2: i128,
    #[educe(Default = 1.1)]
    f3: f64,
    #[educe(Default = true)]
    f4: bool,
    #[educe(Default = "Hi")]
    f5: &'static str,
    #[educe(Default = "Hello")]
    f6: String,
    #[educe(Default = 'M')]
    f7: char,
}

#[derive(Educe)]
#[educe(Default)]
enum Enum {
    Unit,
    #[educe(Default)]
    Tuple(
        #[educe(Default(expression = "0 + 1"))]
        u8,
        #[educe(Default(expression = "-11111111111111111111111111111 * -1"))]
        i128,
        #[educe(Default(expression = "1.0 + 0.1"))]
        f64,
        #[educe(Default(expression = "!false"))]
        bool,
        #[educe(Default(expression = "\"Hi\""))]
        &'static str,
        #[educe(Default(expression = "String::from(\"Hello\")"))]
        String,
        #[educe(Default(expression = "'M'"))]
        char,
    ),
}

#[derive(Educe)]
#[educe(Default)]
union Union {
    f1: u8,
    f2: i128,
    f3: f64,
    f4: bool,
    #[educe(Default = "Hi")]
    f5: &'static str,
    f6: char,
}
```

#### Generic Parameters Bound to the `Default` Trait or Others

The `#[educe(Default(bound))]` attribute can be used to add the `Default` trait bound to all generic parameters for the `Default` implementation.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Default(bound))]
enum Enum<T> {
    Unit,
    #[educe(Default)]
    Struct {
        f1: T
    },
    Tuple(T),
}
```

Or you can set the where predicates by yourself.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Default(bound = "T: std::default::Default"))]
enum Enum<T> {
    Unit,
    #[educe(Default)]
    Struct {
        f1: T
    },
    Tuple(T),
}
```

#### The `new` Associated Function

With the `#[educe(Default(new))]` attribute, your type will have an extra associated function called `new`. That can be used to invoke the `default` method of the `Default` trait.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Default(new))]
struct Struct {
    f1: u8
}
```

## Clone

Use `#[derive(Educe)]` and `#[educe(Clone)]` to implement the `Clone` trait for a struct, an enum, or a union. It supports to set a trait and/or a method to replace the `Clone` trait used by default.

#### Basic Usage

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Clone)]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(Clone)]
enum Enum {
    V1,
    V2 {
        f1: u8,
    },
    V3(u8),
}
```

#### Use Another Method or Trait to Do Cloning

The `trait` and `method` attributes can be used to replace the `Clone` trait for fields. If you only set the `trait` parameter, the `method` will be set to `clone` automatically by default.

```rust
#[macro_use] extern crate educe;

fn clone(v: &u8) -> u8 {
    v + 100
}

trait A {
    fn clone(&self) -> Self;
}

impl A for i32 {
    fn clone(&self) -> i32 {
        self + 100
    }
}

impl A for u64 {
    fn clone(&self) -> u64 {
        self + 100
    }
}

#[derive(Educe)]
#[educe(Clone)]
enum Enum<T: A> {
    V1,
    V2 {
        #[educe(Clone(method = "clone"))]
        f1: u8,
    },
    V3(
        #[educe(Clone(trait = "A"))]
        T
    ),
}
```

#### Generic Parameters Bound to the `Clone` Trait or Others

The `#[educe(Clone(bound))]` attribute can be used to add the `Clone` trait bound or the `Copy` trait bound (if the `#[educe(Copy)]` attribute exists) to all generic parameters for the `Clone` implementation.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Clone(bound))]
enum Enum<T, K> {
    V1,
    V2 {
        f1: K,
    },
    V3(
        T
    ),
}
```

Or you can set the where predicates by yourself.

```rust
#[macro_use] extern crate educe;

fn clone(v: &u8) -> u8 {
    v + 100
}

trait A {
    fn clone(&self) -> Self;
}

impl A for i32 {
    fn clone(&self) -> i32 {
        self + 100
    }
}

impl A for u64 {
    fn clone(&self) -> u64 {
        self + 100
    }
}

#[derive(Educe)]
#[educe(Clone(bound = "T: std::clone::Clone, K: A"))]
enum Enum<T, K> {
    V1,
    V2 {
        #[educe(Clone(trait = "A"))]
        f1: K,
    },
    V3(
        T
    ),
}
```

#### Union

The `#[educe(Clone)]` attribute can be used for a union which also needs to implement the `Copy` trait. The fields of a union cannot be cloned with other methods or traits.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Copy, Clone)]
union Union {
    f1: u8,
}
```

## Copy

Use `#[derive(Educe)]` and `#[educe(Copy)]` to implement the `Copy` trait for a struct, an enum, or a union.

#### Basic Usage

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Copy, Clone)]
struct Struct {
    f1: u8
}

#[derive(Educe)]
#[educe(Copy, Clone)]
enum Enum {
    V1,
    V2 {
        f1: u8,
    },
    V3(u8),
}
```

#### Generic Parameters Bound to the `Copy` Trait or Others

The `#[educe(Copy(bound))]` attribute can be used to add the `Copy` trait bound to all generic parameters for the `Copy` implementation.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Copy(bound), Clone(bound))]
enum Enum<T, K> {
    V1,
    V2 {
        f1: K,
    },
    V3(
        T
    ),
}
```

Or you can set the where predicates by yourself.

```rust
#[macro_use] extern crate educe;

fn clone(v: &u8) -> u8 {
    v + 100
}

trait A {
    fn clone(&self) -> Self;
}

impl A for i32 {
    fn clone(&self) -> i32 {
        self + 100
    }
}

impl A for u64 {
    fn clone(&self) -> u64 {
        self + 100
    }
}

#[derive(Educe)]
#[educe(Copy(bound = "T: Copy, K: A + Copy"), Clone(bound = "T: Copy, K: A + Copy"))]
enum Enum<T, K> {
    V1,
    V2 {
        #[educe(Clone(trait = "A"))]
        f1: K,
    },
    V3(
        T
    ),
}
```

#### Copy and Clone

If you implement both of the `Copy` trait and the `Clone` trait by Educe, the bound for the `Clone` trait needs to include the `Copy` trait due to `Copy, Clone` optimization.

## Deref

Use `#[derive(Educe)]` and `#[educe(Deref)]` to implement the `Deref` trait for a struct or an enum.

#### Basic Usage

You need to assign a field as a default inmutable dereferencing field unless the number of fields is exactly one.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Deref)]
struct Struct {
    f1: u8,
    #[educe(Deref)]
    f2: u8,
}

#[derive(Educe)]
#[educe(Deref)]
enum Enum {
    Struct {
        f1: u8
    },
    Struct2 {
        f1: u8,
        #[educe(Deref)]
        f2: u8,
    },
    Tuple(u8),
    Tuple2(
        u8,
        #[educe(Deref)]
        u8
    ),
}
```

## DerefMut

Use `#[derive(Educe)]` and `#[educe(DerefMut)]` to implement the `DerefMut` trait for a struct or an enum.

#### Basic Usage

You need to assign a field as a default mutable dereferencing field unless the number of fields is exactly one.

```rust
#[macro_use] extern crate educe;

#[derive(Educe)]
#[educe(Deref, DerefMut)]
struct Struct {
    f1: u8,
    #[educe(Deref, DerefMut)]
    f2: u8,
}

#[derive(Educe)]
#[educe(Deref, DerefMut)]
enum Enum {
    Struct {
        f1: u8
    },
    Struct2 {
        f1: u8,
        #[educe(Deref, DerefMut)]
        f2: u8,
    },
    Tuple(u8),
    Tuple2(
        #[educe(DerefMut)]
        u8,
        #[educe(Deref)]
        u8
    ),
}
```

The mutable dereferencing fields don't need to be the same as the inmutable dereferencing fields. But their type must be the same.

## TODO

There is a lot of work to be done. Unimplemented traits are listed below:

1. `From`
1. `Into`
1. `FromStr`
1. `TryFrom`
1. `TryInto`

## Crates.io

https://crates.io/crates/educe

## Documentation

https://docs.rs/educe

## License

[MIT](LICENSE)
