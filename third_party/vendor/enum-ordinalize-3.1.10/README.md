Enum Ordinalize
====================

[![CI](https://github.com/magiclen/enum-ordinalize/actions/workflows/ci.yml/badge.svg)](https://github.com/magiclen/enum-ordinalize/actions/workflows/ci.yml)

This crates provides a procedural macro to let enums not only get its variants' ordinal but also be constructed from an ordinal.

## Ordinalize

Use `#[derive(Ordinalize)]` to make an enum (which must only has unit variants) have `from_ordinal_unsafe`, `from_ordinal`, `variants`, and `variant_count` associated functions and a `ordinal` method.

```rust
#[macro_use] extern crate enum_ordinalize;

#[derive(Debug, PartialEq, Eq, Ordinalize)]
enum MyEnum {
    Zero,
    One,
    Two,
}

assert_eq!(0i8, MyEnum::Zero.ordinal());
assert_eq!(1i8, MyEnum::One.ordinal());
assert_eq!(2i8, MyEnum::Two.ordinal());

assert_eq!(Some(MyEnum::Zero), MyEnum::from_ordinal(0i8));
assert_eq!(Some(MyEnum::One), MyEnum::from_ordinal(1i8));
assert_eq!(Some(MyEnum::Two), MyEnum::from_ordinal(2i8));

assert_eq!(MyEnum::Zero, unsafe { MyEnum::from_ordinal_unsafe(0i8) });
assert_eq!(MyEnum::One, unsafe { MyEnum::from_ordinal_unsafe(1i8) });
assert_eq!(MyEnum::Two, unsafe { MyEnum::from_ordinal_unsafe(2i8) });
```

### Get Variants

```rust
#[macro_use] extern crate enum_ordinalize;

#[derive(Debug, PartialEq, Eq, Ordinalize)]
enum MyEnum {
    Zero,
    One,
    Two,
}

assert_eq!([MyEnum::Zero, MyEnum::One, MyEnum::Two], MyEnum::variants());
assert_eq!(3, MyEnum::variant_count());
```

`variants` and `variant_count` are constant functions.

## The (Ordinal) Size of an Enum

The ordinal value is an integer whose size is determined by the enum itself. The larger (or the smaller if it's negative) the variants' values are, the bigger the enum size is.

For example,

```rust
#[macro_use] extern crate enum_ordinalize;

#[derive(Debug, PartialEq, Eq, Ordinalize)]
enum MyEnum {
    Zero,
    One,
    Two,
    Thousand = 1000,
}

assert_eq!(0i16, MyEnum::Zero.ordinal());
assert_eq!(1i16, MyEnum::One.ordinal());
assert_eq!(2i16, MyEnum::Two.ordinal());

assert_eq!(Some(MyEnum::Zero), MyEnum::from_ordinal(0i16));
assert_eq!(Some(MyEnum::One), MyEnum::from_ordinal(1i16));
assert_eq!(Some(MyEnum::Two), MyEnum::from_ordinal(2i16));

assert_eq!(MyEnum::Zero, unsafe { MyEnum::from_ordinal_unsafe(0i16) });
assert_eq!(MyEnum::One, unsafe { MyEnum::from_ordinal_unsafe(1i16) });
assert_eq!(MyEnum::Two, unsafe { MyEnum::from_ordinal_unsafe(2i16) });
```

In order to store `1000`, the size of `MyEnum` grows. Thus, the ordinal is in `i16` instead of `i8`.

You can use the `#[repr(type)]` attribute to control the size explicitly. For instance,

```rust
#[macro_use] extern crate enum_ordinalize;

#[derive(Debug, PartialEq, Eq, Ordinalize)]
#[repr(usize)]
enum MyEnum {
    Zero,
    One,
    Two,
    Thousand = 1000,
}

assert_eq!(0usize, MyEnum::Zero.ordinal());
assert_eq!(1usize, MyEnum::One.ordinal());
assert_eq!(2usize, MyEnum::Two.ordinal());

assert_eq!(Some(MyEnum::Zero), MyEnum::from_ordinal(0usize));
assert_eq!(Some(MyEnum::One), MyEnum::from_ordinal(1usize));
assert_eq!(Some(MyEnum::Two), MyEnum::from_ordinal(2usize));

assert_eq!(MyEnum::Zero, unsafe { MyEnum::from_ordinal_unsafe(0usize) });
assert_eq!(MyEnum::One, unsafe { MyEnum::from_ordinal_unsafe(1usize) });
assert_eq!(MyEnum::Two, unsafe { MyEnum::from_ordinal_unsafe(2usize) });
```

## Useful Increments

The integers represented by variants are extended in successive increments and can be set explicitly from anywhere.

```rust
#[macro_use] extern crate enum_ordinalize;

#[derive(Debug, PartialEq, Eq, Ordinalize)]
enum MyEnum {
    Two   = 2,
    Three,
    Four,
    Eight = 8,
    Nine,
    NegativeTen = -10,
    NegativeNine,
}

assert_eq!(4i8, MyEnum::Four.ordinal());
assert_eq!(9i8, MyEnum::Nine.ordinal());
assert_eq!(-9i8, MyEnum::NegativeNine.ordinal());

assert_eq!(Some(MyEnum::Four), MyEnum::from_ordinal(4i8));
assert_eq!(Some(MyEnum::Nine), MyEnum::from_ordinal(9i8));
assert_eq!(Some(MyEnum::NegativeNine), MyEnum::from_ordinal(-9i8));

assert_eq!(MyEnum::Four, unsafe { MyEnum::from_ordinal_unsafe(4i8) });
assert_eq!(MyEnum::Nine, unsafe { MyEnum::from_ordinal_unsafe(9i8) });
assert_eq!(MyEnum::NegativeNine, unsafe { MyEnum::from_ordinal_unsafe(-9i8) });
```

## Crates.io

https://crates.io/crates/enum-ordinalize

## Documentation

https://docs.rs/enum-ordinalize

## License

[MIT](LICENSE)