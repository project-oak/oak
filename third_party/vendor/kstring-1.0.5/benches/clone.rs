#![allow(
    clippy::clone_on_copy,
    clippy::useless_conversion,
    clippy::clone_double_ref
)]

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

type StringCow<'s> = std::borrow::Cow<'s, str>;

#[cfg(not(feature = "bench_subset_unstable"))]
pub static FIXTURES: &[&str] = &[
    "",
    "0",
    "01",
    "012",
    "0123",
    "01234",
    "012345",
    "0123456",
    "01234567",
    "012345678",
    "0123456789",
    "01234567890123456789",
    "0123456789012345678901234567890123456789",
    "01234567890123456789012345678901234567890123456789012345678901234567890123456789",
];

#[cfg(feature = "bench_subset_unstable")]
pub static FIXTURES: &[&str] = &[
    "0123456789",
    "01234567890123456789012345678901234567890123456789012345678901234567890123456789",
];

fn bench_clone(c: &mut Criterion) {
    let mut group = c.benchmark_group("clone");
    for fixture in FIXTURES {
        let len = fixture.len();
        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(BenchmarkId::new("&'static str", len), &len, |b, _| {
            let uut = *fixture;
            let uut = criterion::black_box(uut);
            b.iter(|| uut.clone())
        });
        group.bench_with_input(BenchmarkId::new("String", len), &len, |b, _| {
            let uut = String::from(*fixture);
            let uut = criterion::black_box(uut);
            b.iter(|| uut.clone())
        });
        group.bench_with_input(BenchmarkId::new("Box<str>", len), &len, |b, _| {
            let uut = Box::<str>::from(*fixture);
            let uut = criterion::black_box(uut);
            b.iter(|| uut.clone())
        });
        group.bench_with_input(BenchmarkId::new("Arc<str>", len), &len, |b, _| {
            let uut = std::sync::Arc::<str>::from(*fixture);
            let uut = criterion::black_box(uut);
            b.iter(|| uut.clone())
        });
        group.bench_with_input(
            BenchmarkId::new("StringCow::Borrowed", len),
            &len,
            |b, _| {
                let uut = StringCow::Borrowed(*fixture);
                let uut = criterion::black_box(uut);
                b.iter(|| uut.clone())
            },
        );
        group.bench_with_input(BenchmarkId::new("StringCow::Owned", len), &len, |b, _| {
            let fixture = String::from(*fixture);
            let uut = StringCow::Owned(fixture);
            let uut = criterion::black_box(uut);
            b.iter(|| uut.clone())
        });
        group.bench_with_input(BenchmarkId::new("SmolStr::new", len), &len, |b, _| {
            let uut = smol_str::SmolStr::new(fixture);
            let uut = criterion::black_box(uut);
            b.iter(|| uut.clone())
        });
        group.bench_with_input(
            BenchmarkId::new("KString::from_static", len),
            &len,
            |b, _| {
                let uut = kstring::KString::from_static(*fixture);
                let uut = criterion::black_box(uut);
                b.iter(|| uut.clone())
            },
        );
        group.bench_with_input(BenchmarkId::new("KString::from_ref", len), &len, |b, _| {
            let fixture = String::from(*fixture);
            let uut = kstring::KString::from_ref(&fixture);
            let uut = criterion::black_box(uut);
            b.iter(|| uut.clone())
        });
        group.bench_with_input(
            BenchmarkId::new("KString::from_string", len),
            &len,
            |b, _| {
                let fixture = String::from(*fixture);
                let uut = kstring::KString::from_string(fixture);
                let uut = criterion::black_box(uut);
                b.iter(|| uut.clone())
            },
        );
        group.bench_with_input(
            BenchmarkId::new("KStringCow::from_static", len),
            &len,
            |b, _| {
                let uut = kstring::KStringCow::from_static(*fixture);
                let uut = criterion::black_box(uut);
                b.iter(|| uut.clone())
            },
        );
        group.bench_with_input(
            BenchmarkId::new("KStringCow::from_ref", len),
            &len,
            |b, _| {
                let fixture = String::from(*fixture);
                let uut = kstring::KStringCow::from_ref(&fixture);
                let uut = criterion::black_box(uut);
                b.iter(|| uut.clone())
            },
        );
        group.bench_with_input(
            BenchmarkId::new("KStringCow::from_string", len),
            &len,
            |b, _| {
                let fixture = String::from(*fixture);
                let uut = kstring::KStringCow::from_string(fixture);
                let uut = criterion::black_box(uut);
                b.iter(|| uut.clone())
            },
        );
        group.bench_with_input(
            BenchmarkId::new("KStringRef::from_static", len),
            &len,
            |b, _| {
                let uut = kstring::KStringRef::from_static(*fixture);
                let uut = criterion::black_box(uut);
                b.iter(|| uut.clone())
            },
        );
        group.bench_with_input(
            BenchmarkId::new("KStringRef::from_ref", len),
            &len,
            |b, _| {
                let fixture = String::from(*fixture);
                let uut = kstring::KStringRef::from_ref(&fixture);
                let uut = criterion::black_box(uut);
                b.iter(|| uut.clone())
            },
        );
    }
    group.finish();
}

criterion_group!(benches, bench_clone);
criterion_main!(benches);
