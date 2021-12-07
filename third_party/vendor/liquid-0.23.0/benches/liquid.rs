use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

pub static FIXTURES: &[&str] = &["Hello World"];

fn bench_fixtures(c: &mut Criterion) {
    let mut group = c.benchmark_group("liquid_bench_fixtures");
    for fixture in FIXTURES {
        group.bench_function(BenchmarkId::new("parse", fixture), |b| {
            let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
            b.iter(|| parser.parse(fixture));
        });
        group.bench_function(BenchmarkId::new("render", fixture), |b| {
            let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
            let template = parser
                .parse(fixture)
                .expect("Benchmark template parsing failed");

            let data = liquid::Object::new();

            template.render(&data).unwrap();
            b.iter(|| template.render(&data));
        });
    }
    group.finish();
}

criterion_group!(benches, bench_fixtures);
criterion_main!(benches);
