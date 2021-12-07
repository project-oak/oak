use criterion::*;

fn parse_stdlib(c: &mut Criterion) {
    let stdlib = std::fs::read_to_string("stdlib.nnef").unwrap();
    c.bench_function("parse_stdlib", |b| {
        b.iter(|| tract_nnef::ast::parse::parse_fragments(&stdlib))
    });
}

criterion_group!(parser, parse_stdlib);
criterion_main!(parser);
