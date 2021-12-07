#[macro_use]
extern crate serde_derive;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use tera::{Context, Tera};

fn bench_big_loop_big_object(c: &mut Criterion) {
    const NUM_OBJECTS: usize = 100;
    let mut objects = Vec::with_capacity(NUM_OBJECTS);
    for i in 0..NUM_OBJECTS {
        objects.push(BigObject::new(i));
    }

    let mut group = c.benchmark_group("bench_big_loop_big_object");
    group.bench_function(BenchmarkId::new("render", "tera"), |b| {
        let mut tera = Tera::default();
        tera.add_raw_templates(vec![(
            "big_loop.html",
            "
{%- for object in objects -%}
{{ object.field_a.i }}
{%- if object.field_a.i > 2 -%}
{%- break -%}
{%- endif -%}
{%- endfor -%}
",
        )])
        .unwrap();
        let mut context = Context::new();
        context.insert("objects", &objects);
        let rendering = tera.render("big_loop.html", &context).expect("Good render");
        assert_eq!(&rendering[..], "0123");
        b.iter(|| tera.render("big_loop.html", &context));
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        let template = parser
            .parse(
                "
{%- for object in objects -%}
{{ object.field_a.i }}
{%- if object.field_a.i > 2 -%}
{%- break -%}
{%- endif -%}
{%- endfor -%}
            ",
            )
            .expect("Benchmark template parsing failed");

        let mut root: std::collections::HashMap<&'static str, &[BigObject]> = Default::default();
        root.insert("objects", &objects);
        let root = liquid::to_object(&root).unwrap();

        let rendering = template.render(&root).unwrap();
        assert_eq!(rendering, "0123");
        b.iter(|| template.render(&root));
    });
    group.finish();
}

#[derive(Serialize)]
struct BigObject {
    field_a: DataWrapper,
    field_b: DataWrapper,
    field_c: DataWrapper,
    field_d: DataWrapper,
    field_e: DataWrapper,
    field_f: DataWrapper,
}

impl BigObject {
    fn new(i: usize) -> BigObject {
        BigObject {
            field_a: DataWrapper::new(i),
            field_b: DataWrapper::new(i),
            field_c: DataWrapper::new(i),
            field_d: DataWrapper::new(i),
            field_e: DataWrapper::new(i),
            field_f: DataWrapper::new(i),
        }
    }
}

#[derive(Serialize)]
struct DataWrapper {
    i: usize,
    v: String,
}

impl DataWrapper {
    fn new(i: usize) -> DataWrapper {
        DataWrapper {
            i,
            v: "Meta
Before we get to the details, two important notes about the ownership system.
Rust has a focus on safety and speed. It accomplishes these goals through many ‘zero-cost abstractions’, which means that in Rust, abstractions cost as little as possible in order to make them work. The ownership system is a prime example of a zero cost abstraction. All of the analysis we’ll talk about in this guide is done at compile time. You do not pay any run-time cost for any of these features.
However, this system does have a certain cost: learning curve. Many new users to Rust experience something we like to call ‘fighting with the borrow checker’, where the Rust compiler refuses to compile a program that the author thinks is valid. This often happens because the programmer’s mental model of how ownership should work doesn’t match the actual rules that Rust implements. You probably will experience similar things at first. There is good news, however: more experienced Rust developers report that once they work with the rules of the ownership system for a period of time, they fight the borrow checker less and less.
With that in mind, let’s learn about borrowing.".into(),
        }
    }
}

criterion_group!(benches, bench_big_loop_big_object,);
criterion_main!(benches);
