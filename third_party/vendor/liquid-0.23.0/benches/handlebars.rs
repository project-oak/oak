#[macro_use]
extern crate serde_derive;

use std::collections::BTreeMap;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use handlebars::{to_json, Handlebars, Template};
use serde_json::value::Value as Json;

static SOURCE_HANDLEBARS: &str = "<html>
  <head>
    <title>{{year}}</title>
  </head>
  <body>
    <h1>CSL {{year}}</h1>
    <ul>
    {{#each teams}}
      <li class=\"{{#if @first}}champion{{/if}}\">
      <b>{{name}}</b>: {{score}}
      </li>
    {{/each}}
    </ul>
  </body>
</html>";

fn make_data_handlebars() -> BTreeMap<String, Json> {
    let mut data = BTreeMap::new();

    data.insert("year".to_string(), to_json("2015"));

    let mut teams = Vec::new();

    for v in vec![
        ("Jiangsu", 43u16),
        ("Beijing", 27u16),
        ("Guangzhou", 22u16),
        ("Shandong", 12u16),
    ]
    .iter()
    {
        let (name, score) = *v;
        let mut t = BTreeMap::new();
        t.insert("name".to_string(), to_json(name));
        t.insert("score".to_string(), to_json(score));
        teams.push(t)
    }

    data.insert("teams".to_string(), to_json(&teams));
    data
}

static SOURCE_LIQUID: &str = "<html>
  <head>
    <title>{{year}}</title>
  </head>
  <body>
    <h1>CSL {{year}}</h1>
    <ul>
    {% for team in teams %}
      <li class=\"{% if forloop.index0 == 0 %}champion{% endif %}\">
      <b>{{team.name}}</b>: {{team.score}}
      </li>
    {% endfor %}
    </ul>
  </body>
</html>";
static DATA_LIQUID: &str = "
year: 2015
teams:
  - name: Jiangsu
    score: 43
  - name: Beijing
    score: 27
  - name: Guangzhou
    score: 22
  - name: Shandong
    score: 12
";

fn bench_template(c: &mut Criterion) {
    let mut group = c.benchmark_group("handlebars_bench_template");
    group.bench_function(BenchmarkId::new("parse", "handlebars"), |b| {
        b.iter(|| Template::compile(SOURCE_HANDLEBARS).unwrap());
    });
    group.bench_function(BenchmarkId::new("render", "handlebars"), |b| {
        let mut handlebars = Handlebars::new();
        handlebars
            .register_template_string("table", SOURCE_HANDLEBARS)
            .expect("Invalid template format");

        let data = make_data_handlebars();
        b.iter(|| handlebars.render("table", &data).unwrap())
    });
    group.bench_function(BenchmarkId::new("parse", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        b.iter(|| parser.parse(SOURCE_LIQUID));
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        let template = parser
            .parse(SOURCE_LIQUID)
            .expect("Benchmark template parsing failed");

        let data: liquid::Object =
            serde_yaml::from_str(DATA_LIQUID).expect("Benchmark object parsing failed");

        template.render(&data).unwrap();
        b.iter(|| template.render(&data));
    });
    group.finish();
}

#[derive(Serialize)]
struct DataWrapper {
    v: String,
}

#[derive(Serialize)]
struct RowWrapper {
    real: Vec<DataWrapper>,
    dummy: Vec<DataWrapper>,
}

fn bench_large_loop(c: &mut Criterion) {
    let real: Vec<DataWrapper> = (1..1000)
        .map(|i| DataWrapper {
            v: format!("n={}", i),
        })
        .collect();
    let dummy: Vec<DataWrapper> = (1..1000)
        .map(|i| DataWrapper {
            v: format!("n={}", i),
        })
        .collect();
    let rows = RowWrapper { real, dummy };
    let row_wrapper = liquid::to_object(&rows).unwrap();

    let mut group = c.benchmark_group("handlebars_bench_large_loop");
    group.bench_function(BenchmarkId::new("render", "handlebars"), |b| {
        let mut handlebars = Handlebars::new();
        handlebars
            .register_template_string("test", "BEFORE\n{{#each real}}{{this.v}}{{/each}}AFTER")
            .expect("Invalid template format");

        b.iter(|| handlebars.render("test", &rows).unwrap());
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        let template = parser
            .parse("BEFORE\n{% for this in real%}{{this.v}}{%endfor%}AFTER")
            .expect("Benchmark template parsing failed");

        template.render(&row_wrapper).unwrap();
        b.iter(|| template.render(&row_wrapper));
    });
    group.finish();
}

criterion_group!(benches, bench_template, bench_large_loop);
criterion_main!(benches);
