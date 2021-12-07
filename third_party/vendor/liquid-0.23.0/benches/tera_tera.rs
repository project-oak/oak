#[macro_use]
extern crate serde_derive;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use tera::{Context, Template, Tera, Value};

static VARIABLE_ONLY: &str = "{{product.name}}";

static SIMPLE_TEMPLATE: &str = "
<html>
  <head>
    <title>{{ product.name }}</title>
  </head>
  <body>
    <h1>{{ product.name }} - {{ product.manufacturer | upper }}</h1>
    <p>{{ product.summary }}</p>
    <p>£{{ product.price * 1.20 }} (VAT inc.)</p>
    <p>Look at reviews from your friends {{ username }}</p>
    <button>Buy!</button>
  </body>
</html>
";

static SIMPLE_TEMPLATE_LIQUID: &str = "
<html>
  <head>
    <title>{{ product.name }}</title>
  </head>
  <body>
    <h1>{{ product.name }} - {{ product.manufacturer | upcase }}</h1>
    <p>{{ product.summary }}</p>
    <p>£{{ product.price | times: 1.20 }} (VAT inc.)</p>
    <p>Look at reviews from your friends {{ username }}</p>
    <button>Buy!</button>
  </body>
</html>
";

#[derive(Debug, Serialize)]
struct Product {
    name: String,
    manufacturer: String,
    price: i32,
    summary: String,
}
impl Product {
    pub fn new() -> Product {
        Product {
            name: "Moto G".to_owned(),
            manufacturer: "Motorala".to_owned(),
            summary: "A phone".to_owned(),
            price: 100,
        }
    }
}

static PRODUCTS_YAML: &str = "
username: bob
product:
  name: Moto G
  manufacturer: Motorola
  summary: A phone
  price: 100
";

fn bench_parsing_basic_template(c: &mut Criterion) {
    let mut group = c.benchmark_group("bench_parsing_basic_template");
    group.bench_function(BenchmarkId::new("render", "tera"), |b| {
        b.iter(|| Template::new("bench", None, SIMPLE_TEMPLATE));
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        parser
            .parse(SIMPLE_TEMPLATE_LIQUID)
            .expect("benchmark template parsing failed");
        b.iter(|| parser.parse(SIMPLE_TEMPLATE_LIQUID));
    });
    group.finish();
}

fn bench_rendering_only_variable(c: &mut Criterion) {
    let mut group = c.benchmark_group("bench_rendering_only_variable");
    group.bench_function(BenchmarkId::new("render", "tera"), |b| {
        let mut tera = Tera::default();
        tera.add_raw_template("test.html", VARIABLE_ONLY).unwrap();
        let mut context = Context::new();
        context.insert("product", &Product::new());
        context.insert("username", &"bob");

        b.iter(|| tera.render("test.html", &context));
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        let template = parser
            .parse(VARIABLE_ONLY)
            .expect("Benchmark template parsing failed");

        let data: liquid::Object =
            serde_yaml::from_str(PRODUCTS_YAML).expect("Benchmark object parsing failed");

        template.render(&data).unwrap();
        b.iter(|| template.render(&data));
    });
    group.finish();
}

fn bench_rendering_basic_template(c: &mut Criterion) {
    let mut group = c.benchmark_group("bench_rendering_basic_templates");
    group.bench_function(BenchmarkId::new("render", "tera"), |b| {
        let mut tera = Tera::default();
        tera.add_raw_template("bench.html", SIMPLE_TEMPLATE)
            .unwrap();
        let mut context = Context::new();
        context.insert("product", &Product::new());
        context.insert("username", &"bob");

        b.iter(|| tera.render("bench.html", &context));
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        let template = parser
            .parse(SIMPLE_TEMPLATE_LIQUID)
            .expect("Benchmark template parsing failed");

        let data: liquid::Object =
            serde_yaml::from_str(PRODUCTS_YAML).expect("Benchmark object parsing failed");

        template.render(&data).unwrap();
        b.iter(|| template.render(&data));
    });
    group.finish();
}

fn bench_huge_loop(c: &mut Criterion) {
    #[derive(Serialize)]
    struct DataWrapper {
        v: String,
    }

    #[derive(Serialize)]
    struct RowWrapper {
        real: Vec<DataWrapper>,
        dummy: Vec<DataWrapper>,
    }
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

    let mut group = c.benchmark_group("bench_huge_loop");
    group.bench_function(BenchmarkId::new("render", "tera"), |b| {
        let mut tera = Tera::default();
        tera.add_raw_templates(vec![(
            "huge.html",
            "{% for real in rows.real %}{{real.v}}{% endfor %}",
        )])
        .unwrap();
        let mut context = Context::new();
        context.insert("rows", &rows);

        b.iter(|| tera.render("huge.html", &context));
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        let template = parser
            .parse("{% for this in real%}{{this.v}}{% endfor %}")
            .expect("Benchmark template parsing failed");

        let row_wrapper = liquid::to_object(&rows).unwrap();

        template.render(&row_wrapper).unwrap();
        b.iter(|| template.render(&row_wrapper));
    });
    group.finish();
}

fn deep_object() -> Value {
    let data = r#"{
                    "foo": {
                        "bar": {
                            "goo": {
                                "moo": {
                                    "cows": [
                                        {
                                            "name": "betsy",
                                            "age" : 2,
                                            "temperament": "calm"
                                        },
                                        {
                                            "name": "elsie",
                                            "age": 3,
                                            "temperament": "calm"
                                        },
                                        {
                                            "name": "veal",
                                            "age": 1,
                                            "temperament": "ornery"
                                        }
                                    ]
                                }
                            }
                        }
                    }
                  }"#;

    serde_json::from_str(data).unwrap()
}

fn deep_object_liquid() -> liquid::Object {
    liquid::object!({
        "deep_object": {
            "foo": {
                "bar": {
                    "goo": {
                        "moo": {
                            "cows": [
                                {
                                    "name": "betsy",
                                    "age" : 2,
                                    "temperament": "calm"
                                },
                                {
                                    "name": "elsie",
                                    "age": 3,
                                    "temperament": "calm"
                                },
                                {
                                    "name": "veal",
                                    "age": 1,
                                    "temperament": "ornery"
                                }
                            ]
                        }
                    }
                }
            }
        }
    })
}

fn bench_access_deep_object(c: &mut Criterion) {
    let mut group = c.benchmark_group("bench_access_deep_object");
    group.bench_function(BenchmarkId::new("render", "tera"), |b| {
        let mut tera = Tera::default();
        tera.add_raw_templates(vec![(
            "deep_object.html",
            "{% for cow in deep_object.foo.bar.goo.moo.cows %}{{cow.temperament}}{% endfor %}",
        )])
        .unwrap();
        let mut context = Context::new();
        context.insert("deep_object", &deep_object());
        assert!(tera
            .render("deep_object.html", &context)
            .unwrap()
            .contains("ornery"));

        b.iter(|| tera.render("deep_object.html", &context));
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        let template = parser
            .parse(
                "{% for cow in deep_object.foo.bar.goo.moo.cows %}{{cow.temperament}}{% endfor %}",
            )
            .expect("Benchmark template parsing failed");

        let data = deep_object_liquid();

        template.render(&data).unwrap();
        b.iter(|| template.render(&data));
    });
    group.finish();
}

fn bench_access_deep_object_with_literal(c: &mut Criterion) {
    let mut group = c.benchmark_group("bench_access_deep_object_with_literal");
    group.bench_function(BenchmarkId::new("render", "tera"), |b| {
        let mut tera = Tera::default();
        tera.add_raw_templates(vec![(
            "deep_object.html",
            "
{% set goo = deep_object.foo['bar'][\"goo\"] %}
{% for cow in goo.moo.cows %}{{cow.temperament}}
{% endfor %}",
        )])
        .unwrap();
        let mut context = Context::new();
        context.insert("deep_object", &deep_object());
        assert!(tera
            .render("deep_object.html", &context)
            .unwrap()
            .contains("ornery"));

        b.iter(|| tera.render("deep_object.html", &context));
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        let template = parser
            .parse(
                "
{% assign goo = deep_object.foo['bar'][\"goo\"] %}
{% for cow in goo.moo.cows %}{{cow.temperament}}
{% endfor %}
                ",
            )
            .expect("Benchmark template parsing failed");

        let data = deep_object_liquid();

        template.render(&data).unwrap();
        b.iter(|| template.render(&data));
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_parsing_basic_template,
    bench_rendering_only_variable,
    bench_rendering_basic_template,
    bench_huge_loop,
    bench_access_deep_object,
    bench_access_deep_object_with_literal,
);
criterion_main!(benches);
