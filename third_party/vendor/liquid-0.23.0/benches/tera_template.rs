#[macro_use]
extern crate serde_derive;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use tera::{Context, Tera};

// Benches from https://github.com/djc/template-benchmarks-rs

pub fn bench_big_table(c: &mut Criterion) {
    let mut group = c.benchmark_group("bench_big_table");
    group.bench_function(BenchmarkId::new("render", "tera"), |b| {
        // 100 instead of 50 in the original benchmark to make the time bigger
        let size = 100;
        let mut table = Vec::with_capacity(size);
        for _ in 0..size {
            let mut inner = Vec::with_capacity(size);
            for i in 0..size {
                inner.push(i);
            }
            table.push(inner);
        }

        let mut tera = Tera::default();
        tera.add_raw_templates(vec![("big-table.html", BIG_TABLE_TEMPLATE_TERA)])
            .unwrap();
        let mut ctx = Context::new();
        ctx.insert("table", &table);

        b.iter(|| tera.render("big-table.html", &ctx));
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        // 100 instead of 50 in the original benchmark to make the time bigger
        let size = 100;
        let table: Vec<_> = (0..size)
            .map(|_| {
                let inner: Vec<_> = (0..size).map(|i| i as i32).collect();
                inner
            })
            .collect();

        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        let template = parser
            .parse(BIG_TABLE_TEMPLATE_LIQUID)
            .expect("Benchmark template parsing failed");

        let data = liquid::object!({ "table": table });

        template.render(&data).unwrap();
        b.iter(|| template.render(&data));
    });
    group.finish();
}

static BIG_TABLE_TEMPLATE_TERA: &str = "<table>
{% for row in table %}
<tr>{% for col in row %}<td>{{ col }}</td>{% endfor %}</tr>
{% endfor %}
</table>";
static BIG_TABLE_TEMPLATE_LIQUID: &str = "<table>
{% for row in table %}
<tr>{% for col in row %}<td>{{ col }}</td>{% endfor %}</tr>
{% endfor %}
</table>";

pub fn bench_teams(c: &mut Criterion) {
    let mut group = c.benchmark_group("bench_teams");
    group.bench_function(BenchmarkId::new("render", "tera"), |b| {
        let mut tera = Tera::default();
        tera.add_raw_templates(vec![("teams.html", TEAMS_TEMPLATE_TERA)])
            .unwrap();
        let mut ctx = Context::new();
        ctx.insert("year", &2015);
        ctx.insert(
            "teams",
            &vec![
                Team {
                    name: "Jiangsu".into(),
                    score: 43,
                },
                Team {
                    name: "Beijing".into(),
                    score: 27,
                },
                Team {
                    name: "Guangzhou".into(),
                    score: 22,
                },
                Team {
                    name: "Shandong".into(),
                    score: 12,
                },
            ],
        );

        b.iter(|| tera.render("teams.html", &ctx));
    });
    group.bench_function(BenchmarkId::new("render", "liquid"), |b| {
        let parser = liquid::ParserBuilder::with_stdlib().build().unwrap();
        let template = parser
            .parse(TEAMS_TEMPLATE_LIQUID)
            .expect("Benchmark template parsing failed");

        let data: liquid::Object =
            serde_yaml::from_str(TEAMS_DATA_LIQUID).expect("Benchmark object parsing failed");

        template.render(&data).unwrap();
        b.iter(|| template.render(&data));
    });
    group.finish();
}

#[derive(Serialize)]
struct Team {
    name: String,
    score: u8,
}

static TEAMS_TEMPLATE_TERA: &str = "<html>
  <head>
    <title>{{ year }}</title>
  </head>
  <body>
    <h1>CSL {{ year }}</h1>
    <ul>
    {% for team in teams %}
      <li class=\"{% if loop.first %}champion{% endif %}\">
      <b>{{team.name}}</b>: {{team.score}}
      </li>
    {% endfor %}
    </ul>
  </body>
</html>";

static TEAMS_DATA_LIQUID: &str = "
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

static TEAMS_TEMPLATE_LIQUID: &str = "<html>
  <head>
    <title>{{ year }}</title>
  </head>
  <body>
    <h1>CSL {{ year }}</h1>
    <ul>
    {% for team in teams %}
      <li class=\"{% if forloop.index0 == 0 %}champion{% endif %}\">
      <b>{{team.name}}</b>: {{team.score}}
      </li>
    {% endfor %}
    </ul>
  </body>
</html>";

criterion_group!(benches, bench_big_table, bench_teams,);
criterion_main!(benches);
