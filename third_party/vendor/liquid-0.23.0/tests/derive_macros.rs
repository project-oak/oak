use liquid::{Parser, ParserBuilder};
use liquid_core::parser::FilterReflection;

mod derive_macros_test_filters;

fn build_parser() -> Parser {
    ParserBuilder::new()
        .filter(derive_macros_test_filters::TestPositionalFilterParser)
        .filter(derive_macros_test_filters::TestKeywordFilterParser)
        .filter(derive_macros_test_filters::TestMixedFilterParser)
        .filter(derive_macros_test_filters::TestParameterlessFilterParser)
        .build()
        .unwrap()
}

#[test]
pub fn test_derive_positional_filter_ok() {
    let parser = build_parser();

    let template = parser
        .parse(concat!(
            "{{ 0 | pos: \"str\", 5 }}\n",
            "{{ 0 | pos: 0 }}\n",
            "{{ 0 | pos: true, 0 }}"
        ))
        .unwrap();
    let expected = concat!(
        "<pos1: str; pos2: 5>\n",
        "<pos1: 0>\n",
        "<pos1: true; pos2: 0>"
    );

    let globals = liquid::Object::new();
    let rendered = template.render(&globals).unwrap();

    assert_eq!(rendered, expected);
}

#[test]
pub fn test_derive_positional_filter_err() {
    let parser = build_parser();

    assert!(parser.parse("{{ 0 | pos }}\n").is_err());
    assert!(parser.parse("{{ 0 | pos: 1,2,3 }}\n").is_err());
    assert!(parser.parse("{{ 0 | pos:named:4 }}\n").is_err());
    assert!(parser.parse("{{ 0 | pos:32, pos2:42 }}\n").is_err());

    let globals = liquid::Object::new();

    assert!(parser
        .parse("{{ 0 | pos: \"str\", \"str\" }}\n")
        .unwrap()
        .render(&globals)
        .is_err());
}

#[test]
pub fn test_derive_positional_filter_reflection() {
    let filter = derive_macros_test_filters::TestPositionalFilterParser;

    assert_eq!(filter.name(), "pos");
    assert_eq!(filter.description(), "Filter to test positional arguments.");
    let pos_args = filter.positional_parameters();

    assert_eq!(pos_args[0].name, "pos1");
    assert_eq!(pos_args[0].description, "First positional argument.");
    assert_eq!(pos_args[0].is_optional, false);

    assert_eq!(pos_args[1].name, "pos2");
    assert_eq!(
        pos_args[1].description,
        "Second positional argument. Must be an integer."
    );
    assert_eq!(pos_args[1].is_optional, true);

    assert!(filter.keyword_parameters().is_empty());
}

#[test]
pub fn test_derive_keyword_filter_ok() {
    let parser = build_parser();

    let template = parser
        .parse(concat!(
            "{{ 0 | kw: optional:\"str\", required: true }}\n",
            "{{ 0 | kw: required: true, optional:\"str\" }}\n",
            "{{ 0 | kw: required:false }}"
        ))
        .unwrap();
    let expected = concat!(
        "<optional: str; required: true>\n",
        "<optional: str; required: true>\n",
        "<required: false>"
    );

    let globals = liquid::Object::new();
    let rendered = template.render(&globals).unwrap();

    assert_eq!(rendered, expected);
}

#[test]
pub fn test_derive_keyword_filter_err() {
    let parser = build_parser();

    assert!(parser.parse("{{ 0 | kw }}\n").is_err());
    assert!(parser.parse("{{ 0 | kw: 1,2 }}\n").is_err());
    assert!(parser
        .parse("{{ 0 | kw: required: true, optional:\"str\", 5 }}\n")
        .is_err());

    let globals = liquid::Object::new();

    assert!(parser
        .parse("{{ 0 | kw: required:\"str\" }}\n")
        .unwrap()
        .render(&globals)
        .is_err());
}

#[test]
pub fn test_derive_keyword_filter_reflection() {
    let filter = derive_macros_test_filters::TestKeywordFilterParser;

    assert_eq!(filter.name(), "kw");
    assert_eq!(filter.description(), "Filter to test keyword arguments.");
    assert!(filter.positional_parameters().is_empty());
    let kw_args = filter.keyword_parameters();

    assert_eq!(kw_args[0].name, "optional");
    assert_eq!(kw_args[0].description, "Optional keyword argument.");
    assert_eq!(kw_args[0].is_optional, true);

    assert_eq!(kw_args[1].name, "required");
    assert_eq!(
        kw_args[1].description,
        "Required keyword argument. Must be a boolean."
    );
    assert_eq!(kw_args[1].is_optional, false);
}

#[test]
pub fn test_derive_mixed_filter_ok() {
    let parser = build_parser();

    let template = parser
        .parse(concat!(
            "{{ 0 | mix: a: 5, false, c: 4.3, \"2019-02-08 15:34:25 -0800\", \"2019-02-08\", \"str\", type: 0 }}\n",
            "{{ 0 | mix: false, \"2019-02-08 15:34:25 -0800\", \"2019-02-08\", type: 0 }}\n",
            "{{ 0 | mix: false, \"2019-02-08 15:34:25 -0800\", \"2019-02-08\", c: 4.3, a: 5, type: 0, \"str\" }}"
        ))
        .unwrap();
    let expected = concat!(
        "<a: 5; b: false; c: 4.3, d: 2019-02-08 15:34:25 -0800, e: 2019-02-08, f: str, type: 0>\n",
        "<a: None; b: false; c: None, d: 2019-02-08 15:34:25 -0800, e: 2019-02-08, f: None, type: 0>\n",
        "<a: 5; b: false; c: 4.3, d: 2019-02-08 15:34:25 -0800, e: 2019-02-08, f: str, type: 0>"
    );

    let globals = liquid::Object::new();
    let rendered = template.render(&globals).unwrap();

    assert_eq!(rendered, expected);
}

#[test]
pub fn test_derive_mixed_filter_err() {
    let parser = build_parser();

    assert!(parser.parse("{{ 0 | mix: a: 5, b: false, c: 4.3, d: \"2019-02-08 15:34:25 -0800\", e: \"str\", type: 0 }}\n").is_err());
    assert!(parser
        .parse("{{ 0 | mix: 5, false, 4.3, \"2019-02-08 15:34:25 -0800\", \"str\", 0 }}\n")
        .is_err());
    assert!(parser
        .parse("{{ 0 | mix: a: 5, false, c: 4.3, \"2019-02-08 15:34:25 -0800\", \"str\", f: 0 }}\n")
        .is_err());
}

#[test]
pub fn test_derive_mixed_filter_reflection() {
    let filter = derive_macros_test_filters::TestMixedFilterParser;

    assert_eq!(filter.name(), "mix");
    assert_eq!(filter.description(), "Mix it all together.");
    let pos_args = filter.positional_parameters();

    assert_eq!(pos_args.len(), 4);

    assert_eq!(pos_args[0].name, "b");
    assert_eq!(pos_args[0].description, "2");
    assert_eq!(pos_args[0].is_optional, false);

    assert_eq!(pos_args[1].name, "d");
    assert_eq!(pos_args[1].description, "4");
    assert_eq!(pos_args[1].is_optional, false);

    assert_eq!(pos_args[2].name, "e");
    assert_eq!(pos_args[2].description, "5");
    assert_eq!(pos_args[2].is_optional, false);

    assert_eq!(pos_args[3].name, "f");
    assert_eq!(pos_args[3].description, "6");
    assert_eq!(pos_args[3].is_optional, true);

    let kw_args = filter.keyword_parameters();

    assert_eq!(kw_args.len(), 3);

    assert_eq!(kw_args[0].name, "a");
    assert_eq!(kw_args[0].description, "1");
    assert_eq!(kw_args[0].is_optional, true);

    assert_eq!(kw_args[1].name, "c");
    assert_eq!(kw_args[1].description, "3");
    assert_eq!(kw_args[1].is_optional, true);

    assert_eq!(kw_args[2].name, "type");
    assert_eq!(kw_args[2].description, "7");
    assert_eq!(kw_args[2].is_optional, false);
}

#[test]
pub fn test_derive_parameterless_filter_ok() {
    let parser = build_parser();

    let template = parser.parse("{{ 0 | no_args }}").unwrap();
    let expected = "<>";

    let globals = liquid::Object::new();
    let rendered = template.render(&globals).unwrap();

    assert_eq!(rendered, expected);
}

#[test]
pub fn test_derive_parameterless_filter_err() {
    let parser = build_parser();

    assert!(parser.parse("{{ 0 | no_args: 1,2,3 }}\n").is_err());
    assert!(parser.parse("{{ 0 | no_args:named:4 }}\n").is_err());
    assert!(parser.parse("{{ 0 | no_args:32, pos2:42 }}\n").is_err());
}

#[test]
pub fn test_derive_parameterless_filter_reflection() {
    let filter = derive_macros_test_filters::TestParameterlessFilterParser;

    assert_eq!(filter.name(), "no_args");
    assert_eq!(filter.description(), "Filter with no arguments.");
    assert!(filter.positional_parameters().is_empty());
    assert!(filter.keyword_parameters().is_empty());
}

#[test]
pub fn test_derive_stateful_filter() {
    let globals = liquid::Object::new();

    let filter = derive_macros_test_filters::TestStatefulFilterParser::new();

    let parser = ParserBuilder::new().filter(filter).build().unwrap();
    let rendered = parser
        .parse("{{ 0 | state: \"hello\" }}")
        .unwrap()
        .render(&globals)
        .unwrap();
    assert_eq!(rendered, ":-| hello :-|");

    let mut filter = derive_macros_test_filters::TestStatefulFilterParser::new();
    filter.make_happy();

    let parser = ParserBuilder::new().filter(filter).build().unwrap();
    let rendered = parser
        .parse("{{ 0 | state: \"hello\" }}")
        .unwrap()
        .render(&globals)
        .unwrap();
    assert_eq!(rendered, ":-) hello :-)");

    let mut filter = derive_macros_test_filters::TestStatefulFilterParser::new();
    filter.make_sad();

    let parser = ParserBuilder::new().filter(filter).build().unwrap();
    let rendered = parser
        .parse("{{ 0 | state: \"hello\" }}")
        .unwrap()
        .render(&globals)
        .unwrap();
    assert_eq!(rendered, ":-( hello :-(");
}
