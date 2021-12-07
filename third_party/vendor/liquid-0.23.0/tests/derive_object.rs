use liquid::ObjectView;
use liquid::ValueView;

#[derive(ObjectView, ValueView, serde::Serialize, serde::Deserialize, Debug)]
struct TestEmpty {}

#[test]
fn test_empty_value() {
    let uut = TestEmpty {};

    assert_eq!(uut.render().to_string(), "");
    assert_eq!(uut.source().to_string(), "{}");
    assert_eq!(uut.type_name(), "object");
    assert_eq!(uut.query_state(liquid::model::State::Truthy), true);
    assert_eq!(uut.query_state(liquid::model::State::DefaultValue), true);
    assert_eq!(uut.query_state(liquid::model::State::Empty), true);
    assert_eq!(uut.query_state(liquid::model::State::Blank), true);
    assert_eq!(uut.to_kstr(), "");
    assert_eq!(uut.to_value(), liquid::model::value!({}));
    assert!(uut.as_object().is_some());
}

#[test]
fn test_empty_object() {
    let uut = TestEmpty {};

    assert_eq!(uut.size(), 0);
    assert!(uut.keys().next().is_none());
    assert!(uut.values().next().is_none());
    assert!(uut.iter().next().is_none());
    assert_eq!(uut.contains_key("non-existent"), false);
    assert!(uut.get("non-existent").is_none());
}

#[derive(ObjectView, ValueView, serde::Serialize, serde::Deserialize, Debug)]
struct TestStatic {
    boolean: bool,
    int: i64,
    float: f64,
    static_str: &'static str,
    string: String,
    kstring: kstring::KString,
    array: Vec<i64>,
}

impl TestStatic {
    fn non_default() -> Self {
        Self {
            boolean: true,
            int: 5,
            float: 4.2,
            static_str: "Hello world",
            string: String::from("Goodbye world"),
            kstring: kstring::KString::from_static("foo"),
            array: vec![1, 2, 3],
        }
    }
}

#[test]
fn test_static_value() {
    let uut = TestStatic::non_default();

    assert_ne!(uut.render().to_string(), "");
    assert_ne!(uut.source().to_string(), "{}");
    assert_eq!(uut.type_name(), "object");
    assert_eq!(uut.query_state(liquid::model::State::Truthy), true);
    assert_eq!(uut.query_state(liquid::model::State::DefaultValue), false);
    assert_eq!(uut.query_state(liquid::model::State::Empty), false);
    assert_eq!(uut.query_state(liquid::model::State::Blank), false);
    assert_ne!(uut.to_kstr(), "");
    assert_ne!(uut.to_value(), liquid::model::value!({}));
    assert!(uut.as_object().is_some());
}

#[test]
fn test_static_object() {
    let uut = TestStatic::non_default();

    assert_eq!(uut.size(), 7i64);
    assert!(uut.keys().next().is_some());
    assert!(uut.values().next().is_some());
    assert!(uut.iter().next().is_some());
    assert_eq!(uut.contains_key("non-existent"), false);
    assert_eq!(uut.contains_key("boolean"), true);
    assert!(uut.get("boolean").is_some());
}

#[derive(ObjectView, ValueView, serde::Serialize, serde::Deserialize, Debug)]
struct TestBorrow<'s> {
    s: &'s str,
}

#[test]
fn test_borrow_value() {
    let fixture = String::from("foo");
    let uut = TestBorrow {
        s: fixture.as_str(),
    };

    assert!(uut.as_object().is_some());
}

#[test]
fn test_borrow_object() {
    let fixture = String::from("foo");
    let uut = TestBorrow {
        s: fixture.as_str(),
    };

    assert_eq!(uut.size(), 1i64);
    assert!(uut.keys().next().is_some());
    assert!(uut.values().next().is_some());
    assert!(uut.iter().next().is_some());
    assert_eq!(uut.contains_key("non-existent"), false);
    assert_eq!(uut.contains_key("s"), true);
    assert!(uut.get("s").is_some());
}
