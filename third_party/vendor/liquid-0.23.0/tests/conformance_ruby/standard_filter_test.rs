use crate::test_helper::*;

#[test]
fn test_size() {
    assert_eq!(
        v!(3),
        call_filter!(liquid_lib::stdlib::Size, v!([1, 2, 3])).unwrap()
    );
    assert_eq!(
        v!(0),
        call_filter!(liquid_lib::stdlib::Size, v!([])).unwrap()
    );
    assert_eq!(
        v!(0),
        call_filter!(liquid_lib::stdlib::Size, v!(nil)).unwrap()
    );
}

#[test]
fn test_downcase() {
    assert_eq!(
        v!("testing"),
        call_filter!(liquid_lib::stdlib::Downcase, v!("Testing")).unwrap()
    );
    assert_eq!(
        v!(""),
        call_filter!(liquid_lib::stdlib::Downcase, Nil).unwrap()
    );
}

#[test]
fn test_upcase() {
    assert_eq!(
        v!("TESTING"),
        call_filter!(liquid_lib::stdlib::Upcase, v!("Testing")).unwrap()
    );
    assert_eq!(
        v!(""),
        call_filter!(liquid_lib::stdlib::Upcase, Nil).unwrap()
    );
}

#[test]
#[should_panic] // liquid-rust#261
fn test_slice() {
    assert_eq!(
        v!("oob"),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!(1), v!(3)).unwrap()
    );
    assert_eq!(
        v!("oobar"),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!(1), v!(1000)).unwrap()
    );
    assert_eq!(
        v!(""),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!(1), v!(0)).unwrap()
    );
    assert_eq!(
        v!("o"),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!(1), v!(1)).unwrap()
    );
    assert_eq!(
        v!("bar"),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!(3), v!(3)).unwrap()
    );
    assert_eq!(
        v!("ar"),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!(-2), v!(2)).unwrap()
    );
    assert_eq!(
        v!("ar"),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!(-2), v!(1000)).unwrap()
    );
    assert_eq!(
        v!("r"),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!(-1)).unwrap()
    );
    assert_eq!(
        v!(""),
        call_filter!(liquid_lib::stdlib::Slice, Nil, v!(0)).unwrap()
    );
    assert_eq!(
        v!(""),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!(100), v!(10)).unwrap()
    );
    assert_eq!(
        v!(""),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!(-100), v!(10)).unwrap()
    );
    assert_eq!(
        v!("oob"),
        call_filter!(liquid_lib::stdlib::Slice, v!("foobar"), v!("1"), v!("3")).unwrap()
    );
    liquid_core::call_filter!(liquid_lib::stdlib::Slice, "foobar", Nil).unwrap_err();
    liquid_core::call_filter!(liquid_lib::stdlib::Slice, "foobar", 0, "").unwrap_err();
}

#[test]
#[should_panic] // liquid-rust#261
fn test_slice_on_arrays() {
    let input = v!(["f", "o", "o", "b", "a", "r"]);
    assert_eq!(
        v!(["o", "o", "b"]),
        call_filter!(liquid_lib::stdlib::Slice, input, v!(1), v!(3)).unwrap()
    );
    assert_eq!(
        v!(["o", "o", "b", "a", "r"]),
        call_filter!(liquid_lib::stdlib::Slice, input, v!(1), v!(1000)).unwrap()
    );
    assert_eq!(
        v!([]),
        call_filter!(liquid_lib::stdlib::Slice, input, v!(1), v!(0)).unwrap()
    );
    assert_eq!(
        v!(["o"]),
        call_filter!(liquid_lib::stdlib::Slice, input, v!(1), v!(1)).unwrap()
    );
    assert_eq!(
        v!(["b", "a", "r"]),
        call_filter!(liquid_lib::stdlib::Slice, input, v!(3), v!(3)).unwrap()
    );
    assert_eq!(
        v!(["a", "r"]),
        call_filter!(liquid_lib::stdlib::Slice, input, v!(-2), v!(2)).unwrap()
    );
    assert_eq!(
        v!(["a", "r"]),
        call_filter!(liquid_lib::stdlib::Slice, input, v!(-2), v!(1000)).unwrap()
    );
    assert_eq!(
        v!(["r"]),
        call_filter!(liquid_lib::stdlib::Slice, input, v!(-1)).unwrap()
    );
    assert_eq!(
        v!([]),
        call_filter!(liquid_lib::stdlib::Slice, input, v!(100), v!(10)).unwrap()
    );
    assert_eq!(
        v!([]),
        call_filter!(liquid_lib::stdlib::Slice, input, v!(-100), v!(10)).unwrap()
    );
}

#[test]
fn test_truncate() {
    assert_eq!(
        v!("1234..."),
        call_filter!(liquid_lib::stdlib::Truncate, v!("1234567890"), v!(7)).unwrap()
    );
    assert_eq!(
        v!("1234567890"),
        call_filter!(liquid_lib::stdlib::Truncate, v!("1234567890"), v!(20)).unwrap()
    );
    assert_eq!(
        v!("..."),
        call_filter!(liquid_lib::stdlib::Truncate, v!("1234567890"), v!(0)).unwrap()
    );
    assert_eq!(
        v!("1234567890"),
        call_filter!(liquid_lib::stdlib::Truncate, v!("1234567890")).unwrap()
    );
    assert_eq!(
        v!("测试..."),
        call_filter!(liquid_lib::stdlib::Truncate, v!("测试测试测试测试"), v!(5)).unwrap()
    );
    assert_eq!(
        v!("12341"),
        call_filter!(liquid_lib::stdlib::Truncate, v!("1234567890"), v!(5), v!(1)).unwrap()
    );
}

#[test]
fn test_split() {
    assert_eq!(
        v!(["12", "34"]),
        call_filter!(liquid_lib::stdlib::Split, v!("12~34"), v!("~")).unwrap()
    );
    assert_eq!(
        v!(["A? ", " ,Z"]),
        call_filter!(liquid_lib::stdlib::Split, v!("A? ~ ~ ~ ,Z"), v!("~ ~ ~")).unwrap()
    );
    assert_eq!(
        v!(["A?Z"]),
        call_filter!(liquid_lib::stdlib::Split, v!("A?Z"), v!("~")).unwrap()
    );
    assert_eq!(
        v!([]),
        call_filter!(liquid_lib::stdlib::Split, Nil, v!(" ")).unwrap()
    );
    assert_eq!(
        v!(["A", "Z"]),
        call_filter!(liquid_lib::stdlib::Split, v!("A1Z"), v!(1)).unwrap()
    );
}

#[test]
fn test_escape() {
    assert_eq!(
        v!("&lt;strong&gt;"),
        call_filter!(liquid_lib::stdlib::Escape, v!("<strong>")).unwrap()
    );
    assert_eq!(
        v!("1"),
        call_filter!(liquid_lib::stdlib::Escape, v!(1)).unwrap()
    );
    assert_eq!(
        v!("2001-02-03"),
        call_filter!(liquid_lib::stdlib::Escape, date(2001, 2, 3)).unwrap()
    );
    assert_eq!(Nil, call_filter!(liquid_lib::stdlib::Escape, Nil).unwrap());
}

#[test]
#[should_panic] // liquid-rust#269
fn test_h() {
    panic!("Implement this filter");
    /*
    assert_eq!(v!("&lt;strong&gt;"), call_filter!(liquid_lib::stdlib::h, v!("<strong>")));
    assert_eq!(v!("1"), call_filter!(liquid_lib::stdlib::h, 1));
    assert_eq!(v!("2001-02-03"), call_filter!(liquid_lib::stdlib::h, date(2001, 2, 3)));
    assert_eq!(Nil, call_filter!(liquid_lib::stdlib::h, Nil));
    */
}

#[test]
fn test_escape_once() {
    assert_eq!(
        v!("&lt;strong&gt;Hulk&lt;/strong&gt;"),
        call_filter!(
            liquid_lib::stdlib::EscapeOnce,
            v!("&lt;strong&gt;Hulk</strong>")
        )
        .unwrap()
    );
}

#[test]
fn test_url_encode() {
    assert_eq!(
        v!("foo%2B1%40example.com"),
        call_filter!(liquid_lib::stdlib::UrlEncode, v!("foo+1@example.com")).unwrap()
    );
    assert_eq!(
        v!("1"),
        call_filter!(liquid_lib::stdlib::UrlEncode, v!(1)).unwrap()
    );
    assert_eq!(
        v!("2001-02-03"),
        call_filter!(liquid_lib::stdlib::UrlEncode, date(2001, 2, 3)).unwrap()
    );
    assert_eq!(
        Nil,
        call_filter!(liquid_lib::stdlib::UrlEncode, Nil).unwrap()
    );
}

#[test]
fn test_url_decode() {
    assert_eq!(
        v!("foo bar"),
        call_filter!(liquid_lib::stdlib::UrlDecode, v!("foo+bar")).unwrap()
    );
    assert_eq!(
        v!("foo bar"),
        call_filter!(liquid_lib::stdlib::UrlDecode, v!("foo%20bar")).unwrap()
    );
    assert_eq!(
        v!("foo+1@example.com"),
        call_filter!(liquid_lib::stdlib::UrlDecode, v!("foo%2B1%40example.com")).unwrap()
    );
    assert_eq!(
        v!("1"),
        call_filter!(liquid_lib::stdlib::UrlDecode, v!(1)).unwrap()
    );
    assert_eq!(
        v!("2001-02-03"),
        call_filter!(liquid_lib::stdlib::UrlDecode, date(2001, 2, 3)).unwrap()
    );
    assert_eq!(
        Nil,
        call_filter!(liquid_lib::stdlib::UrlDecode, Nil).unwrap()
    );
}

#[test]
fn test_truncatewords() {
    assert_eq!(
        v!("one two three"),
        call_filter!(
            liquid_lib::stdlib::TruncateWords,
            v!("one two three"),
            v!(4)
        )
        .unwrap()
    );
    assert_eq!(
        v!("one two..."),
        call_filter!(
            liquid_lib::stdlib::TruncateWords,
            v!("one two three"),
            v!(2)
        )
        .unwrap()
    );
    assert_eq!(
        v!("one two three"),
        call_filter!(liquid_lib::stdlib::TruncateWords, v!("one two three")).unwrap()
    );
    assert_eq!(v!("Two small (13&#8221; x 5.5&#8221; x 10&#8221; high) baskets fit inside one large basket (13&#8221;..."), call_filter!(liquid_lib::stdlib::TruncateWords, v!("Two small (13&#8221; x 5.5&#8221; x 10&#8221; high) baskets fit inside one large basket (13&#8221; x 16&#8221; x 10.5&#8221; high) with cover."), v!(15)).unwrap());
    assert_eq!(
        v!("测试测试测试测试"),
        call_filter!(
            liquid_lib::stdlib::TruncateWords,
            v!("测试测试测试测试"),
            v!(5)
        )
        .unwrap()
    );
    assert_eq!(
        v!("one two1"),
        call_filter!(
            liquid_lib::stdlib::TruncateWords,
            v!("one two three"),
            v!(2),
            v!(1)
        )
        .unwrap()
    );
}

#[test]
fn test_strip_html() {
    assert_eq!(
        v!("test"),
        call_filter!(liquid_lib::stdlib::StripHtml, v!(r#"<div>test</div>"#)).unwrap()
    );
    assert_eq!(
        v!("test"),
        call_filter!(
            liquid_lib::stdlib::StripHtml,
            v!(r#"<div id="test">test</div>"#)
        )
        .unwrap()
    );
    assert_eq!(
        v!(""),
        call_filter!(
            liquid_lib::stdlib::StripHtml,
            v!(r#"<script type="text/javascript">document.write"some stuff";</script>"#)
        )
        .unwrap()
    );
    assert_eq!(
        v!(""),
        call_filter!(
            liquid_lib::stdlib::StripHtml,
            v!(r#"<style type="text/css">foo bar</style>"#)
        )
        .unwrap()
    );
    assert_eq!(
        v!("test"),
        call_filter!(
            liquid_lib::stdlib::StripHtml,
            v!(r#"<div\nclass="multiline">test</div>"#)
        )
        .unwrap()
    );
    assert_eq!(
        v!("test"),
        call_filter!(
            liquid_lib::stdlib::StripHtml,
            v!(r#"<!-- foo bar \n test -->test"#)
        )
        .unwrap()
    );
    assert_eq!(
        v!(""),
        call_filter!(liquid_lib::stdlib::StripHtml, Nil).unwrap()
    );
}

#[test]
fn test_join() {
    assert_eq!(
        v!("1 2 3 4"),
        call_filter!(liquid_lib::stdlib::Join, v!([1, 2, 3, 4])).unwrap()
    );
    assert_eq!(
        v!("1 - 2 - 3 - 4"),
        call_filter!(liquid_lib::stdlib::Join, v!([1, 2, 3, 4]), v!(" - ")).unwrap()
    );
    assert_eq!(
        v!("1121314"),
        call_filter!(liquid_lib::stdlib::Join, v!([1, 2, 3, 4]), v!(1)).unwrap()
    );
}

#[test]
fn test_sort() {
    assert_eq!(
        v!([1, 2, 3, 4]),
        call_filter!(liquid_lib::stdlib::Sort, v!([4, 3, 2, 1])).unwrap()
    );
    assert_eq!(
        v!([{ "a": 1 }, { "a": 2 }, { "a": 3 }, { "a": 4 }]),
        call_filter!(
            liquid_lib::stdlib::Sort,
            v!([{ "a": 4 }, { "a": 3 }, { "a": 1 }, { "a": 2 }]),
            "a"
        )
        .unwrap()
    );
}

#[test]
fn test_sort_with_nils() {
    assert_eq!(
        v!([1, 2, 3, 4, nil]),
        call_filter!(liquid_lib::stdlib::Sort, v!([nil, 4, 3, 2, 1])).unwrap()
    );
    assert_eq!(
        v!([{ "a": 1 }, { "a": 2 }, { "a": 3 }, { "a": 4 }, {}]),
        call_filter!(
            liquid_lib::stdlib::Sort,
            v!([{ "a": 4 }, { "a": 3 }, {}, { "a": 1 }, { "a": 2 }]),
            "a"
        )
        .unwrap()
    );
}

#[test]
fn test_sort_when_property_is_sometimes_missing_puts_nils_last() {
    let input = v!([
      { "price": 4, "handle": "alpha" },
      { "handle": "beta" },
      { "price": 1, "handle": "gamma" },
      { "handle": "delta" },
      { "price": 2, "handle": "epsilon" }
    ]);
    let expectation_start = vec![
        v!({ "price": 1, "handle": "gamma" }),
        v!({ "price": 2, "handle": "epsilon" }),
        v!({ "price": 4, "handle": "alpha" }),
    ];
    // Those two results are viable, since both values "map" to nil.
    // Since the sorting is unstable, the order between the results is undefined.
    // The original test (Ruby implementation) tests for only one of the results,
    // which, I think, was the one produced by their specific implementation.
    let expectation_end = (
        vec![v!({ "handle": "delta" }), v!({ "handle": "beta" })],
        vec![v!({ "handle": "beta" }), v!({ "handle": "delta" })],
    );
    let result = call_filter!(liquid_lib::stdlib::Sort, input, v!("price")).unwrap();
    let result = result.into_array();
    assert!(result.is_some());
    let result = result.unwrap();
    assert_eq!(expectation_start, &result[..3]);
    assert!(expectation_end.0 == &result[3..] || expectation_end.1 == &result[3..]);
}

#[test]
fn test_sort_natural() {
    assert_eq!(
        v!(["a", "B", "c", "D"]),
        call_filter!(liquid_lib::stdlib::SortNatural, v!(["c", "D", "a", "B"])).unwrap()
    );
    assert_eq!(
        v!([{ "a": "a" }, { "a": "B" }, { "a": "c" }, { "a": "D" }]),
        call_filter!(
            liquid_lib::stdlib::SortNatural,
            v!([{ "a": "D" }, { "a": "c" }, { "a": "a" }, { "a": "B" }]),
            "a"
        )
        .unwrap()
    );
}

#[test]
fn test_sort_natural_with_nils() {
    assert_eq!(
        v!(["a", "B", "c", "D", nil]),
        call_filter!(
            liquid_lib::stdlib::SortNatural,
            v!([nil, "c", "D", "a", "B"])
        )
        .unwrap()
    );
    assert_eq!(
        v!([{ "a": "a" }, { "a": "B" }, { "a": "c" }, { "a": "D" }, {}]),
        call_filter!(
            liquid_lib::stdlib::SortNatural,
            v!([{ "a": "D" }, { "a": "c" }, {}, { "a": "a" }, { "a": "B" }]),
            "a"
        )
        .unwrap()
    );
}

#[test]
fn test_sort_natural_when_property_is_sometimes_missing_puts_nils_last() {
    let input = v!([
      { "price": "4", "handle": "alpha" },
      { "handle": "beta" },
      { "price": "1", "handle": "gamma" },
      { "handle": "delta" },
      { "price": 2, "handle": "epsilon" }
    ]);
    let expectation_start = vec![
        v!({ "price": "1", "handle": "gamma" }),
        v!({ "price": 2, "handle": "epsilon" }),
        v!({ "price": "4", "handle": "alpha" }),
    ];
    // Those two results are viable, since both values "map" to nil.
    // Since the sorting is unstable, the order between the results is undefined.
    // The original test (Ruby implementation) tests for only one of the results,
    // which, I think, was the one produced by their specific implementation.
    let expectation_end = (
        vec![v!({ "handle": "delta" }), v!({ "handle": "beta" })],
        vec![v!({ "handle": "beta" }), v!({ "handle": "delta" })],
    );
    let result = call_filter!(liquid_lib::stdlib::SortNatural, input, v!("price")).unwrap();
    let result = result.into_array();
    assert!(result.is_some());
    let result = result.unwrap();
    assert_eq!(expectation_start, &result[..3]);
    assert!(expectation_end.0 == &result[3..] || expectation_end.1 == &result[3..]);
}

#[test]
fn test_sort_natural_case_check() {
    let input = v!([
      { "key": "X" },
      { "key": "Y" },
      { "key": "Z" },
      { "fake": "t" },
      { "key": "a" },
      { "key": "b" },
      { "key": "c" }
    ]);
    let expectation = v!([
      { "key": "a" },
      { "key": "b" },
      { "key": "c" },
      { "key": "X" },
      { "key": "Y" },
      { "key": "Z" },
      { "fake": "t" }
    ]);
    assert_eq!(
        expectation,
        call_filter!(liquid_lib::stdlib::SortNatural, input, "key").unwrap()
    );
    assert_eq!(
        v!(["a", "b", "c", "X", "Y", "Z"]),
        call_filter!(
            liquid_lib::stdlib::SortNatural,
            v!(["X", "Y", "Z", "a", "b", "c"])
        )
        .unwrap()
    );
}

#[test]
fn test_sort_empty_array() {
    assert_eq!(
        v!([]),
        call_filter!(liquid_lib::stdlib::Sort, v!([]), v!("a")).unwrap()
    );
}

#[test]
fn test_sort_natural_empty_array() {
    assert_eq!(
        v!([]),
        call_filter!(liquid_lib::stdlib::SortNatural, v!([]), v!("a")).unwrap()
    );
}

#[test]
fn test_legacy_sort_hash() {
    assert_eq!(
        v!([{ "a": 1, "b": 2 }]),
        call_filter!(liquid_lib::stdlib::Sort, v!({ "a": 1, "b": 2 })).unwrap()
    );
}

#[test]
fn test_numerical_vs_lexicographical_sort() {
    assert_eq!(
        v!([2, 10]),
        call_filter!(liquid_lib::stdlib::Sort, v!([10, 2])).unwrap()
    );
    assert_eq!(
        v!([{ "a": 2 }, { "a": 10 }]),
        call_filter!(liquid_lib::stdlib::Sort, v!([{ "a": 10 }, { "a": 2 }]), "a").unwrap()
    );
    assert_eq!(
        v!(["10", "2"]),
        call_filter!(liquid_lib::stdlib::Sort, v!(["10", "2"])).unwrap()
    );
    assert_eq!(
        v!([{ "a": "10" }, { "a": "2" }]),
        call_filter!(
            liquid_lib::stdlib::Sort,
            v!([{ "a": "10" }, { "a": "2" }]),
            "a"
        )
        .unwrap()
    );
}

#[test]
#[should_panic] // liquid-rust#266
fn test_uniq() {
    assert_eq!(
        v!(["foo"]),
        call_filter!(liquid_lib::stdlib::Uniq, v!("foo")).unwrap()
    );
    assert_eq!(
        v!([1, 3, 2, 4]),
        call_filter!(liquid_lib::stdlib::Uniq, v!([1, 1, 3, 2, 3, 1, 4, 3, 2, 1])).unwrap()
    );
    assert_eq!(
        v!([{ "a": 1 }, { "a": 3 }, { "a": 2 }]),
        call_filter!(
            liquid_lib::stdlib::Uniq,
            v!([{ "a": 1 }, { "a": 3 }, { "a": 1 }, { "a": 2 }]),
            "a"
        )
        .unwrap()
    );
    //testdrop: Implementation specific: Drops
}

#[test]
#[should_panic] // liquid-rust#267
fn test_uniq_empty_array() {
    assert_eq!(
        v!([]),
        call_filter!(liquid_lib::stdlib::Uniq, v!([]), v!("a")).unwrap()
    );
}

#[test]
fn test_compact_empty_array() {
    assert_eq!(
        v!([]),
        call_filter!(liquid_lib::stdlib::Compact, v!([]), v!("a")).unwrap()
    );
}

#[test]
fn test_compact_invalid_property() {
    let input = v!([[1], [2], [3]]);

    liquid_core::call_filter!(liquid_lib::stdlib::Compact, input, "bar").unwrap_err();
}

#[test]
fn test_reverse() {
    assert_eq!(
        v!([4, 3, 2, 1]),
        call_filter!(liquid_lib::stdlib::Reverse, v!([1, 2, 3, 4])).unwrap()
    );
}

#[test]
#[should_panic] // liquid-rust#256
fn test_legacy_reverse_hash() {
    assert_eq!(
        v!([{ "a": 1, "b": 2 }]),
        call_filter!(liquid_lib::stdlib::Reverse, v!({"a": 1, "b": 2})).unwrap()
    );
}

#[test]
fn test_map() {
    assert_eq!(
        v!([1, 2, 3, 4]),
        call_filter!(
            liquid_lib::stdlib::Map,
            v!([{ "a": 1 }, { "a": 2 }, { "a": 3 }, { "a": 4 }]),
            "a"
        )
        .unwrap()
    );
    assert_template_result!(
        "abc",
        r#"{{ ary | map:"foo" | map:"bar" }}"#,
        o!({"ary": [{ "foo": { "bar": "a" } }, { "foo": { "bar": "b" } }, { "foo": { "bar": "c" } }]}),
    );
}

#[test]
#[should_panic]
fn test_map_doesnt_call_arbitrary_stuff() {
    panic!("Implementation specific: filters can't access arbitrary variables");
}

#[test]
#[should_panic]
fn test_map_calls_to_liquid() {
    panic!("Implementation specific: to_liquid");
}

#[test]
#[should_panic] // liquid-rust#255
fn test_map_on_hashes() {
    assert_template_result!(
        "4217",
        r#"{{ thing | map: "foo" | map: "bar" }}"#,
        o!({"thing": { "foo": [ { "bar": 42 }, { "bar": 17 } ] }}),
    );
}

#[test]
#[should_panic] // liquid-rust#255
fn test_legacy_map_on_hashes_with_dynamic_key() {
    let template = r#"{% assign key = "foo" %}{{ thing | map: key | map: "bar" }}"#;
    let hash = o!({ "foo": { "bar": 42 } });
    assert_template_result!("42", template, o!({ "thing": hash }));
}

#[test]
#[should_panic]
fn test_sort_calls_to_liquid() {
    panic!("Implementation specific: to_liquid");
}

#[test]
#[should_panic]
fn test_map_over_proc() {
    panic!("Implementation specific: proc");
}

#[test]
#[should_panic]
fn test_map_over_drops_returning_procs() {
    panic!("Implementation specific: proc / drops");
}

#[test]
#[should_panic]
fn test_map_works_on_enumerables() {
    panic!("Implementation specific: drops");
}

#[test]
#[should_panic]
fn test_sort_works_on_enumerables() {
    panic!("Implementation specific: drops");
}

#[test]
#[should_panic]
fn test_first_and_last_call_to_liquid() {
    panic!("Implementation specific: to_liquid");
}

#[test]
#[should_panic]
fn test_truncate_calls_to_liquid() {
    panic!("Implementation specific: to_liquid");
}

#[test]
#[should_panic] // liquid-rust#252
fn test_date() {
    assert_eq!(
        v!("May"),
        call_filter!(
            liquid_lib::stdlib::Date,
            with_time("2006-05-05 10:00:00"),
            "%B"
        )
        .unwrap()
    );
    assert_eq!(
        v!("June"),
        call_filter!(
            liquid_lib::stdlib::Date,
            with_time("2006-06-05 10:00:00"),
            "%B"
        )
        .unwrap()
    );
    assert_eq!(
        v!("July"),
        call_filter!(
            liquid_lib::stdlib::Date,
            with_time("2006-07-05 10:00:00"),
            "%B"
        )
        .unwrap()
    );

    assert_eq!(
        v!("May"),
        call_filter!(liquid_lib::stdlib::Date, "2006-05-05 10:00:00", "%B").unwrap()
    );
    assert_eq!(
        v!("June"),
        call_filter!(liquid_lib::stdlib::Date, "2006-06-05 10:00:00", "%B").unwrap()
    );
    assert_eq!(
        v!("July"),
        call_filter!(liquid_lib::stdlib::Date, "2006-07-05 10:00:00", "%B").unwrap()
    );

    assert_eq!(
        v!("2006-07-05 10:00:00"),
        call_filter!(liquid_lib::stdlib::Date, "2006-07-05 10:00:00", "").unwrap()
    );
    assert_eq!(
        v!("2006-07-05 10:00:00"),
        call_filter!(liquid_lib::stdlib::Date, "2006-07-05 10:00:00", "").unwrap()
    );
    assert_eq!(
        v!("2006-07-05 10:00:00"),
        call_filter!(liquid_lib::stdlib::Date, "2006-07-05 10:00:00", "").unwrap()
    );
    assert_eq!(
        v!("2006-07-05 10:00:00"),
        call_filter!(liquid_lib::stdlib::Date, "2006-07-05 10:00:00", Nil).unwrap()
    );

    assert_eq!(
        v!("07/05/2006"),
        call_filter!(liquid_lib::stdlib::Date, "2006-07-05 10:00:00", "%m/%d/%Y").unwrap()
    );

    assert_eq!(
        v!("07/16/2004"),
        call_filter!(
            liquid_lib::stdlib::Date,
            "Fri Jul 16 01:00:00 2004",
            "%m/%d/%Y"
        )
        .unwrap()
    );
    assert_eq!(
        v!("#{Date.today.year}"),
        call_filter!(liquid_lib::stdlib::Date, "now", "%Y").unwrap()
    );
    assert_eq!(
        v!("#{Date.today.year}"),
        call_filter!(liquid_lib::stdlib::Date, "today", "%Y").unwrap()
    );
    assert_eq!(
        v!("#{Date.today.year}"),
        call_filter!(liquid_lib::stdlib::Date, "Today", "%Y").unwrap()
    );

    assert_eq!(
        Nil,
        call_filter!(liquid_lib::stdlib::Date, Nil, "%B").unwrap()
    );

    assert_eq!(
        v!(""),
        call_filter!(liquid_lib::stdlib::Date, "", "%B").unwrap()
    );

    // Limited in value because we can't change the timezone
    assert_eq!(
        v!("07/05/2006"),
        call_filter!(liquid_lib::stdlib::Date, 1152098955, "%m/%d/%Y").unwrap()
    );
    assert_eq!(
        v!("07/05/2006"),
        call_filter!(liquid_lib::stdlib::Date, "1152098955", "%m/%d/%Y").unwrap()
    );
}

#[test]
fn test_first_last() {
    assert_eq!(
        v!(1),
        call_filter!(liquid_lib::stdlib::First, v!([1, 2, 3])).unwrap()
    );
    assert_eq!(
        v!(3),
        call_filter!(liquid_lib::stdlib::Last, v!([1, 2, 3])).unwrap()
    );
    assert_eq!(
        Nil,
        call_filter!(liquid_lib::stdlib::First, v!([])).unwrap()
    );
    assert_eq!(Nil, call_filter!(liquid_lib::stdlib::Last, v!([])).unwrap());
}

#[test]
fn test_replace() {
    assert_eq!(
        v!("2 2 2 2"),
        call_filter!(liquid_lib::stdlib::Replace, v!("1 1 1 1"), v!("1"), v!(2)).unwrap()
    );
    assert_eq!(
        v!("2 2 2 2"),
        call_filter!(liquid_lib::stdlib::Replace, v!("1 1 1 1"), v!(1), v!(2)).unwrap()
    );
    assert_eq!(
        v!("2 1 1 1"),
        call_filter!(
            liquid_lib::stdlib::ReplaceFirst,
            v!("1 1 1 1"),
            v!("1"),
            v!(2)
        )
        .unwrap()
    );
    assert_eq!(
        v!("2 1 1 1"),
        call_filter!(
            liquid_lib::stdlib::ReplaceFirst,
            v!("1 1 1 1"),
            v!(1),
            v!(2)
        )
        .unwrap()
    );
    assert_template_result!(
        "2 1 1 1",
        r#"{{ "1 1 1 1" | replace_first: "1", 2 }}"#,
        o!({}),
    );
}

#[test]
fn test_remove() {
    assert_eq!(
        v!("   "),
        call_filter!(liquid_lib::stdlib::Remove, v!("a a a a"), v!("a")).unwrap()
    );
    assert_eq!(
        v!("   "),
        call_filter!(liquid_lib::stdlib::Remove, v!("1 1 1 1"), v!(1)).unwrap()
    );
    assert_eq!(
        v!("a a a"),
        call_filter!(liquid_lib::stdlib::RemoveFirst, v!("a a a a"), v!("a ")).unwrap()
    );
    assert_eq!(
        v!(" 1 1 1"),
        call_filter!(liquid_lib::stdlib::RemoveFirst, v!("1 1 1 1"), v!(1)).unwrap()
    );
    assert_template_result!("a a a", r#"{{ "a a a a" | remove_first: "a " }}"#);
}

#[test]
fn test_pipes_in_string_arguments() {
    assert_template_result!("foobar", r#"{{ "foo|bar" | remove: "|" }}"#);
}

#[test]
fn test_strip() {
    assert_template_result!("ab c", "{{ source | strip }}", o!({"source": " ab c  "}));
    assert_template_result!(
        "ab c",
        "{{ source | strip }}",
        o!({"source": " \tab c  \n \t"}),
    );
}

#[test]
fn test_lstrip() {
    assert_template_result!("ab c  ", "{{ source | lstrip }}", o!({"source": " ab c  "}));
    assert_template_result!(
        "ab c  \n \t",
        "{{ source | lstrip }}",
        o!({"source": " \tab c  \n \t"}),
    );
}

#[test]
fn test_rstrip() {
    assert_template_result!(" ab c", "{{ source | rstrip }}", o!({"source": " ab c  "}));
    assert_template_result!(
        " \tab c",
        "{{ source | rstrip }}",
        o!({"source": " \tab c  \n \t"}),
    );
}

#[test]
fn test_strip_newlines() {
    assert_template_result!(
        "abc",
        "{{ source | strip_newlines }}",
        o!({"source": "a\nb\nc"}),
    );
    assert_template_result!(
        "abc",
        "{{ source | strip_newlines }}",
        o!({"source": "a\r\nb\nc"}),
    );
}

#[test]
fn test_newlines_to_br() {
    assert_template_result!(
        "a<br />\nb<br />\nc",
        "{{ source | newline_to_br }}",
        o!({"source": "a\nb\nc"}),
    );
}

#[test]
#[should_panic] // liquid-rust#260
fn test_plus() {
    assert_template_result!("2", r#"{{ 1 | plus:1 }}"#);
    assert_template_result!("2.0", r#"{{ "1" | plus:"1.0" }}"#);

    // Implementation specific: use of drops
}

#[test]
fn test_minus() {
    assert_template_result!(
        "4",
        r#"{{ input | minus:operand }}"#,
        o!({"input": 5, "operand": 1}),
    );
    assert_template_result!("2.3", r#"{{ "4.3" | minus:"2" }}"#);

    // Implementation specific: use of drops
}

#[test]
fn test_abs() {
    assert_template_result!("17", r#"{{ 17 | abs }}"#);
    assert_template_result!("17", r#"{{ -17 | abs }}"#);
    assert_template_result!("17", r#"{{ "17" | abs }}"#);
    assert_template_result!("17", r#"{{ "-17" | abs }}"#);
    assert_template_result!("0", r#"{{ 0 | abs }}"#);
    assert_template_result!("0", r#"{{ "0" | abs }}"#);
    assert_template_result!("17.42", r#"{{ 17.42 | abs }}"#);
    assert_template_result!("17.42", r#"{{ -17.42 | abs }}"#);
    assert_template_result!("17.42", r#"{{ "17.42" | abs }}"#);
    assert_template_result!("17.42", r#"{{ "-17.42" | abs }}"#);
}

#[test]
#[should_panic] // liquid-rust#265
fn test_times() {
    assert_template_result!("12", r#"{{ 3 | times:4 }}"#);
    assert_template_result!("0", r#"{{ "foo" | times:4 }}"#);
    assert_template_result!(
        "6",
        r#"{{ "2.1" | times:3 | replace: ".","-" | plus:0}}"#,
        o!({}),
    );
    assert_template_result!("7.25", r#"{{ 0.0725 | times:100 }}"#);
    assert_template_result!("-7.25", r#"{{ "-0.0725" | times:100 }}"#);
    assert_template_result!("7.25", r#"{{ "-0.0725" | times: -100 }}"#);
    // Implementation specific: use of drops
}

#[test]
fn test_divided_by() {
    assert_template_result!("4", r#"{{ 12 | divided_by:3 }}"#);
    assert_template_result!("4", r#"{{ 14 | divided_by:3 }}"#);

    assert_template_result!("5", r#"{{ 15 | divided_by:3 }}"#);
    assert_render_error!("{{ 5 | divided_by:0 }}");

    assert_template_result!("0.5", r#"{{ 2.0 | divided_by:4 }}"#);
    assert_render_error!("{{ 1 | modulo:0 }}");

    // Implementation specific: use of drops
}

#[test]
fn test_modulo() {
    assert_template_result!("1", r#"{{ 3 | modulo:2 }}"#);
    assert_render_error!("{{ 1 | modulo:0 }}");

    // Implementation specific: use of drops
}

#[test]
fn test_round() {
    assert_template_result!("5", r#"{{ input | round }}"#, o!({"input": 4.6}));
    assert_template_result!("4", r#"{{ "4.3" | round }}"#);
    assert_template_result!("4.56", r#"{{ input | round: 2 }}"#, o!({"input": 4.5612}));
    assert_render_error!("{{ 1.0 | divided_by: 0.0 | round }}");

    // Implementation specific: use of drops
}

#[test]
fn test_ceil() {
    assert_template_result!("5", r#"{{ input | ceil }}"#, o!({"input": 4.6}));
    assert_template_result!("5", r#"{{ "4.3" | ceil }}"#);
    assert_render_error!("{{ 1.0 | divided_by: 0.0 | ceil }}");

    // Implementation specific: use of drops
}

#[test]
fn test_floor() {
    assert_template_result!("4", r#"{{ input | floor }}"#, o!({"input": 4.6}));
    assert_template_result!("4", r#"{{ "4.3" | floor }}"#);
    assert_render_error!("{{ 1.0 | divided_by: 0.0 | floor }}");

    // Implementation specific: use of drops
}

#[test]
fn test_at_most() {
    assert_template_result!("4", r#"{{ 5 | at_most:4 }}"#);
    assert_template_result!("5", r#"{{ 5 | at_most:5 }}"#);
    assert_template_result!("5", r#"{{ 5 | at_most:6 }}"#);

    assert_template_result!("4.5", r#"{{ 4.5 | at_most:5 }}"#);
    // Implementation specific: use of drops
}

#[test]
fn test_at_least() {
    assert_template_result!("5", r#"{{ 5 | at_least:4 }}"#);
    assert_template_result!("5", r#"{{ 5 | at_least:5 }}"#);
    assert_template_result!("6", r#"{{ 5 | at_least:6 }}"#);

    assert_template_result!("5", r#"{{ 4.5 | at_least:5 }}"#);
    // Implementation specific: use of drops
}

#[test]
fn test_append() {
    let assigns = o!({ "a": "bc", "b": "d" });
    assert_template_result!("bcd", r#"{{ a | append: "d"}}"#, assigns);
    assert_template_result!("bcd", r#"{{ a | append: b}}"#, assigns);
}

#[test]
fn test_concat() {
    assert_eq!(
        v!([1, 2, 3, 4]),
        call_filter!(liquid_lib::stdlib::Concat, v!([1, 2]), v!([3, 4])).unwrap()
    );
    assert_eq!(
        v!([1, 2, "a"]),
        call_filter!(liquid_lib::stdlib::Concat, v!([1, 2]), v!(["a"])).unwrap()
    );
    assert_eq!(
        v!([1, 2, 10]),
        call_filter!(liquid_lib::stdlib::Concat, v!([1, 2]), v!([10])).unwrap()
    );

    liquid_core::call_filter!(liquid_lib::stdlib::Concat, v!([1, 2]), 10).unwrap_err();
}

#[test]
fn test_prepend() {
    let assigns = o!({ "a": "bc", "b": "a" });
    assert_template_result!("abc", r#"{{ a | prepend: "a"}}"#, assigns);
    assert_template_result!("abc", r#"{{ a | prepend: b}}"#, assigns);
}

#[test]
fn test_default() {
    assert_eq!(
        v!("foo"),
        call_filter!(liquid_lib::stdlib::Default, v!("foo"), v!("bar")).unwrap()
    );
    assert_eq!(
        v!("bar"),
        call_filter!(liquid_lib::stdlib::Default, Nil, v!("bar")).unwrap()
    );
    assert_eq!(
        v!("bar"),
        call_filter!(liquid_lib::stdlib::Default, v!(""), v!("bar")).unwrap()
    );
    assert_eq!(
        v!("bar"),
        call_filter!(liquid_lib::stdlib::Default, v!(false), v!("bar")).unwrap()
    );
    assert_eq!(
        v!("bar"),
        call_filter!(liquid_lib::stdlib::Default, v!([]), v!("bar")).unwrap()
    );
    assert_eq!(
        v!("bar"),
        call_filter!(liquid_lib::stdlib::Default, v!({}), v!("bar")).unwrap()
    );
}

#[test]
#[should_panic]
fn test_cannot_access_private_methods() {
    panic!("Implementation specific: filters can't access arbitrary variables");
}

#[test]
fn test_date_raises_nothing() {
    assert_template_result!("", r#"{{ "" | date: "%D" }}"#);
    assert_template_result!("abc", r#"{{ "abc" | date: "%D" }}"#);
}

#[test]
fn test_where() {
    let input = v!([
      { "handle": "alpha", "ok": true },
      { "handle": "beta", "ok": false },
      { "handle": "gamma", "ok": false },
      { "handle": "delta", "ok": true }
    ]);

    let expectation = v!([
      { "handle": "alpha", "ok": true },
      { "handle": "delta", "ok": true }
    ]);

    assert_eq!(
        expectation,
        call_filter!(liquid_lib::stdlib::Where, input, v!("ok"), v!(true)).unwrap()
    );
    assert_eq!(
        expectation,
        call_filter!(liquid_lib::stdlib::Where, input, v!("ok")).unwrap()
    );
}

#[test]
fn test_where_no_key_set() {
    let input = v!([
      { "handle": "alpha", "ok": true },
      { "handle": "beta" },
      { "handle": "gamma" },
      { "handle": "delta", "ok": true }
    ]);

    let expectation = v!([
      { "handle": "alpha", "ok": true },
      { "handle": "delta", "ok": true }
    ]);

    assert_eq!(
        expectation,
        call_filter!(liquid_lib::stdlib::Where, input, v!("ok"), v!(true)).unwrap()
    );
    assert_eq!(
        expectation,
        call_filter!(liquid_lib::stdlib::Where, input, v!("ok")).unwrap()
    );
}

#[test]
fn test_where_non_array_map_input() {
    assert_eq!(
        v!([{ "a": "ok" }]),
        call_filter!(
            liquid_lib::stdlib::Where,
            v!({ "a": "ok" }),
            v!("a"),
            v!("ok")
        )
        .unwrap()
    );
    assert_eq!(
        v!([]),
        call_filter!(
            liquid_lib::stdlib::Where,
            v!({ "a": "not ok" }),
            v!("a"),
            v!("ok")
        )
        .unwrap()
    );
}

#[test]
fn test_where_indexable_but_non_map_value() {
    liquid_core::call_filter!(liquid_lib::stdlib::Where, 1, "ok", true).unwrap_err();
    liquid_core::call_filter!(liquid_lib::stdlib::Where, 1, "ok").unwrap_err();
}

#[test]
fn test_where_non_boolean_value() {
    let input = v!([
      { "message": "Bonjour!", "language": "French" },
      { "message": "Hello!", "language": "English" },
      { "message": "Hallo!", "language": "German" }
    ]);

    assert_eq!(
        v!([{ "message": "Bonjour!", "language": "French" }]),
        call_filter!(liquid_lib::stdlib::Where, input, "language", "French").unwrap()
    );
    assert_eq!(
        v!([{ "message": "Hallo!", "language": "German" }]),
        call_filter!(
            liquid_lib::stdlib::Where,
            input,
            v!("language"),
            v!("German")
        )
        .unwrap()
    );
    assert_eq!(
        v!([{ "message": "Hello!", "language": "English" }]),
        call_filter!(liquid_lib::stdlib::Where, input, "language", "English").unwrap()
    );
}

#[test]
fn test_where_array_of_only_unindexable_values() {
    assert_eq!(
        Nil,
        call_filter!(liquid_lib::stdlib::Where, v!([Nil]), "ok", true).unwrap()
    );
    assert_eq!(
        Nil,
        call_filter!(liquid_lib::stdlib::Where, v!([Nil]), "ok").unwrap()
    );
}

#[test]
fn test_where_no_target_value() {
    let input = v!([
      { "foo": false },
      { "foo": true },
      { "foo": "for sure" },
      { "bar": true }
    ]);

    assert_eq!(
        v!([{ "foo": true }, { "foo": "for sure" }]),
        call_filter!(liquid_lib::stdlib::Where, input, v!("foo")).unwrap()
    );
}
