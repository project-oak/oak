// Make sure the trim isn't applied to standard output
#[test]
fn test_standard_output() {
    let text = r#"
      <div>
        <p>
          {{ 'John' }}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>
          John
        </p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_variable_output_with_multiple_blank_lines() {
    let text = r#"
      <div>
        <p>


          {{- 'John' -}}


        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>John</p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_tag_output_with_multiple_blank_lines() {
    let text = r#"
      <div>
        <p>


          {%- if true -%}
          yes
          {%- endif -%}


        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>yes</p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

// Make sure the trim isn't applied to standard tags
#[test]
fn test_standard_tags() {
    let text = r#"
      <div>
        <p>
          {% if true %}
          yes
          {% endif %}
        </p>
      </div>
    "#;
    let expected = r#"
......<div>
........<p>
..........
..........yes
..........
........</p>
......</div>
...."#
        .replace(".", " ");
    assert_template_result!(expected, text);

    let text = r#"
      <div>
        <p>
          {% if false %}
          no
          {% endif %}
        </p>
      </div>
    "#;
    let expected = r#"
......<div>
........<p>
..........
........</p>
......</div>
...."#
        .replace(".", " ");
    assert_template_result!(expected, text);
}

// Make sure the trim isn't too aggressive
#[test]
fn test_no_trim_output() {
    let text = r#"<p>{{- 'John' -}}</p>"#;
    let expected = "<p>John</p>";
    assert_template_result!(expected, text);
}

// Make sure the trim isn't too aggressive
#[test]
fn test_no_trim_tags() {
    let text = r#"<p>{%- if true -%}yes{%- endif -%}</p>"#;
    let expected = r#"<p>yes</p>"#;
    assert_template_result!(expected, text);

    let text = r#"<p>{%- if false -%}no{%- endif -%}</p>"#;
    let expected = r#"<p></p>"#;
    assert_template_result!(expected, text);
}

#[test]
fn test_single_line_outer_tag() {
    let text = r#"<p> {%- if true %} yes {% endif -%} </p>"#;
    let expected = r#"<p> yes </p>"#;
    assert_template_result!(expected, text);

    let text = r#"<p> {%- if false %} no {% endif -%} </p>"#;
    let expected = r#"<p></p>"#;
    assert_template_result!(expected, text);
}

#[test]
fn test_single_line_inner_tag() {
    let text = r#"<p> {% if true -%} yes {%- endif %} </p>"#;
    let expected = r#"<p> yes </p>"#;
    assert_template_result!(expected, text);

    let text = r#"<p> {% if false -%} no {%- endif %} </p>"#;
    let expected = r#"<p>  </p>"#;
    assert_template_result!(expected, text);
}

#[test]
fn test_single_line_post_tag() {
    let text = r#"<p> {% if true -%} yes {% endif -%} </p>"#;
    let expected = r#"<p> yes </p>"#;
    assert_template_result!(expected, text);

    let text = r#"<p> {% if false -%} no {% endif -%} </p>"#;
    let expected = r#"<p> </p>"#;
    assert_template_result!(expected, text);
}

#[test]
fn test_single_line_pre_tag() {
    let text = r#"<p> {%- if true %} yes {%- endif %} </p>"#;
    let expected = r#"<p> yes </p>"#;
    assert_template_result!(expected, text);

    let text = r#"<p> {%- if false %} no {%- endif %} </p>"#;
    let expected = r#"<p> </p>"#;
    assert_template_result!(expected, text);
}

#[test]
fn test_pre_trim_output() {
    let text = r#"
      <div>
        <p>
          {{- 'John' }}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>John
        </p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_pre_trim_tags() {
    let text = r#"
      <div>
        <p>
          {%- if true %}
          yes
          {%- endif %}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>
          yes
        </p>
      </div>
    "#;
    assert_template_result!(expected, text);

    let text = r#"
      <div>
        <p>
          {%- if false %}
          no
          {%- endif %}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>
        </p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_post_trim_output() {
    let text = r#"
      <div>
        <p>
          {{ 'John' -}}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>
          John</p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_post_trim_tags() {
    let text = r#"
      <div>
        <p>
          {% if true -%}
          yes
          {% endif -%}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>
          yes
          </p>
      </div>
    "#;
    assert_template_result!(expected, text);

    let text = r#"
      <div>
        <p>
          {% if false -%}
          no
          {% endif -%}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>
          </p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_pre_and_post_trim_tags() {
    let text = r#"
      <div>
        <p>
          {%- if true %}
          yes
          {% endif -%}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>
          yes
          </p>
      </div>
    "#;
    assert_template_result!(expected, text);

    let text = r#"
      <div>
        <p>
          {%- if false %}
          no
          {% endif -%}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p></p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_post_and_pre_trim_tags() {
    let text = r#"
      <div>
        <p>
          {% if true -%}
          yes
          {%- endif %}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>
          yes
        </p>
      </div>
    "#;
    assert_template_result!(expected, text);

    let text = r#"
      <div>
        <p>
          {% if false -%}
          no
          {%- endif %}
        </p>
      </div>
    "#;
    let expected = r#"
......<div>
........<p>
..........
........</p>
......</div>
...."#
        .replace(".", " ");
    assert_template_result!(expected, text);
}

#[test]
fn test_trim_output() {
    let text = r#"
      <div>
        <p>
          {{- 'John' -}}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>John</p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_trim_tags() {
    let text = r#"
      <div>
        <p>
          {%- if true -%}
          yes
          {%- endif -%}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>yes</p>
      </div>
    "#;
    assert_template_result!(expected, text);

    let text = r#"
      <div>
        <p>
          {%- if false -%}
          no
          {%- endif -%}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p></p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_whitespace_trim_output() {
    let text = r#"
      <div>
        <p>
          {{- 'John' -}},
          {{- '30' -}}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>John,30</p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_whitespace_trim_tags() {
    let text = r#"
      <div>
        <p>
          {%- if true -%}
          yes
          {%- endif -%}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>yes</p>
      </div>
    "#;
    assert_template_result!(expected, text);

    let text = r#"
      <div>
        <p>
          {%- if false -%}
          no
          {%- endif -%}
        </p>
      </div>
    "#;
    let expected = r#"
      <div>
        <p></p>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_complex_trim_output() {
    let text = r#"
      <div>
        <p>
          {{- 'John' -}}
          {{- '30' -}}
        </p>
        <b>
          {{ 'John' -}}
          {{- '30' }}
        </b>
        <i>
          {{- 'John' }}
          {{ '30' -}}
        </i>
      </div>
    "#;
    let expected = r#"
      <div>
        <p>John30</p>
        <b>
          John30
        </b>
        <i>John
          30</i>
      </div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_complex_trim() {
    let text = r#"
      <div>
        {%- if true -%}
          {%- if true -%}
            <p>
              {{- 'John' -}}
            </p>
          {%- endif -%}
        {%- endif -%}
      </div>
    "#;
    let expected = r#"
      <div><p>John</p></div>
    "#;
    assert_template_result!(expected, text);
}

#[test]
fn test_right_trim_followed_by_tag() {
    assert_template_result!(r#"ab c"#, r#"{{ "a" -}}{{ "b" }} c"#);
}

#[test]
fn test_raw_output() {
    let text = r#"
      <div>
        {% raw %}
          {%- if true -%}
            <p>
              {{- 'John' -}}
            </p>
          {%- endif -%}
        {% endraw %}
      </div>
    "#;
    let expected = r#"
......<div>
........
..........{%-.if.true.-%}
............<p>
..............{{-.'John'.-}}
............</p>
..........{%-.endif.-%}
........
......</div>
...."#
        .replace(".", " ");
    assert_template_result!(expected, text);
}
