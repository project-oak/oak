//
// Copyright 2021 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use super::*;

// Tests based on https://github.com/google/differential-privacy/blob/main/go/checks/checks_test.go.

#[test]
fn test_check_epsilon_very_strict() {
    struct TestCase {
        desc: &'static str,
        epsilon: f64,
        want_err: bool,
    }

    for tc in vec![
        TestCase {
            desc: "epsilon < 2⁻⁵⁰",
            epsilon: (-51.0_f64).exp2(),
            want_err: true,
        },
        TestCase {
            desc: "epsilon == 2⁻⁵⁰",
            epsilon: (-50.0_f64).exp2(),
            want_err: false,
        },
        TestCase {
            desc: "negative epsilon",
            epsilon: -2.0_f64,
            want_err: true,
        },
        TestCase {
            desc: "zero epsilon",
            epsilon: 0.0_f64,
            want_err: true,
        },
        TestCase {
            desc: "epsilon is NaN",
            epsilon: f64::NAN,
            want_err: true,
        },
        TestCase {
            desc: "epsilon is negative infinity",
            epsilon: f64::NEG_INFINITY,
            want_err: true,
        },
        TestCase {
            desc: "epsilon is positive infinity",
            epsilon: f64::INFINITY,
            want_err: true,
        },
        TestCase {
            desc: "positive epsilon",
            epsilon: 50.0_f64,
            want_err: false,
        },
    ] {
        let err = check_epsilon_very_strict("test", tc.epsilon).is_err();
        assert_eq!(
            err, tc.want_err,
            "check_epsilon_very_strict: when {} for err got {}, want {}",
            tc.desc, err, tc.want_err
        );
    }
}

#[test]
fn test_check_no_delta() {
    struct TestCase {
        desc: &'static str,
        delta: f64,
        want_err: bool,
    }

    for tc in vec![
        TestCase {
            desc: "negative delta",
            delta: -2.0_f64,
            want_err: true,
        },
        TestCase {
            desc: "positive delta",
            delta: 10.0_f64,
            want_err: true,
        },
        TestCase {
            desc: "zero delta",
            delta: 0.0_f64,
            want_err: false,
        },
    ] {
        let err = check_no_delta("test", tc.delta).is_err();
        assert_eq!(
            err, tc.want_err,
            "check_no_delta: when {} for err got {}, want {}",
            tc.desc, err, tc.want_err
        );
    }
}

#[test]
fn test_check_l_0_sensitivity() {
    struct TestCase {
        desc: &'static str,
        l_0_sensitivity: i64,
        want_err: bool,
    }

    for tc in vec![
        TestCase {
            desc: "negative l0 sensitivity",
            l_0_sensitivity: -2,
            want_err: true,
        },
        TestCase {
            desc: "zero l0 sensitivity",
            l_0_sensitivity: 0,
            want_err: true,
        },
        TestCase {
            desc: "l0 sensitivity == 10",
            l_0_sensitivity: 10,
            want_err: false,
        },
    ] {
        let err = check_l_0_sensitivity("test", tc.l_0_sensitivity).is_err();
        assert_eq!(
            err, tc.want_err,
            "check_l_0_sensitivity: when {} for err got {}, want {}",
            tc.desc, err, tc.want_err
        );
    }
}

#[test]
fn test_check_l_inf_sensitivity() {
    struct TestCase {
        desc: &'static str,
        l_inf_sensitivity: f64,
        want_err: bool,
    }
    for tc in vec![
        TestCase {
            desc: "negative lInf sensitivity",
            l_inf_sensitivity: -2.0_f64,
            want_err: true,
        },
        TestCase {
            desc: "zero lInf sensitivity",
            l_inf_sensitivity: 0.0_f64,
            want_err: true,
        },
        TestCase {
            desc: "lInf sensitivity is negative infinity",
            l_inf_sensitivity: f64::NEG_INFINITY,
            want_err: true,
        },
        TestCase {
            desc: "lInf sensitivity is positive infinity",
            l_inf_sensitivity: f64::INFINITY,
            want_err: true,
        },
        TestCase {
            desc: "lInf sensitivity is NaN",
            l_inf_sensitivity: f64::NAN,
            want_err: true,
        },
        TestCase {
            desc: "lInf sensitivity == 10",
            l_inf_sensitivity: 10.0_f64,
            want_err: false,
        },
    ] {
        let err = check_l_inf_sensitivity("test", tc.l_inf_sensitivity).is_err();
        assert_eq!(
            err, tc.want_err,
            "check_l_inf_sensitivity: when {} for err got {}, want {}",
            tc.desc, err, tc.want_err
        );
    }
}
