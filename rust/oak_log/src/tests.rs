//
// Copyright 2019 The Project Oak Authors
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

extern crate oak_tests;

use crate::OakChannelLogger;
use log::{Level, LevelFilter, Log, Metadata, Record};
use oak_tests::last_message;

#[test]
fn test_enabled() {
    let x = OakChannelLogger {};
    struct T {
        l: Level,
        max: LevelFilter,
        want: bool,
    };
    let tests = vec![
        T {
            l: Level::Debug,
            max: LevelFilter::Debug,
            want: true,
        },
        T {
            l: Level::Error,
            max: LevelFilter::Debug,
            want: true,
        },
        T {
            l: Level::Trace,
            max: LevelFilter::Debug,
            want: false,
        },
    ];
    for test in &tests {
        let m = Metadata::builder().level(test.l).target("test").build();
        log::set_max_level(test.max);
        assert_eq!(test.want, x.enabled(&m));
    }
}

#[test]
fn test_log() {
    let logger = OakChannelLogger {};
    let trace = Metadata::builder()
        .level(Level::Trace)
        .target("test")
        .build();
    let r1 = Record::builder()
        .metadata(trace)
        .args(format_args!("Detailed trace"))
        .line(Some(433))
        .file(Some("app.rs"))
        .module_path(Some("server"))
        .build();
    logger.log(&r1);
    assert_eq!("", last_message());

    let error = Metadata::builder()
        .level(Level::Error)
        .target("test")
        .build();
    let r2 = Record::builder()
        .metadata(error)
        .args(format_args!("Error!"))
        .line(Some(433))
        .file(Some("app.rs"))
        .module_path(Some("server"))
        .build();
    logger.log(&r2);
    assert_eq!("ERROR  app.rs : 433 : Error!\n", last_message());
}

#[test]
fn test_flush() {
    let x = OakChannelLogger {};
    x.flush(); // Purely for coverage
}
