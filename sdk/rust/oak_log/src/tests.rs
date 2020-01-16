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

use crate::OakChannelLogger;
use log::{Level, LevelFilter, Log, Metadata, Record};
use serial_test_derive::serial;

fn test_logger() -> (oak::ReadHandle, OakChannelLogger) {
    let (write_handle, read_handle) = oak::channel_create().unwrap();
    (
        read_handle,
        OakChannelLogger {
            channel: oak::io::Channel::new(oak::WriteHandle {
                handle: write_handle.handle,
            }),
        },
    )
}

#[test]
#[serial(set_level)]
fn test_enabled() {
    let (_h, x) = test_logger();
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
#[serial(set_level)]
fn test_log() {
    oak_tests::reset();
    let (handle, logger) = test_logger();
    log::set_max_level(log::LevelFilter::Info);

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

    let mut buf = Vec::new();
    let mut handles = Vec::new();
    assert_eq!(
        Err(oak::OakStatus::ERR_CHANNEL_EMPTY),
        oak::channel_read(handle, &mut buf, &mut handles)
    );
    assert_eq!(0, buf.len());
    assert_eq!(0, handles.len());

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
    let mut buf = Vec::new();
    let mut handles = Vec::new();
    assert_eq!(Ok(()), oak::channel_read(handle, &mut buf, &mut handles));
    assert_eq!(0, handles.len());
    assert_eq!(
        "ERROR  app.rs : 433 : Error!\n",
        std::str::from_utf8(&buf).unwrap()
    );
}

#[test]
fn test_flush() {
    let (_h, x) = test_logger();
    x.flush(); // Purely for coverage
}
