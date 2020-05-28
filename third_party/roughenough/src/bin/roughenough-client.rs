// Copyright 2017-2019 int08h LLC

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

// for value_t_or_exit!()
#[macro_use]
extern crate clap;

use ring::rand;
use ring::rand::SecureRandom;

use byteorder::{LittleEndian, ReadBytesExt};

use chrono::offset::Utc;
use chrono::{TimeZone, Local};

use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::iter::Iterator;
use std::net::{SocketAddr, ToSocketAddrs, UdpSocket};

use clap::{App, Arg};
use roughenough::merkle::root_from_paths;
use roughenough::sign::Verifier;
use roughenough::{
    roughenough_version, RtMessage, Tag, CERTIFICATE_CONTEXT, SIGNED_RESPONSE_CONTEXT,
};

fn create_nonce() -> [u8; 64] {
    let rng = rand::SystemRandom::new();
    let mut nonce = [0u8; 64];
    rng.fill(&mut nonce).unwrap();

    nonce
}

fn make_request(nonce: &[u8]) -> Vec<u8> {
    let mut msg = RtMessage::new(1);
    msg.add_field(Tag::NONC, nonce).unwrap();
    msg.pad_to_kilobyte();

    msg.encode().unwrap()
}

fn receive_response(sock: &mut UdpSocket) -> RtMessage {
    let mut buf = [0; 744];
    let resp_len = sock.recv_from(&mut buf).unwrap().0;

    RtMessage::from_bytes(&buf[0..resp_len]).unwrap()
}

fn stress_test_forever(addr: &SocketAddr) -> ! {
    if !addr.ip().is_loopback() {
        panic!("Cannot use non-loopback address {} for stress testing", addr.ip());
    }

    println!("Stress testing!");

    let nonce = create_nonce();
    let socket = UdpSocket::bind("0.0.0.0:0").expect("Couldn't open UDP socket");
    let request = make_request(&nonce);
    loop {
        socket.send_to(&request, addr).unwrap();
    }
}

struct ResponseHandler {
    pub_key: Option<Vec<u8>>,
    msg: HashMap<Tag, Vec<u8>>,
    srep: HashMap<Tag, Vec<u8>>,
    cert: HashMap<Tag, Vec<u8>>,
    dele: HashMap<Tag, Vec<u8>>,
    nonce: [u8; 64],
}

struct ParsedResponse {
    verified: bool,
    midpoint: u64,
    radius: u32,
}

impl ResponseHandler {
    pub fn new(pub_key: Option<Vec<u8>>, response: RtMessage, nonce: [u8; 64]) -> ResponseHandler {
        let msg = response.into_hash_map();
        let srep = RtMessage::from_bytes(&msg[&Tag::SREP])
            .unwrap()
            .into_hash_map();
        let cert = RtMessage::from_bytes(&msg[&Tag::CERT])
            .unwrap()
            .into_hash_map();
        let dele = RtMessage::from_bytes(&cert[&Tag::DELE])
            .unwrap()
            .into_hash_map();

        ResponseHandler {
            pub_key,
            msg,
            srep,
            cert,
            dele,
            nonce,
        }
    }

    pub fn extract_time(&self) -> ParsedResponse {
        let midpoint = self.srep[&Tag::MIDP]
            .as_slice()
            .read_u64::<LittleEndian>()
            .unwrap();
        let radius = self.srep[&Tag::RADI]
            .as_slice()
            .read_u32::<LittleEndian>()
            .unwrap();

        let verified = if self.pub_key.is_some() {
            self.validate_dele();
            self.validate_srep();
            self.validate_merkle();
            self.validate_midpoint(midpoint);
            true
        } else {
            false
        };

        ParsedResponse {
            verified,
            midpoint,
            radius,
        }
    }

    fn validate_dele(&self) {
        let mut full_cert = Vec::from(CERTIFICATE_CONTEXT.as_bytes());
        full_cert.extend(&self.cert[&Tag::DELE]);

        assert!(
            self.validate_sig(
                self.pub_key.as_ref().unwrap(),
                &self.cert[&Tag::SIG],
                &full_cert
            ),
            "Invalid signature on DELE tag, response may not be authentic"
        );
    }

    fn validate_srep(&self) {
        let mut full_srep = Vec::from(SIGNED_RESPONSE_CONTEXT.as_bytes());
        full_srep.extend(&self.msg[&Tag::SREP]);

        assert!(
            self.validate_sig(&self.dele[&Tag::PUBK], &self.msg[&Tag::SIG], &full_srep),
            "Invalid signature on SREP tag, response may not be authentic"
        );
    }

    fn validate_merkle(&self) {
        let srep = RtMessage::from_bytes(&self.msg[&Tag::SREP])
            .unwrap()
            .into_hash_map();
        let index = self.msg[&Tag::INDX]
            .as_slice()
            .read_u32::<LittleEndian>()
            .unwrap();
        let paths = &self.msg[&Tag::PATH];

        let hash = root_from_paths(index as usize, &self.nonce, paths);

        assert_eq!(
            hash, srep[&Tag::ROOT],
            "Nonce is not present in the response's merkle tree"
        );
    }

    fn validate_midpoint(&self, midpoint: u64) {
        let mint = self.dele[&Tag::MINT]
            .as_slice()
            .read_u64::<LittleEndian>()
            .unwrap();
        let maxt = self.dele[&Tag::MAXT]
            .as_slice()
            .read_u64::<LittleEndian>()
            .unwrap();

        assert!(
            midpoint >= mint,
            "Response midpoint {} lies *before* delegation span ({}, {})",
            midpoint, mint, maxt
        );
        assert!(
            midpoint <= maxt,
            "Response midpoint {} lies *after* delegation span ({}, {})",
            midpoint, mint, maxt
        );
    }

    fn validate_sig(&self, public_key: &[u8], sig: &[u8], data: &[u8]) -> bool {
        let mut verifier = Verifier::new(public_key);
        verifier.update(data);
        verifier.verify(sig)
    }
}

fn main() {
    let matches = App::new("roughenough client")
    .version(roughenough_version().as_ref())
    .arg(Arg::with_name("host")
      .required(true)
      .help("The Roughtime server to connect to.")
      .takes_value(true))
    .arg(Arg::with_name("port")
      .required(true)
      .help("The Roughtime server port to connect to.")
      .takes_value(true))
    .arg(Arg::with_name("verbose")
      .short("v")
      .long("verbose")
      .help("Output additional details about the server's response."))
    .arg(Arg::with_name("json")
      .short("j")
      .long("json")
      .help("Output the server's response in JSON format."))
    .arg(Arg::with_name("public-key")
      .short("p")
      .long("public-key")
      .takes_value(true)
      .help("The server public key used to validate responses. If unset, no validation will be performed."))
    .arg(Arg::with_name("time-format")
      .short("f")
      .long("time-format")
      .takes_value(true)
      .help("The strftime format string used to print the time recieved from the server.")
      .default_value("%b %d %Y %H:%M:%S %Z")
    )
    .arg(Arg::with_name("num-requests")
      .short("n")
      .long("num-requests")
      .takes_value(true)
      .help("The number of requests to make to the server (each from a different source port). This is mainly useful for testing batch response handling.")
      .default_value("1")
    )
    .arg(Arg::with_name("stress")
      .short("s")
      .long("stress")
      .help("Stress test the server by sending the same request as fast as possible. Please only use this on your own server.")
    )
    .arg(Arg::with_name("output")
      .short("o")
      .long("output")
      .takes_value(true)
      .help("Writes all requests to the specified file, in addition to sending them to the server. Useful for generating fuzzer inputs.")
    )
    .arg(Arg::with_name("zulu")
      .short("z")
      .long("zulu")
      .help("Display time in UTC (default is local time zone)")
    )
    .get_matches();

    let host = matches.value_of("host").unwrap();
    let port = value_t_or_exit!(matches.value_of("port"), u16);
    let verbose = matches.is_present("verbose");
    let json = matches.is_present("json");
    let num_requests = value_t_or_exit!(matches.value_of("num-requests"), u16) as usize;
    let time_format = matches.value_of("time-format").unwrap();
    let stress = matches.is_present("stress");
    let pub_key = matches
        .value_of("public-key")
        .map(|pkey| hex::decode(pkey).expect("Error parsing public key!"));
    let out = matches.value_of("output");
    let use_utc = matches.is_present("zulu");

    if verbose {
        eprintln!("Requesting time from: {:?}:{:?}", host, port);
    }

    let addr = (host, port).to_socket_addrs().unwrap().next().unwrap();

    if stress {
        stress_test_forever(&addr)
    }

    let mut requests = Vec::with_capacity(num_requests);
    let mut file = out.map(|o| File::create(o).expect("Failed to create file!"));

    for _ in 0..num_requests {
        let nonce = create_nonce();
        let socket = UdpSocket::bind("0.0.0.0:0").expect("Couldn't open UDP socket");
        let request = make_request(&nonce);

        if let Some(f) = file.as_mut() {
            f.write_all(&request).expect("Failed to write to file!")
        }

        requests.push((nonce, request, socket));
    }

    for &mut (_, ref request, ref mut socket) in &mut requests {
        socket.send_to(request, addr).unwrap();
    }

    for (nonce, _, mut socket) in requests {
        let resp = receive_response(&mut socket);

        let ParsedResponse {
            verified,
            midpoint,
            radius,
        } = ResponseHandler::new(pub_key.clone(), resp.clone(), nonce).extract_time();

        let map = resp.into_hash_map();
        let index = map[&Tag::INDX]
            .as_slice()
            .read_u32::<LittleEndian>()
            .unwrap();

        let seconds = midpoint / 10_u64.pow(6);
        let nsecs = (midpoint - (seconds * 10_u64.pow(6))) * 10_u64.pow(3);
        let verify_str = if verified { "Yes" } else { "No" };

        let out = if use_utc {
            let ts = Utc.timestamp(seconds as i64, nsecs as u32);
            ts.format(time_format).to_string()
        } else {
            let ts = Local.timestamp(seconds as i64, nsecs as u32);
            ts.format(time_format).to_string()
        };

        if verbose {
            eprintln!(
                "Received time from server: midpoint={:?}, radius={:?}, verified={} (merkle_index={})",
                out, radius, verify_str, index
            );
        }

        if json {
            println!(
                r#"{{ "midpoint": {:?}, "radius": {:?}, "verified": {}, "merkle_index": {} }}"#,
                out, radius, verified, index
            );
        } else {
            println!("{}", out);
        }
    }
}

