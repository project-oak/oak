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

use super::{
    merkle::root_from_paths, sign::Verifier, Error, RtMessage, Tag, CERTIFICATE_CONTEXT,
    SIGNED_RESPONSE_CONTEXT,
};
use byteorder::{LittleEndian, ReadBytesExt};
use ring::{rand, rand::SecureRandom as _};
use std::collections::HashMap;

/// Creates a 64 byte nonce.
pub fn create_nonce() -> Result<[u8; 64], Error> {
    let rng = rand::SystemRandom::new();
    let mut nonce = [0u8; 64];
    rng.fill(&mut nonce)?;

    Ok(nonce)
}

/// Converts a nonce to a Roughtime request.
pub fn make_request(nonce: &[u8]) -> Result<Vec<u8>, Error> {
    let mut msg = RtMessage::new(1);
    msg.add_field(Tag::NONC, nonce)?;
    msg.pad_to_kilobyte();

    msg.encode()
}

/// The parsed data extracted from a Roughtime response.
pub struct ParsedResponse {
    pub verified: bool,
    pub midpoint: u64,
    pub radius: u32,
}

/// Decodes, parses and validates Roughtime responses.
///
/// See https://roughtime.googlesource.com/roughtime/+/HEAD/PROTOCOL.md#processing-a-response
pub struct ResponseHandler {
    /// The 256-bit Ed25519 public key for validating the signature.
    pub_key: Vec<u8>,
    /// The entire parsed message.
    msg: HashMap<Tag, Vec<u8>>,
    /// The response.
    srep: HashMap<Tag, Vec<u8>>,
    /// The full extracted certificate.
    cert: HashMap<Tag, Vec<u8>>,
    /// The delegated key contained in the certificate
    dele: HashMap<Tag, Vec<u8>>,
    /// The nonce sent in the original request.
    nonce: [u8; 64],
}

impl ResponseHandler {
    pub fn new(
        pub_key: Vec<u8>,
        response: RtMessage,
        nonce: [u8; 64],
    ) -> Result<ResponseHandler, Error> {
        let msg = response.into_hash_map();
        let srep = RtMessage::from_bytes(&msg[&Tag::SREP])?.into_hash_map();
        let cert = RtMessage::from_bytes(&msg[&Tag::CERT])?.into_hash_map();
        let dele = RtMessage::from_bytes(&cert[&Tag::DELE])?.into_hash_map();

        Ok(ResponseHandler {
            pub_key,
            msg,
            srep,
            cert,
            dele,
            nonce,
        })
    }

    pub fn extract_time(&self) -> Result<ParsedResponse, Error> {
        let midpoint = self.srep[&Tag::MIDP]
            .as_slice()
            .read_u64::<LittleEndian>()?;
        let radius = self.srep[&Tag::RADI]
            .as_slice()
            .read_u32::<LittleEndian>()?;

        let verified = self.validate_dele()?
            && self.validate_srep()
            && self.validate_merkle()?
            && self.validate_midpoint(midpoint)?;

        Ok(ParsedResponse {
            verified,
            midpoint,
            radius,
        })
    }

    fn validate_dele(&self) -> Result<bool, Error> {
        let mut full_cert = Vec::from(CERTIFICATE_CONTEXT.as_bytes());
        full_cert.extend(&self.cert[&Tag::DELE]);

        Ok(self.validate_sig(&self.pub_key, &self.cert[&Tag::SIG], &full_cert))
    }

    fn validate_srep(&self) -> bool {
        let mut full_srep = Vec::from(SIGNED_RESPONSE_CONTEXT.as_bytes());
        full_srep.extend(&self.msg[&Tag::SREP]);

        self.validate_sig(&self.dele[&Tag::PUBK], &self.msg[&Tag::SIG], &full_srep)
    }

    fn validate_merkle(&self) -> Result<bool, Error> {
        let srep = RtMessage::from_bytes(&self.msg[&Tag::SREP])?.into_hash_map();
        let index = self.msg[&Tag::INDX].as_slice().read_u32::<LittleEndian>()?;
        let paths = &self.msg[&Tag::PATH];

        let hash = root_from_paths(index as usize, &self.nonce, paths);

        Ok(hash == srep[&Tag::ROOT])
    }

    fn validate_midpoint(&self, midpoint: u64) -> Result<bool, Error> {
        let mint = self.dele[&Tag::MINT]
            .as_slice()
            .read_u64::<LittleEndian>()?;
        let maxt = self.dele[&Tag::MAXT]
            .as_slice()
            .read_u64::<LittleEndian>()?;
        Ok(midpoint >= mint && midpoint <= maxt)
    }

    fn validate_sig(&self, public_key: &[u8], sig: &[u8], data: &[u8]) -> bool {
        let mut verifier = Verifier::new(public_key);
        verifier.update(data);
        verifier.verify(sig)
    }
}

#[cfg(test)]
mod test {
    use crate::{
        client::{make_request, ParsedResponse, ResponseHandler},
        RtMessage,
    };
    use hex::FromHex as _;

    /// Test decoding, parsing and validating of a valid Roughtime response.
    #[test]
    fn test_handle_valid_response() {
        let public_key =
            hex::decode("016e6e0284d24c37c6e4d7d8d5b4e1d3c1949ceaa545bf875616c9dce0c9bec1")
                .unwrap();
        let nonce = <[u8; 64]>::from_hex(
            "dcc9cf71abdc6e2628fbbc81ba662656f27434af992ac71dd85950e4d2f51512\
             79e98b249e5ae290f1a3434b89effcfd5c342b10f578cb16f93336fe05218504",
        )
        .unwrap();
        let response = hex::decode(
            "050000004000000040000000a40000003c010000534947005041544853524550\
             43455254494e445841b51370f677aec82b2a7fb79395646b7dc5890cdc919954\
             927962b753d06f4df6a075ae4336a33bd113573ba9be42c72b5b6149474288cc\
             d6b113f42190bb0a03000000040000000c000000524144494d494450524f4f54\
             40420f00b7b228afb6a6050066dd21c1c33d0e8538b3134c96aedd174a0f7b4b\
             671008ba7249cee87381b80261540f222cff6a6dae32f46036be7add8ec1debc\
             4d4977197a53d9d13b2a6a8b02000000400000005349470044454c45340b2e99\
             50bf4acde29efb068e7da93f1b6eab95e8c292c082c8fd3c362cb1a8f67a1a65\
             e81416633eacdbb5775015384550d358faff6c43981be9d1de8c660103000000\
             20000000280000005055424b4d494e544d415854b86b5758a08079bbfce46d1d\
             ec22d7ae855ad092ccf38fe1a783dcb0a3a3bd560000000000000000ffffffff\
             ffffffff00000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();
        let ParsedResponse {
            verified,
            midpoint,
            radius,
        } = ResponseHandler::new(
            public_key,
            RtMessage::from_bytes(response.as_ref()).unwrap(),
            nonce.to_owned(),
        )
        .unwrap()
        .extract_time()
        .unwrap();
        assert!(verified);
        assert_eq!(midpoint, 1_590_678_436_491_959);
        assert_eq!(radius, 1_000_000);
    }

    /// Test decoding, parsing and validating of a Roughtime response with an invalid signature.
    #[test]
    fn test_handle_invalid_response() {
        let public_key =
            hex::decode("116e6e0284d24c37c6e4d7d8d5b4e1d3c1949ceaa545bf875616c9dce0c9bec1")
                .unwrap();
        let nonce = <[u8; 64]>::from_hex(
            "dcc9cf71abdc6e2628fbbc81ba662656f27434af992ac71dd85950e4d2f51512\
             79e98b249e5ae290f1a3434b89effcfd5c342b10f578cb16f93336fe05218504",
        )
        .unwrap();
        let response = hex::decode(
            "050000004000000040000000a40000003c010000534947005041544853524550\
             43455254494e445841b51370f677aec82b2a7fb79395646b7dc5890cdc919954\
             927962b753d06f4df6a075ae4336a33bd113573ba9be42c72b5b6149474288cc\
             d6b113f42190bb0a03000000040000000c000000524144494d494450524f4f54\
             40420f00b7b228afb6a6050066dd21c1c33d0e8538b3134c96aedd174a0f7b4b\
             671008ba7249cee87381b80261540f222cff6a6dae32f46036be7add8ec1debc\
             4d4977197a53d9d13b2a6a8b02000000400000005349470044454c45340b2e99\
             50bf4acde29efb068e7da93f1b6eab95e8c292c082c8fd3c362cb1a8f67a1a65\
             e81416633eacdbb5775015384550d358faff6c43981be9d1de8c660103000000\
             20000000280000005055424b4d494e544d415854b86b5758a08079bbfce46d1d\
             ec22d7ae855ad092ccf38fe1a783dcb0a3a3bd560000000000000000ffffffff\
             ffffffff00000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();
        let ParsedResponse {
            verified,
            midpoint,
            radius,
        } = ResponseHandler::new(
            public_key,
            RtMessage::from_bytes(response.as_ref()).unwrap(),
            nonce.to_owned(),
        )
        .unwrap()
        .extract_time()
        .unwrap();

        assert!(!verified);
        assert_eq!(midpoint, 1_590_678_436_491_959);
        assert_eq!(radius, 1_000_000);
    }

    #[test]
    fn test_make_request() {
        let nonce = hex::decode(
            "cbf7350a64a9a6db8784a22fc90c60fe2b9acf65340f139dbaa179c0a23763cc\
             eb258d1867db96052b2b0de5312d39dedffe123dde6d4546a6f536597e985cd6",
        )
        .unwrap();
        let expected_request = hex::decode(
            "02000000400000004e4f4e43504144ffcbf7350a64a9a6db8784a22fc90c60fe\
             2b9acf65340f139dbaa179c0a23763cceb258d1867db96052b2b0de5312d39de\
             dffe123dde6d4546a6f536597e985cd600000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000\
             0000000000000000000000000000000000000000000000000000000000000000",
        )
        .unwrap();
        let request = make_request(nonce.as_ref()).unwrap();
        assert_eq!(request, expected_request);
    }
}
