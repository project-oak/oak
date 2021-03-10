//
// Copyright 2018 The Project Oak Authors
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

use crate::proto::oak::examples::veracruz_demo::{
    RandomRequest, RandomResponse, RandomResult, VeracruzDemo, VeracruzDemoDispatcher, Init,
};
use log::info;
use oak::grpc;
use http;
use oak::http::create_http_invocation;
use oak_abi::{
    label::{confidentiality_label, tls_endpoint_tag}
};

use oak::io::SenderExt;

oak::impl_dispatcher!(impl Handler : VeracruzDemoDispatcher);
oak::entrypoint_command_handler_init!(handler => Handler);

pub struct Handler {
    translator: Option<translator_common::TranslatorClient>,
}

impl oak::WithInit for Handler {
    type Init = Init;

    fn create(init: Self::Init) -> Self {
        oak::logger::init(init.log_sender.unwrap(), log::Level::Debug).unwrap();
        Self {
            translator: init
                .translator_sender
                .map(translator_common::TranslatorClient),
        }
    }
}

impl Handler {
    fn translate(&self, text: &str, from_lang: &str, to_lang: &str) -> Option<String> {
        let client = self.translator.as_ref()?;
        translator_common::translate(client, text, from_lang, to_lang)
    }
}

impl VeracruzDemo for Handler {
    fn generate_random(&mut self, req: RandomRequest) -> grpc::Result<RandomResponse> {
        info!("generate random called requesting {:} bytes", req.number_of_bytes);
        let mut response: RandomResponse = RandomResponse::default();
        let mut data: Vec<u8> = vec![0; req.number_of_bytes as usize];
        oak::random_get(&mut data).unwrap();
        response.data = data;
        Ok(response)
    }

    fn forward_random(&mut self, req: RandomRequest) -> grpc::Result<RandomResult> {
        info!("forward random called requesting {:} bytes", req.number_of_bytes);
        let mut result: RandomResult = RandomResult::default();
        let mut data: Vec<u8> = vec![0; req.number_of_bytes as usize];
        match oak::random_get(&mut data) {
            Ok(_) => {},
            Err(_) => {
                result.status = 1;
                return Ok(result);
            }
        }

        // Here's where the fun begins. How do we instantiate a http client pseudo node?

        let authority = "https://veracruz:8090/hello";
        let request = http::Request::builder()
            .method(http::Method::GET)
            .uri(authority)
            .body(data)
            .unwrap();
        info!("creating client node");
        let client_certificate = "-----BEGIN CERTIFICATE-----\nMIIDdTCCAl2gAwIBAgIUdnfz9i1JnlIDVUQ06i3YUTdbPxQwDQYJKoZIhvcNAQEL\nBQAwSjELMAkGA1UEBhMCVVMxDjAMBgNVBAgMBVRleGFzMQ8wDQYDVQQHDAZBdXN0\naW4xGjAYBgNVBAoMEVNwYWNlbHkgU3Byb2NrZXRzMB4XDTIxMDMwOTE2NTMxMloX\nDTI4MDYxMDE2NTMxMlowSjELMAkGA1UEBhMCVVMxDjAMBgNVBAgMBVRleGFzMQ8w\nDQYDVQQHDAZBdXN0aW4xGjAYBgNVBAoMEVNwYWNlbHkgU3Byb2NrZXRzMIIBIjAN\nBgkqhkiG9w0BAQEFAAOCAQ8AMIIBCgKCAQEA+YP+8o++9DQouQf37GlQVI2yBFXk\n7L+g9bnQlxAJSmocHy5SuiKfns+HSqd5iWSY4xAnD3OHlYxng9CQXRccJC6/YQfT\nkmKFxpyXnZW/kzs1yWivigJ+uyY1B4+/6vDmLYo4Df1EgiYhbodPgYC7buPMKAfw\nLPuwZi8Hg+D7jKD2s64yinUWtf/ddLtBGnK5FXJSlaWV3KMHKJt6BijMKN/6rhRo\nXWSObCZPSFLFdsyAoIwEzROPnXv1swjSVkIwEJgSuMC8vXDikwHJGdT4RPFyBMlu\n9zcxUDR5Ak1f7ot6Pwd2lhPg/4lXjHuDLz2YSTVrxyQjaH+NvAUzFWJYLwIDAQAB\no1MwUTAdBgNVHQ4EFgQUqZhFGctZCc+cQdqcZG/urMky/60wHwYDVR0jBBgwFoAU\nqZhFGctZCc+cQdqcZG/urMky/60wDwYDVR0TAQH/BAUwAwEB/zANBgkqhkiG9w0B\nAQsFAAOCAQEANSmm1h3OTaPMTTce7wBLzLsjwcCZHgeafsKORhuov9Yyij2OnrVD\nB/cEeXp/AEm/yfiFH6xhqRUnUaYQAbH73huSKSXlUkv2X0yN6rCHCcy6BDznMfjs\n1iSckBEyuu/BXeuHG/wnsYX06AED1MPhW2tAwMh3MP2Kj/goL8U6Ij23+83rSbgX\nZGC8inDC+NFT5J+afoCh/HO/+yRx25jt8TZmQvpxsrGtXvt14rQhfKzRcGLKb0oe\nZ8YWYKeqoXIKvEIrXRVJHABuSUb5TViSYzuc6Ir8/kqt5moq7JjFA0rM+032OaVc\n3Z3XPGm1dZ2gsTNMKM1tdsO+3CnLlUAK3g==\n-----END CERTIFICATE-----";

        let client_private_key = "-----BEGIN RSA PRIVATE KEY-----\nMIIEpAIBAAKCAQEA+YP+8o++9DQouQf37GlQVI2yBFXk7L+g9bnQlxAJSmocHy5S\nuiKfns+HSqd5iWSY4xAnD3OHlYxng9CQXRccJC6/YQfTkmKFxpyXnZW/kzs1yWiv\nigJ+uyY1B4+/6vDmLYo4Df1EgiYhbodPgYC7buPMKAfwLPuwZi8Hg+D7jKD2s64y\ninUWtf/ddLtBGnK5FXJSlaWV3KMHKJt6BijMKN/6rhRoXWSObCZPSFLFdsyAoIwE\nzROPnXv1swjSVkIwEJgSuMC8vXDikwHJGdT4RPFyBMlu9zcxUDR5Ak1f7ot6Pwd2\nlhPg/4lXjHuDLz2YSTVrxyQjaH+NvAUzFWJYLwIDAQABAoIBAQCONFtOFPzIox1+\nbvsuosrklakabXW+NGzg/xjRr5ML9TO31afSa787PJ2nv5E1675y0pbgaICii9XH\nO0u7slsYiAgMnfBH4pzJmB+U8W6w07MQ6ff5mPhvYxQgDh5cIRWeaMMPvgOYhXDS\nVI3MifjI9004l2WbzYo4gp8u2z+iYk6AYCNy8iJMp/P23Lm8HEvvwyVq0EW3hGXM\n9Ed5oWkW5gjdhylqXUQPP9s0nY3HpF/9p/rYgYWrpgyn9LRCYOaQmrTesoWLb8GY\nW59zNe5qOlTxWkD9qveibd7x6jcL3/0juRsqdJpwpjXxetQGmjLRNH8mx8N0FQjp\nVYISXsjpAoGBAP6JTZt2oXL+51dGbp45VU9Mud90fvLCfqOEgDd2az3aYdr4Ab8E\nRzGc8RI+ixsQ6d2yhR/d3lzuHwNl6KpngYSajagNv06EwdLVIoly47eoRcmaEAlE\nSWrqXuMY+shPSLlO5KeXqz/dKsV+LIOD3E1G6TZNyiN/SdvrLPxnyEl7AoGBAPrz\nTUUsOr205pwblV9iHmgeP++2jeo2d/FkFywRTq6paKb4FSZd0ZN4+skGnzfR7Bjr\nYau1NuWECp9JbAp3lvGQ8L0cXAtXKvyT0Kax3Wm09mYC+bK8wDAIwwJLKTOry9ok\nTJ/+JJruA86gPI0ojSCu8f0SRr7VkenyW3aF5evdAoGAMuLkPwZSdJj9Svdrufog\nUgA20LOLhaDYjHw63duwyObV1V7rinKigQqtL0aNrNWOy6Ga96n1gIKidJ11DEwx\nGn+DfmtxKZNk5G9zviLX36mmeg1w00lxnAxK9//QcydWlKVvFQo/VD81A9Kbt5cu\n/cwFZ7PZi4sxCuRTVAqzge0CgYEAnJuntipzAh7Z58QjBOKTvUBbgDp5+BdD5QYk\nm+C1LLUWVVTuxgG4n4LZZwjV5h0AbVC/pEuz1aoAgwVsAmA9d8WPJ0WCf6VHc1a/\n2LeZSLWhK2ph79RxT8i4Aj9rmA53akxK8XHF4FX3VESVZTZQVHw5EkkMk11u8QPJ\nZn8LTJUCgYB11sq+WFD8rPcGK228XTi0uSROdRfQ7lObGGNcq2f0v9QiheFYOuAv\n+7CkaQJ3+xSzParMzUZ1P+FGDb6poQskgu+dbhuLGqZY+RjgupH5CW4np6xXK986\nz22DeBxa7RTIHE1wYifUw+uH+iA3qawdSosyqpegSPKBCLT1LPSzyg==\n-----END RSA PRIVATE KEY-----";
        
        let client_invocation_sender = oak::http::client::init_credentialed("", (client_certificate.to_string(), client_private_key.to_string())).unwrap();
        let label = oak_abi::label::Label::public_untrusted();
        //let label = confidentiality_label(tls_endpoint_tag(authority));
        let (client_invocation, client_invocation_source) = create_http_invocation(&label).unwrap();
        info!("sending client_invocation to client_invocation_sender");
        client_invocation_sender.send(&client_invocation).unwrap();
        info!("Sending request to client_invocation_source");
        match client_invocation_source.send(request) {
            Ok(whatisthis) => info!("Send Ok:{:?}", whatisthis),
            Err(err) => info!("Send Err:{:?}", err),
        }
        info!("Receiving through client_invocation_source");
        match client_invocation_source.receive() {
            Ok(whatisthis) => info!("Receive Ok:{:?}", whatisthis),
            Err(err) => info!("Receive Err:{:?}", err),
        }

        result.status = 0;

        Ok(result)
    }

}
