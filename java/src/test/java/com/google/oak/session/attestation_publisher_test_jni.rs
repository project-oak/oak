//
// Copyright 2023 The Project Oak Authors
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

//! Test data used by the Java AttestationPublisherTest

use std::sync::Arc;

use jni::{
    objects::{JClass, JObject, JValue},
    sys::{jlong, jobject},
    JNIEnv,
};
use oak_jni_attestation_publisher::JNIAttestationPublisher;
use oak_proto_rust::oak::{
    attestation::v1::{Assertion, Endorsements, EventLog, Evidence},
    session::v1::SessionBinding,
    Variant,
};
use oak_sdk_common::{StaticAttester, StaticEndorser};
use oak_session::{
    attestation::AttestationType,
    config::{SessionConfig, SessionConfigBuilder},
    generator::{BindableAssertion, BindableAssertionGenerator, BindableAssertionGeneratorError},
    handshake::HandshakeType,
    session::AttestationPublisher,
    session_binding::SessionBinder,
};

pub fn new_java_session_config_builder(
    env: &mut JNIEnv,
    session_config_builder: SessionConfigBuilder,
) -> jobject {
    let builder_ptr = Box::into_raw(Box::new(session_config_builder));
    let cls = env
        .find_class("com/google/oak/session/OakSessionConfigBuilder")
        .expect("Failed to find class OakSessionConfigBuilder");

    env.new_object(cls, "(J)V", &[JValue::Long(builder_ptr as jlong)])
        .expect("Failed to call OakSessionConfigBuilder constructor")
        .as_raw()
}

struct FakeBindableAssertion {
    assertion: Assertion,
}

impl FakeBindableAssertion {
    fn new() -> Self {
        Self { assertion: Assertion { content: b"fake assertion".to_vec() } }
    }
}

impl BindableAssertion for FakeBindableAssertion {
    fn assertion(&self) -> &Assertion {
        &self.assertion
    }

    fn bind(&self, _: &[u8]) -> Result<SessionBinding, BindableAssertionGeneratorError> {
        Ok(SessionBinding { binding: vec![] })
    }
}

struct FakeBindableAssertionGenerator {}

impl BindableAssertionGenerator for FakeBindableAssertionGenerator {
    fn generate(&self) -> Result<Box<dyn BindableAssertion>, BindableAssertionGeneratorError> {
        Ok(Box::new(FakeBindableAssertion::new()))
    }
}

struct FakeSessionBinder {}

impl SessionBinder for FakeSessionBinder {
    fn bind(&self, bound_data: &[u8]) -> Vec<u8> {
        bound_data.to_vec()
    }
}

#[no_mangle]
extern "system" fn Java_com_google_oak_session_AttestationPublisherTest_nativeCreateServerConfigBuilder(
    mut env: JNIEnv,
    _class: JClass,
) -> jobject {
    let evidence = Evidence {
        root_layer: None,
        application_keys: None,
        event_log: Some(EventLog { encoded_events: vec![b"fake event".to_vec()] }),
        layers: vec![],
        transparent_event_log: None,
        signed_user_data_certificate: None,
    };

    let endorsement = Variant { id: b"testing".to_vec(), value: b"fake endorsement".to_vec() };

    let endorsements =
        Endorsements { r#type: None, events: vec![endorsement], initial: None, platform: None };
    let assertion_generator = FakeBindableAssertionGenerator {};

    new_java_session_config_builder(
        &mut env,
        SessionConfig::builder(AttestationType::SelfUnidirectional, HandshakeType::NoiseNN)
            .add_self_attester("test id".to_string(), Box::new(StaticAttester::new(evidence)))
            .add_self_endorser("test id".to_string(), Box::new(StaticEndorser::new(endorsements)))
            .add_session_binder("test id".to_string(), Box::new(FakeSessionBinder {}))
            .add_self_assertion_generator("test id".to_string(), Box::new(assertion_generator)),
    )
}

#[no_mangle]
extern "system" fn Java_com_google_oak_session_AttestationPublisherTest_nativeCreateClientConfigBuilder(
    mut env: JNIEnv,
    _class: JClass,
    java_publisher_object: JObject,
) -> jobject {
    let publisher: Arc<dyn AttestationPublisher> = Arc::new(
        JNIAttestationPublisher::new(&env, &java_publisher_object)
            .expect("failed to create attestation publisher"),
    );

    new_java_session_config_builder(
        &mut env,
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_attestation_publisher(&publisher),
    )
}
