//
// Copyright 2025 The Project Oak Authors
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

// We are not actually no_std because the jni crate is pulling it in, but at
// least this enforces that this lib isn't using anything from the std lib
#![no_std]

extern crate alloc;

use alloc::{boxed::Box, format};

use jni::{
    JNIEnv,
    objects::JClass,
    sys::{jint, jlong},
};
use oak_session::{attestation::AttestationType, config::SessionConfig, handshake::HandshakeType};

macro_rules! exception {
    ($env:ident, $message:tt) => {
        $env.throw_new("com/google/oak/session/OakSessionException", format!($message))
            .expect($message);
    };
}

#[unsafe(no_mangle)]
extern "system" fn Java_com_google_oak_session_OakSessionConfigBuilder_nativeCreateConfigBuilder(
    env: JNIEnv,
    _class: JClass,
    attestation_type_java: jint,
    handshake_type_java: jint,
) -> jlong {
    let mut env = env;
    let attestation_type = match attestation_type_java {
        0 => AttestationType::Bidirectional,
        1 => AttestationType::SelfUnidirectional,
        2 => AttestationType::PeerUnidirectional,
        3 => AttestationType::Unattested,
        _ => {
            exception!(
                env,
                "Invalid attestation type ordinal {attestation_type_java}. This is a library bug."
            );
            return 0;
        }
    };

    let handshake_type = match handshake_type_java {
        0 => HandshakeType::NoiseKK,
        1 => HandshakeType::NoiseKN,
        2 => HandshakeType::NoiseNK,
        3 => HandshakeType::NoiseNN,
        _ => {
            exception!(
                env,
                "Invalid handshake type ordinal {handshake_type_java}. This is a library bug."
            );
            return 0;
        }
    };

    Box::into_raw(Box::new(SessionConfig::builder(attestation_type, handshake_type))) as jlong
}
