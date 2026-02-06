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

use std::collections::BTreeMap;

use anyhow::Context;
use jni::{
    JNIEnv, JavaVM,
    errors::Result,
    objects::{GlobalRef, JMap, JObject},
};
use oak_session::session::{AttestationEvidence, AttestationPublisher};

// An implementation of oak_session::attestation::AttestationPublisher that
// calls out to a JVM-provided implementation.
//
// The calling function should provide a
// java.com.google.oak.session.AttestationPublisher implementation to the
// constructor which this implementation wraps.
pub struct JNIAttestationPublisher {
    jni_vm: JavaVM,
    jni_instance: GlobalRef,
}

impl JNIAttestationPublisher {
    /// Create a new JNIAttestationPublisher instance.
    ///
    /// This must be called from a JNI method exposed to Java, and
    /// the JNIEnv argument provided to that method call will be passed here.
    ///
    /// The Java caller provides an
    /// java.com.google.oak.session.AttestationPublisher instance, and
    /// this code holds a global reference to it, and uses it to get the
    /// current time from JVM.
    ///
    /// ```
    /// #[no_mangle]
    /// fn Java_com_example_make_rust_jni_attestation_publisher(
    ///     env: JNIEnv,
    ///     _class: JClass,
    ///     java_impl: JObject,
    /// ) -> jlong {
    ///     let jni_publisher =
    ///         oak_jni_attestation_publisher::JNIAttestationPublisher::new(&env, &java_impl)
    ///             .expect("Failed to create publisher");
    ///
    ///     Box::into_raw(Box::new(jni_publisher)) as jlong
    /// }
    /// ```
    pub fn new(env: &JNIEnv, local_instance: &JObject) -> Result<Self> {
        Ok(Self { jni_vm: env.get_java_vm()?, jni_instance: env.new_global_ref(local_instance)? })
    }

    fn convert_map<M: prost::Message>(&self, rust_map: &BTreeMap<String, M>) -> Result<JObject> {
        let mut attached = self.jni_vm.attach_current_thread()?;
        let map: JObject = attached.new_object("java/util/HashMap", "()V", &[])?;
        let jmap: JMap = attached.get_map(&map)?;
        for (id, m) in rust_map {
            let java_id = attached.new_string(id)?;
            let encoded_m = m.encode_to_vec();
            let java_encoded_m = attached.byte_array_from_slice(encoded_m.as_slice())?;
            jmap.put(&mut attached, &java_id, &java_encoded_m)?;
        }
        Ok(map)
    }

    fn publish_impl(&self, attestation_evidence: AttestationEvidence) -> anyhow::Result<()> {
        // Attaching an already attached thread is a no-op, so this should not be too
        // expensive for typical use cases.
        // If this fails, we can't do anything but bail, since we won't even have an env
        // for throwing exceptions.
        let mut attached = self.jni_vm.attach_current_thread().context("failed to attach to VM")?;

        let ee_map = self.convert_map(&attestation_evidence.evidence)?;
        let bindings_map = self.convert_map(&attestation_evidence.evidence_bindings)?;
        let handshake_hash =
            attached.byte_array_from_slice(attestation_evidence.handshake_hash.as_slice())?;

        // Call the java method with our converted maps.
        attached
            .call_method(
                &self.jni_instance,
                "publish",
                "(Ljava/util/Map;Ljava/util/Map;[B)V",
                &[(&ee_map).into(), (&bindings_map).into(), (&handshake_hash).into()],
            )
            .map_err(|e| anyhow::anyhow!("Failed to invoke JVM publish: {e:?}"))?;

        Ok(())
    }
}

impl AttestationPublisher for JNIAttestationPublisher {
    fn publish(&self, attesation_evidence: AttestationEvidence) {
        if let Err(e) = self.publish_impl(attesation_evidence) {
            eprintln!("Failed to publish: {e:?}");
        }
    }
}
