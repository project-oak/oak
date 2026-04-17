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

use jni::{
    JNIEnv, JavaVM,
    errors::Result,
    objects::{GlobalRef, JObject},
};
use oak_time::{Clock as AttestationClock, Instant};

// An implementation of oak_attestation_type::util::Clock that gets time from a
// Java-provided class.
//
// This should be constructed in other Rust-JNI functions that would like
// to construct attestation-related components that require a clock.
//
// The calling function should provide a
// java.com.google.oak.remote_attestation.AttestationClock implementation to the
// constructor which this implementation wraps.
pub struct JNIClock {
    jni_vm: JavaVM,
    jni_instance: GlobalRef,
}

impl JNIClock {
    /// Create a new JNIClock instance.
    ///
    /// Typically, this will be called from a JNI method exposed to Java, and
    /// the JNIENV argument provided to that method call will be passed here.
    ///
    /// The Java caller provides an
    /// java.com.google.oak.remote_attestation.AttestationClock instance, and
    /// this code holds a global reference to it, and uses it to get the
    /// current time from JVM.
    ///
    /// ```
    /// #[no_mangle]
    /// fn Java_com_example_make_rust_jni_clock(
    ///     env: JNIEnv,
    ///     _class: JClass,
    ///     java_clock_impl: JObject,
    /// ) -> jlong {
    ///     let jni_clock = oak_jni_attestation_clock::JNIClock::new(&env, &java_clock_impl)
    ///         .expect("Failed to create clock");
    ///
    ///     Box::into_raw(Box::new(jni_clock)) as jlong
    /// }
    /// ```
    pub fn new(env: &JNIEnv, local_instance: &JObject) -> Result<Self> {
        Ok(Self { jni_vm: env.get_java_vm()?, jni_instance: env.new_global_ref(local_instance)? })
    }
}

impl AttestationClock for JNIClock {
    fn get_time(&self) -> Instant {
        // Attaching an already attached thread is a no-op, so this should not be too
        // expensive for typical use cases.
        // If this fails, we can't do anything but bail, since we won't even have an env
        // for throwing exceptions.
        let mut attached = self.jni_vm.attach_current_thread().expect("Failed to attach to VM");

        let result =
            match attached.call_method(&self.jni_instance, "millisecondsSinceEpoch", "()J", &[]) {
                Ok(r) => r,
                Err(_) => {
                    // An exception will have been thrown.
                    return Instant::UNIX_EPOCH;
                }
            };
        Instant::from_unix_millis(result.j().expect("Failed to unwrap as long"))
    }
}
