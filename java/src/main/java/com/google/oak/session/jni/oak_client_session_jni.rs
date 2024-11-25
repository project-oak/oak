// We are not actually no_std because the jni crate is pulling it in, but at
// least this enforces that this lib isn't using anything from the std lib
#![no_std]

extern crate alloc;

use alloc::{boxed::Box, format};
use core::{fmt::Debug, ptr::null_mut};

use jni::{
    objects::{JByteArray, JClass},
    sys::{jboolean, jbyteArray, jlong},
    JNIEnv,
};
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionResponse};
use oak_session::{
    attestation::AttestationType, config::SessionConfig, handshake::HandshakeType, ClientSession,
    ProtocolEngine, Session,
};
use prost::Message;

fn oak_exception<Error: Debug>(mut env: JNIEnv, message: &str, err: Error) {
    env.throw_new("com/google/oak/session/OakSessionException", format!("{message}: {err:?}"))
        .expect(message);
}

#[no_mangle]
extern "system" fn Java_com_google_oak_session_OakClientSession_nativeCreateClientSessionUnattested(
    env: JNIEnv,
    _class: JClass,
) -> jlong {
    let config =
        SessionConfig::builder(AttestationType::Unattested, HandshakeType::NoiseNN).build();
    match ClientSession::create(config) {
        Ok(session) => Box::into_raw(Box::new(session)) as jlong,
        Err(err) => {
            oak_exception(env, "Couldn't create a native session", err);
            0
        }
    }
}

#[no_mangle]
extern "system" fn Java_com_google_oak_session_OakClientSession_nativePutIncomingMessage(
    env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
    message: JByteArray,
) -> jboolean {
    let session: &mut ClientSession = unsafe { &mut *(native_ptr as *mut ClientSession) };

    let byte_array = match env.convert_byte_array(&message) {
        Ok(array) => array,
        Err(err) => {
            oak_exception(env, "Error getting byte array elements", err);
            return false as jboolean;
        }
    };

    let incoming_message: SessionResponse = match Message::decode(byte_array.as_slice()) {
        Ok(incoming_message) => incoming_message,
        Err(err) => {
            oak_exception(env, "Error parsing the SessionResponse message", err);
            return false as jboolean;
        }
    };

    match session.put_incoming_message(&incoming_message) {
        Ok(result) => result.is_some() as jboolean,
        Err(err) => {
            oak_exception(env, "Error processing the incoming message", err);
            false as jboolean
        }
    }
}

#[no_mangle]
extern "system" fn Java_com_google_oak_session_OakClientSession_nativeGetOutgoingMessage(
    env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
) -> jbyteArray {
    let session: &mut ClientSession = unsafe { &mut *(native_ptr as *mut ClientSession) };

    match session.get_outgoing_message() {
        Ok(Some(message)) => match env.byte_array_from_slice(message.encode_to_vec().as_slice()) {
            Ok(result) => result.into_raw(),
            Err(err) => {
                oak_exception(env, "Error creating a Java byte array", err);
                null_mut()
            }
        },
        Ok(None) => null_mut(),
        Err(err) => {
            oak_exception(env, "Error processing the outgoing message", err);
            null_mut()
        }
    }
}

#[no_mangle]
extern "system" fn Java_com_google_oak_session_OakClientSession_nativeIsSessionOpen(
    _env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
) -> jboolean {
    let session: &mut ClientSession = unsafe { &mut *(native_ptr as *mut ClientSession) };
    session.is_open() as jboolean
}

#[no_mangle]
extern "system" fn Java_com_google_oak_session_OakClientSession_nativeRead(
    env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
) -> jbyteArray {
    let session: &mut ClientSession = unsafe { &mut *(native_ptr as *mut ClientSession) };
    match session.read() {
        Ok(Some(message)) => match env.byte_array_from_slice(message.encode_to_vec().as_slice()) {
            Ok(result) => result.into_raw(),
            Err(err) => {
                oak_exception(env, "Error getting byte array elements", err);
                null_mut()
            }
        },
        Ok(None) => null_mut(),
        Err(err) => {
            oak_exception(env, "Error reading the data from the session", err);
            null_mut()
        }
    }
}

#[no_mangle]
extern "system" fn Java_com_google_oak_session_OakClientSession_nativeWrite(
    env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
    message: JByteArray,
) {
    let session: &mut ClientSession = unsafe { &mut *(native_ptr as *mut ClientSession) };

    let byte_array = match env.convert_byte_array(&message) {
        Ok(array) => array,
        Err(err) => {
            oak_exception(env, "Error getting byte array elements", err);
            return;
        }
    };

    let message: PlaintextMessage = match Message::decode(byte_array.as_slice()) {
        Ok(message) => message,
        Err(err) => {
            oak_exception(env, "Error parsing the PlaintextMessage", err);
            return;
        }
    };

    if let Err(err) = session.write(&message) {
        oak_exception(env, "Error writing the data to the session", err);
    }
}

#[no_mangle]
extern "system" fn Java_com_google_oak_session_OakClientSession_nativeClose(
    _env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
) {
    drop(unsafe { Box::from_raw(&mut *(native_ptr as *mut ClientSession)) });
}
