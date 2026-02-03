// We are not actually no_std because the jni crate is pulling it in, but at
// least this enforces that this lib isn't using anything from the std lib

extern crate alloc;

use alloc::{boxed::Box, format};
use core::{fmt::Debug, ptr::null_mut};

use jni::{
    objects::{JByteArray, JClass},
    sys::{jboolean, jbyteArray, jlong},
    JNIEnv,
};
use oak_proto_rust::oak::session::v1::{PlaintextMessage, SessionRequest};
use oak_session::{config::SessionConfigBuilder, ProtocolEngine, ServerSession, Session};
use prost::Message;

fn oak_exception<Error: Debug>(mut env: JNIEnv, message: &str, err: Error) {
    env.throw_new("com/google/oak/session/OakSessionException", format!("{message}: {err:?}"))
        .expect(message);
}

#[unsafe(no_mangle)]
extern "system" fn Java_com_google_oak_session_OakServerSession_nativeCreateServerSession(
    env: JNIEnv,
    _class: JClass,
    config_builder_ptr: jlong,
) -> jlong {
    // Safety: OakServerSession.java will only pass valid pointers.
    let config_builder: Box<SessionConfigBuilder> =
        unsafe { Box::from_raw(config_builder_ptr as *mut SessionConfigBuilder) };
    match ServerSession::create(config_builder.build()) {
        Ok(session) => Box::into_raw(Box::new(session)) as jlong,
        Err(err) => {
            oak_exception(env, "Couldn't create a native session", err);
            0
        }
    }
}

#[unsafe(no_mangle)]
extern "system" fn Java_com_google_oak_session_OakServerSession_nativePutIncomingMessage(
    env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
    session_request_message: JByteArray,
) -> jboolean {
    // Safety: OakServerSession.java will only pass valid pointers.
    let session: &mut ServerSession = unsafe { &mut *(native_ptr as *mut ServerSession) };

    let byte_array = match env.convert_byte_array(&session_request_message) {
        Ok(array) => array,
        Err(err) => {
            oak_exception(env, "Error getting byte array elements", err);
            return false as jboolean;
        }
    };

    let incoming_message: SessionRequest = match Message::decode(byte_array.as_slice()) {
        Ok(incoming_message) => incoming_message,
        Err(err) => {
            oak_exception(env, "Error parsing the SessionRequest message", err);
            return false as jboolean;
        }
    };

    match session.put_incoming_message(incoming_message) {
        Ok(result) => result.is_some() as jboolean,
        Err(err) => {
            oak_exception(env, "Error processing the incoming message", err);
            false as jboolean
        }
    }
}

#[unsafe(no_mangle)]
extern "system" fn Java_com_google_oak_session_OakServerSession_nativeGetOutgoingMessage(
    env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
) -> jbyteArray {
    // Safety: OakServerSession.java will only pass valid pointers.
    let session: &mut ServerSession = unsafe { &mut *(native_ptr as *mut ServerSession) };

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

#[unsafe(no_mangle)]
extern "system" fn Java_com_google_oak_session_OakServerSession_nativeIsSessionOpen(
    _env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
) -> jboolean {
    // Safety: OakServerSession.java will only pass valid pointers.
    let session: &mut ServerSession = unsafe { &mut *(native_ptr as *mut ServerSession) };
    session.is_open() as jboolean
}

#[unsafe(no_mangle)]
extern "system" fn Java_com_google_oak_session_OakServerSession_nativeRead(
    env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
) -> jbyteArray {
    // Safety: OakServerSession.java will only pass valid pointers.
    let session: &mut ServerSession = unsafe { &mut *(native_ptr as *mut ServerSession) };
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

#[unsafe(no_mangle)]
extern "system" fn Java_com_google_oak_session_OakServerSession_nativeWrite(
    env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
    message: JByteArray,
) {
    // Safety: OakServerSession.java will only pass valid pointers.
    let session: &mut ServerSession = unsafe { &mut *(native_ptr as *mut ServerSession) };

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

    if let Err(err) = session.write(message) {
        oak_exception(env, "Error writing the data to the session", err);
    }
}

#[unsafe(no_mangle)]
extern "system" fn Java_com_google_oak_session_OakServerSession_nativeGetSessionBindingToken(
    env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
    info_byte_array: JByteArray,
) -> jbyteArray {
    let session: &mut ServerSession = unsafe { &mut *(native_ptr as *mut ServerSession) };

    let info = match env.convert_byte_array(&info_byte_array) {
        Ok(info) => info,
        Err(err) => {
            oak_exception(env, "Error getting byte array elements", err);
            return null_mut();
        }
    };

    match session.get_session_binding_token(info.as_slice()) {
        Ok(token) => match env.byte_array_from_slice(token.as_slice()) {
            Ok(token) => token.into_raw(),
            Err(err) => {
                oak_exception(env, "Failed to create byte array", err);
                null_mut()
            }
        },
        Err(err) => {
            oak_exception(env, "Failed to get session binding token", err);
            null_mut()
        }
    }
}

#[unsafe(no_mangle)]
extern "system" fn Java_com_google_oak_session_OakServerSession_nativeClose(
    _env: JNIEnv,
    _class: JClass,
    native_ptr: jlong,
) {
    // Safety: OakServerSession.java will only pass valid pointers.
    drop(unsafe { Box::from_raw(&mut *(native_ptr as *mut ServerSession)) });
}
