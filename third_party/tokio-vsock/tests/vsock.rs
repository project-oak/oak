/*
 * Copyright 2019 fsyncd, Berlin, Germany.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use rand::RngCore;
use sha2::{Digest, Sha256};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio_vsock::{VsockAddr, VsockListener, VsockStream};

const TEST_BLOB_SIZE: usize = 100_000;
const TEST_BLOCK_SIZE: usize = 5_000;

/// A simple test for the tokio-vsock implementation.
/// Generate a large random blob of binary data, and transfer it in chunks over the VsockStream
/// interface. The vm enpoint is running a simple echo server, so for each chunk we will read
/// it's reply and compute a checksum. Comparing the data sent and received confirms that the
/// vsock implementation does not introduce corruption and properly implements the interface
/// semantics.
#[tokio::test]
async fn test_vsock_server() {
    let mut rng = rand::thread_rng();
    let mut blob: Vec<u8> = vec![];
    let mut rx_blob = vec![];
    let mut tx_pos = 0;

    blob.resize(TEST_BLOB_SIZE, 0);
    rx_blob.resize(TEST_BLOB_SIZE, 0);
    rng.fill_bytes(&mut blob);

    let addr = VsockAddr::new(3, 8000);
    let mut stream = VsockStream::connect(addr).await.expect("connection failed");

    while tx_pos < TEST_BLOB_SIZE {
        let written_bytes = stream
            .write(&blob[tx_pos..tx_pos + TEST_BLOCK_SIZE])
            .await
            .expect("write failed");
        if written_bytes == 0 {
            panic!("stream unexpectedly closed");
        }

        let mut rx_pos = tx_pos;
        while rx_pos < (tx_pos + written_bytes) {
            let read_bytes = stream
                .read(&mut rx_blob[rx_pos..])
                .await
                .expect("read failed");
            if read_bytes == 0 {
                panic!("stream unexpectedly closed");
            }
            rx_pos += read_bytes;
        }

        tx_pos += written_bytes;
    }

    let expected = Sha256::digest(&blob);
    let actual = Sha256::digest(&rx_blob);

    assert_eq!(expected, actual);
}

#[tokio::test]
async fn test_vsock_conn_error() {
    let addr = VsockAddr::new(3, 8001);
    let err = VsockStream::connect(addr)
        .await
        .expect_err("connection succeeded")
        .raw_os_error()
        .expect("not an OS error");

    if err == 0 {
        panic!("non-zero error expected");
    }
}

/// This test was taken from tokio/tests/tcp_split.rs and adapted to fit the Vsock API
///
/// source: https://github.com/tokio-rs/tokio/blob/fc9518b62714daac9a38b46c698b94ac5d5b1ca2/tokio/tests/tcp_split.rs
#[tokio::test]
async fn split_vsock() {
    const MSG: &[u8] = b"split";
    const PORT: u32 = 8002;

    let addr = VsockAddr::new(tokio_vsock::VMADDR_CID_LOCAL, PORT);
    let mut listener = VsockListener::bind(addr).expect("connection failed");

    let handle = tokio::task::spawn(async move {
        let (mut stream, _) = listener
            .accept()
            .await
            .expect("failed to accept connection");
        stream
            .write_all(MSG)
            .await
            .expect("failed to write to vsock from task");

        let mut read_buf = [0u8; 32];
        let read_len = stream
            .read(&mut read_buf)
            .await
            .expect("failed to read data");
        assert_eq!(&read_buf[..read_len], MSG);
    });

    let mut stream = VsockStream::connect(addr).await.expect("connection failed");
    let (mut read_half, mut write_half) = stream.split();

    let mut read_buf = [0u8; 32];
    let read_len = read_half
        .read(&mut read_buf[..])
        .await
        .expect("failed to read from vsock");
    assert_eq!(&read_buf[..read_len], MSG);

    assert_eq!(
        write_half
            .write(MSG)
            .await
            .expect("failed to write to vsock"),
        MSG.len()
    );
    handle.await.expect("failed to join task");
}

/// This test was taken from tokio/tests/tcp_split.rs and adapted to fit the Vsock API
///
/// source: https://github.com/tokio-rs/tokio/blob/fc9518b62714daac9a38b46c698b94ac5d5b1ca2/tokio/tests/tcp_split.rs
#[tokio::test]
async fn into_split_vsock() {
    const MSG: &[u8] = b"split";
    const PORT: u32 = 8001;

    let addr = VsockAddr::new(tokio_vsock::VMADDR_CID_LOCAL, PORT);
    let mut listener = VsockListener::bind(addr).expect("connection failed");

    let handle = tokio::task::spawn(async move {
        let (mut stream, _) = listener
            .accept()
            .await
            .expect("failed to accept connection");
        stream
            .write_all(MSG)
            .await
            .expect("failed to write to vsock from task");

        let mut read_buf = [0u8; 32];
        let read_len = stream
            .read(&mut read_buf)
            .await
            .expect("failed to read data");
        assert_eq!(&read_buf[..read_len], MSG);
    });

    let stream = VsockStream::connect(addr).await.expect("connection failed");
    let (mut read_half, mut write_half) = stream.into_split();

    let mut read_buf = [0u8; 32];
    let read_len = read_half
        .read(&mut read_buf[..])
        .await
        .expect("failed to read from vsock");
    assert_eq!(&read_buf[..read_len], MSG);

    assert_eq!(
        write_half
            .write(MSG)
            .await
            .expect("failed to write to vsock"),
        MSG.len()
    );
    handle.await.expect("failed to join task");

    // Assert that the halfs can be merged together again
    let _ = read_half.unsplit(write_half);
}
