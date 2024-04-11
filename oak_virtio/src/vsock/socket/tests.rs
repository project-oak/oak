//
// Copyright 2022 The Project Oak Authors
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

use alloc::{alloc::Global, vec};

use rand::RngCore;
use rust_hypervisor_firmware_virtio::device::VirtioBaseDevice;

use super::*;
use crate::{
    test::{identity_map, inverse_identity_map, new_valid_transport, TestingTransport},
    vsock::{HOST_CID, QUEUE_SIZE},
};

const GUEST_CID: u64 = 3;
const HOST_PORT: u32 = 1111;
const GUEST_PORT: u32 = 2222;

#[test]
fn test_socket_accept() {
    let (vsock, transport) = new_vsock_and_transport();
    let mut packet = Packet::new_control(HOST_PORT, GUEST_PORT, VSockOp::Request).unwrap();
    set_packet_cids_host_to_guest(&mut packet);
    transport.device_write_to_queue::<QUEUE_SIZE>(0, packet.as_slice());
    let listener = SocketListener::new(vsock, GUEST_PORT);
    let socket = listener.accept().unwrap();
    assert_eq!(socket.connection_state, ConnectionState::Connected);
    let response =
        Packet::new(transport.device_read_once_from_queue::<QUEUE_SIZE>(1).unwrap()).unwrap();
    assert_eq!(response.get_op().unwrap(), VSockOp::Response);
}

#[test]
fn test_socket_accept_invalid() {
    let (vsock, transport) = new_vsock_and_transport();
    let mut packet = Packet::new_control(HOST_PORT, GUEST_PORT, VSockOp::Response).unwrap();
    set_packet_cids_host_to_guest(&mut packet);
    transport.device_write_to_queue::<QUEUE_SIZE>(0, packet.as_slice());
    let listener = SocketListener::new(vsock, GUEST_PORT);
    assert!(listener.accept().is_err());
}

#[test]
fn test_socket_connect() {
    let (vsock, transport) = new_vsock_and_transport();
    let connector = SocketConnector::new(vsock, HOST_PORT, GUEST_PORT);
    let mut packet = Packet::new_control(HOST_PORT, GUEST_PORT, VSockOp::Response).unwrap();
    set_packet_cids_host_to_guest(&mut packet);

    // Send the reesponse beforehand because the connector blocks.
    transport.device_write_to_queue::<QUEUE_SIZE>(0, packet.as_slice());
    let socket = connector.connect().unwrap();
    assert_eq!(socket.connection_state, ConnectionState::Connected);

    // Read the original request from the queue and validate.
    let request =
        Packet::new(transport.device_read_once_from_queue::<QUEUE_SIZE>(1).unwrap()).unwrap();
    assert_eq!(request.get_op().unwrap(), VSockOp::Request);
}

#[test]
fn test_socket_connect_invalid() {
    let (vsock, transport) = new_vsock_and_transport();
    let connector = SocketConnector::new(vsock, HOST_PORT, GUEST_PORT);
    let mut packet = Packet::new_control(HOST_PORT, GUEST_PORT, VSockOp::Request).unwrap();
    set_packet_cids_host_to_guest(&mut packet);
    // Send the reesponse beforehand because the connector blocks.
    transport.device_write_to_queue::<QUEUE_SIZE>(0, packet.as_slice());
    assert!(connector.connect().is_err());
}

#[test]
fn test_read_exact() {
    let data = [3; 17];
    let mut packet = Packet::new_data(&data[..], HOST_PORT, GUEST_PORT).unwrap();
    set_packet_cids_host_to_guest(&mut packet);
    let mut first = [0; 11];
    let mut second = [0; 2];
    let (mut socket, transport) = new_socket_and_transport();
    transport.device_write_to_queue::<QUEUE_SIZE>(0, packet.as_slice());
    assert!(socket.read_exact(&mut first).is_ok());
    assert!(socket.read_exact(&mut second).is_ok());
    assert_eq!(&data[..11], &first[..]);
    assert_eq!(&data[11..13], &second[..]);
    assert!(socket.pending_data.is_some());
    assert_eq!(socket.pending_data.unwrap().len(), 4);
}

#[test]
fn test_write_all() {
    // Send data larger than the max payload size, so we expect 2 packets.
    let data = [31; 5000];
    let (mut socket, transport) = new_socket_and_transport();
    assert!(socket.write_all(&data[..]).is_ok());
    let first =
        Packet::new(transport.device_read_once_from_queue::<QUEUE_SIZE>(1).unwrap()).unwrap();
    let second =
        Packet::new(transport.device_read_once_from_queue::<QUEUE_SIZE>(1).unwrap()).unwrap();
    assert_eq!(first.get_dst_cid(), HOST_CID);
    assert_eq!(first.get_src_cid(), GUEST_CID);
    assert_eq!(first.get_dst_port(), HOST_PORT);
    assert_eq!(first.get_src_port(), GUEST_PORT);
    assert_eq!(&data[..MAX_PAYLOAD_SIZE], first.get_payload());
    assert_eq!(second.get_dst_cid(), HOST_CID);
    assert_eq!(second.get_src_cid(), GUEST_CID);
    assert_eq!(second.get_dst_port(), HOST_PORT);
    assert_eq!(second.get_src_port(), GUEST_PORT);
    assert_eq!(&data[MAX_PAYLOAD_SIZE..], second.get_payload());
}

#[test]
fn test_many_echos() {
    const DATA_LEN: usize = 47;
    let (mut socket, transport) = new_socket_and_transport();
    let mut rng = rand::thread_rng();
    for i in 0..1000 {
        let mut data = vec![0; DATA_LEN];
        rng.fill_bytes(&mut data);
        // Write packet from device to host.
        let mut packet = Packet::new_data(&data[..], HOST_PORT, GUEST_PORT).unwrap();
        set_packet_cids_host_to_guest(&mut packet);
        // Ensure credit info is valid.
        packet.set_buf_alloc(50);
        packet.set_fwd_cnt(i * DATA_LEN as u32);
        let mut buffer = vec![0; DATA_LEN];
        transport.device_write_to_queue::<QUEUE_SIZE>(0, packet.as_slice());
        assert!(socket.read_exact(&mut buffer).is_ok());

        // Echo back.
        assert!(socket.write_all(&buffer[..]).is_ok());
        let output =
            Packet::new(transport.device_read_once_from_queue::<QUEUE_SIZE>(1).unwrap()).unwrap();
        assert_eq!(output.get_payload(), &data[..]);
    }
}

fn set_packet_cids_host_to_guest(packet: &mut Packet) {
    packet.set_dst_cid(GUEST_CID);
    packet.set_src_cid(HOST_CID);
}

fn new_vsock_and_transport() -> (VSock<'static, TestingTransport, Global>, TestingTransport) {
    let transport = new_valid_transport();
    transport.write_device_config(0, GUEST_CID as u32);

    let device = VirtioBaseDevice::new(transport.clone());
    let mut vsock = VSock::new(device, identity_map, &Global);
    vsock.init(identity_map, inverse_identity_map).unwrap();

    (vsock, transport)
}

fn new_socket_and_transport() -> (Socket<'static, TestingTransport, Global>, TestingTransport) {
    let (vsock, transport) = new_vsock_and_transport();
    let mut packet = Packet::new_control(HOST_PORT, GUEST_PORT, VSockOp::Request).unwrap();
    set_packet_cids_host_to_guest(&mut packet);
    // Reports a large enough stream buffer from the peer.
    packet.set_buf_alloc(10000);
    transport.device_write_to_queue::<QUEUE_SIZE>(0, packet.as_slice());
    let listener = SocketListener::new(vsock, GUEST_PORT);
    let socket = listener.accept().unwrap();
    // Take the response packet from the queue.
    let response =
        Packet::new(transport.device_read_once_from_queue::<QUEUE_SIZE>(1).unwrap()).unwrap();
    assert_eq!(response.get_op().unwrap(), VSockOp::Response);

    (socket, transport)
}
