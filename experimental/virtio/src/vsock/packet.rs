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

//! Virtio vsock packet implementation.
//!
//! A packet consists of a header and an optional payload.
//!
//! See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-3960006>.

use alloc::{vec, vec::Vec};
use anyhow::Context;
use bitflags::bitflags;
use core::mem::size_of;
use num_enum::{IntoPrimitive, TryFromPrimitive};

/// The size of the packet header in bytes.
const HEADER_SIZE: usize = 44;
/// The offset to the src_cid field.
const SRC_CID_OFFSET: usize = 0;
/// The offset to the dst_cid field.
const DST_CID_OFFSET: usize = 8;
/// The offset to the src_port field.
const SRC_PORT_OFFSET: usize = 16;
/// The offset to the dst_port field.
const DST_PORT_OFFSET: usize = 20;
/// The offset to the len field.
const LEN_OFFSET: usize = 24;
/// The offset ot the type field.
const TYPE_OFFSET: usize = 28;
/// The offset ot the op field.
const OP_OFFSET: usize = 30;
/// The offset ot the flags field.
const FLAGS_OFFSET: usize = 32;
/// The offset ot the buf_alloc field.
const BUF_ALLOC_OFFSET: usize = 36;
/// The offset ot the fwd_cnt field.
const FWD_CNT_OFFSET: usize = 40;

pub struct Packet {
    buffer: Vec<u8>,
}

impl Packet {
    /// Creates a new `Packet` from an existing buffer.
    pub fn new(buffer: Vec<u8>) -> anyhow::Result<Self> {
        if buffer.len() < HEADER_SIZE {
            anyhow::bail!("vsock packet too short");
        }
        Ok(Self { buffer })
    }

    /// Creates a new control `Packet` with only a header.
    pub fn new_header_only() -> Self {
        Self::new_with_buffer_size(HEADER_SIZE)
    }

    /// Creates a new data `Packet` with the given payload length.
    pub fn new_with_payload(payload_len: usize) -> Self {
        let mut result = Self::new_with_buffer_size(HEADER_SIZE + payload_len);
        result.set_len(payload_len as u32);
        result.set_op(VSockOp::Rw).unwrap();
        result
    }

    /// Creates a new `Packet` with the specified buffer size.
    fn new_with_buffer_size(buffer_len: usize) -> Self {
        let buffer = vec![0u8; buffer_len];
        let mut result = Self { buffer };
        result.set_type(VSockType::Stream);
        result
    }

    /// Gets the source CID.
    pub fn get_src_cid(&self) -> u64 {
        self.read_u64(SRC_CID_OFFSET)
    }

    /// Sets the source CID.
    pub fn set_src_cid(&mut self, src_cid: u64) {
        self.write_u64(SRC_CID_OFFSET, src_cid);
    }

    /// Gets the destination CID.
    pub fn get_dst_cid(&self) -> u64 {
        self.read_u64(DST_CID_OFFSET)
    }

    /// Sets the destination CID.
    pub fn set_dst_cid(&mut self, dst_cid: u64) {
        self.write_u64(DST_CID_OFFSET, dst_cid);
    }

    /// Gets the source port.
    pub fn get_src_port(&self) -> u32 {
        self.read_u32(SRC_PORT_OFFSET)
    }

    /// Sets the source port.
    pub fn set_src_port(&mut self, src_port: u32) {
        self.write_u32(SRC_PORT_OFFSET, src_port);
    }

    /// Gets the destination port.
    pub fn get_dst_port(&self) -> u32 {
        self.read_u32(DST_PORT_OFFSET)
    }

    /// Sets the destination port.
    pub fn set_dst_port(&mut self, dst_port: u32) {
        self.write_u32(DST_PORT_OFFSET, dst_port);
    }

    /// Gets the payload length.
    pub fn get_len(&self) -> u32 {
        self.read_u32(LEN_OFFSET)
    }

    /// Sets the payload length.
    fn set_len(&mut self, len: u32) {
        self.write_u32(LEN_OFFSET, len);
    }

    /// Gets the type of socket the packet is intended for.
    pub fn get_type(&self) -> anyhow::Result<VSockType> {
        VSockType::try_from_primitive(self.read_u16(TYPE_OFFSET))
            .map_err(anyhow::Error::msg)
            .context("invalid socket type")
    }

    /// Sets the type of socket the packet is intended for.
    fn set_type(&mut self, socket_type: VSockType) {
        self.write_u16(TYPE_OFFSET, socket_type.into())
    }

    /// Gets the op that the packet represents.
    pub fn get_op(&self) -> anyhow::Result<VSockOp> {
        VSockOp::try_from_primitive(self.read_u16(OP_OFFSET))
            .map_err(anyhow::Error::msg)
            .context("invalid op")
    }

    /// Sets the op that the packet represents.
    pub fn set_op(&mut self, op: VSockOp) -> anyhow::Result<()> {
        if self.get_len() > 0 && op != VSockOp::Rw {
            anyhow::bail!("non-empty payloads are only allowed with RW ops");
        }
        self.write_u16(OP_OFFSET, op.into());
        Ok(())
    }

    /// Gets the flags.
    ///
    /// Only currently used for connection shutdown requests.
    pub fn get_flags(&self) -> VSockFlags {
        VSockFlags::from_bits_truncate(self.read_u32(FLAGS_OFFSET))
    }

    /// Sets the flags.
    ///
    /// Only currently used for connection shutdown requests.
    pub fn set_flags(&mut self, flags: VSockFlags) {
        self.write_u32(FLAGS_OFFSET, flags.bits());
    }

    /// Gets the size of the peer's stream buffer.
    ///
    /// Used to facilitate flow-control calculations.
    pub fn get_buf_alloc(&self) -> u32 {
        self.read_u32(BUF_ALLOC_OFFSET)
    }

    /// Sets the size of the stream buffer.
    pub fn set_buf_alloc(&mut self, buf_alloc: u32) {
        self.write_u32(BUF_ALLOC_OFFSET, buf_alloc);
    }

    /// Gets the number of bytes that the peer has read out of the stream buffer (hence making space
    /// in the buffer).
    ///
    /// Used to facilitate flow-control calculations.
    pub fn get_fwd_cnt(&self) -> u32 {
        self.read_u32(FWD_CNT_OFFSET)
    }

    /// Sets the number of bytes read from the stream buffer.
    pub fn set_fwd_cnt(&mut self, fwd_cnt: u32) {
        self.write_u32(FWD_CNT_OFFSET, fwd_cnt);
    }

    /// Gets the payload.
    pub fn get_payload(&self) -> &[u8] {
        &self.buffer[HEADER_SIZE..(HEADER_SIZE + self.get_len() as usize)]
    }

    /// Sets the payload of a data packet from a slice.
    ///
    /// The length of the slice must match the packets configures payload length. Only usable if the
    /// packet's op is `VSockOp::Rw`.
    pub fn set_payload(&mut self, data: &[u8]) -> anyhow::Result<()> {
        if self.get_op()? != VSockOp::Rw {
            anyhow::bail!("non-empty payloads are only allowed with RW ops");
        }
        let len = self.get_len();
        if len as usize != data.len() {
            anyhow::bail!("data length does not match the paacket's configured payload length");
        }

        self.buffer[HEADER_SIZE..(HEADER_SIZE + len as usize)].copy_from_slice(data);
        Ok(())
    }

    /// Returns the entire buffer as a slice.
    pub fn as_slice(&self) -> &[u8] {
        self.buffer.as_slice()
    }

    fn read_u16(&self, offset: usize) -> u16 {
        let mut data = [0; size_of::<u16>()];
        data.copy_from_slice(&self.buffer[offset..(offset + size_of::<u16>())]);
        u16::from_le_bytes(data)
    }

    fn read_u32(&self, offset: usize) -> u32 {
        let mut data = [0; size_of::<u32>()];
        data.copy_from_slice(&self.buffer[offset..(offset + size_of::<u32>())]);
        u32::from_le_bytes(data)
    }

    fn read_u64(&self, offset: usize) -> u64 {
        let mut data = [0; size_of::<u64>()];
        data.copy_from_slice(&self.buffer[offset..(offset + size_of::<u64>())]);
        u64::from_le_bytes(data)
    }

    fn write_u16(&mut self, offset: usize, value: u16) {
        let dest = &mut self.buffer[offset..(offset + size_of::<u16>())];
        dest.copy_from_slice(&value.to_le_bytes()[..]);
    }

    fn write_u32(&mut self, offset: usize, value: u32) {
        let dest = &mut self.buffer[offset..(offset + size_of::<u32>())];
        dest.copy_from_slice(&value.to_le_bytes()[..]);
    }

    fn write_u64(&mut self, offset: usize, value: u64) {
        let dest = &mut self.buffer[offset..(offset + size_of::<u64>())];
        dest.copy_from_slice(&value.to_le_bytes()[..]);
    }
}

/// Vsock Ops.
#[derive(Debug, Eq, PartialEq, TryFromPrimitive, IntoPrimitive)]
#[repr(u16)]
pub enum VSockOp {
    Invalid = 0,
    /// Connection request.
    Request = 1,
    /// Connections accepted response.
    Response = 2,
    /// Connection reset, either in reponse to a shutdown request or invalid packets received.
    Rst = 3,
    /// Connection shutdown request.
    Shutdown = 4,
    /// Represents a data packet.
    ///
    /// Used to send payload. Only data packets with this op can contain a payload.
    Rw = 5,
    /// Give update on credit to support flow control, either in response to a credit request or at
    /// any time it might be useful to inform the peer of the state of the stream buffer.
    CreditUpdate = 6,
    /// Request for update on credit to calculate stream buffer availability.
    CreditRequest = 7,
}

bitflags! {
    /// Flags about a socket connection.
    ///
    /// Used in a connection shutdown request.
    /// See <https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-4070005>.
    pub struct VSockFlags: u32 {
        /// Indicates that no more payload data will be received.
        const NO_RECEIVE = 1;
        /// Indicates that no more payload data will be senn.
        const NO_SEND = 2;
    }
}

/// Socket Type.
#[derive(Debug, Eq, PartialEq, TryFromPrimitive, IntoPrimitive)]
#[repr(u16)]
pub enum VSockType {
    /// Only stream sockets are currently supported in the Virtio spec.
    Stream = 1,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_and_get_all_header_fields() {
        let mut packet = Packet::new_header_only();
        packet.set_src_cid(1234);
        packet.set_dst_cid(2);
        packet.set_src_port(1023);
        packet.set_dst_port(8888);
        packet.set_flags(VSockFlags::all());
        packet.set_op(VSockOp::Shutdown).unwrap();
        packet.set_buf_alloc(4096);
        packet.set_fwd_cnt(12);

        assert_eq!(packet.get_src_cid(), 1234);
        assert_eq!(packet.get_dst_cid(), 2);
        assert_eq!(packet.get_src_port(), 1023);
        assert_eq!(packet.get_dst_port(), 8888);
        assert_eq!(packet.get_flags(), VSockFlags::all());
        assert_eq!(packet.get_type().unwrap(), VSockType::Stream);
        assert_eq!(packet.get_op().unwrap(), VSockOp::Shutdown);
        assert_eq!(packet.get_len(), 0);
        assert_eq!(packet.get_buf_alloc(), 4096);
        assert_eq!(packet.get_fwd_cnt(), 12);
    }

    #[test]
    fn test_invalid_payload() {
        let mut packet = Packet::new_with_payload(5);
        let result = packet.set_payload(&[1, 2, 3, 4]);
        assert!(result.is_err());
    }

    #[test]
    fn test_valid_payload() {
        let mut packet = Packet::new_with_payload(4);
        let result = packet.set_payload(&[1, 2, 3, 4]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_new_from_buffer() {
        let mut packet = Packet::new_with_payload(4);
        packet.set_payload(&[1, 2, 3, 4]).unwrap();

        let packet = Packet::new(packet.buffer.clone()).unwrap();
        assert_eq!(packet.get_payload(), &[1, 2, 3, 4]);
        assert_eq!(packet.get_len(), 4);
        assert_eq!(packet.get_type().unwrap(), VSockType::Stream);
        assert_eq!(packet.get_op().unwrap(), VSockOp::Rw);
        assert_eq!(packet.get_flags(), VSockFlags::empty());
    }

    #[test]
    fn test_invalid_op() {
        let mut packet = Packet::new_with_payload(1);
        assert!(packet.set_op(VSockOp::Rst).is_err())
    }
}
