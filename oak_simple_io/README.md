# Simple I/O Channel

This library provides a simple `no_std` compatible guest driver that can be used
as a communications channel between a bare-metal guest VM and the host.

The communication is based on shared memory. There are two separate channels,
one for input and one for output. Each channel has one buffer in shared memory.
The guest notifies the hypervisor of the guest-physical addresses of these
buffers via pre-agreed 32-bit I/O ports. The guest only does this once at
startup. Since each address is 64 bits long the guest uses 2 ports for each
address. The first port contains the most significant 4 bytes, and the second
contains the least significant 4 bytes.

The current implementation assumes an identity mapping for the memory so that
guest-phsyical and guest-virtual addresses are the same.

The guest uses an additional pre-agreed 32-bit I/O port for each channel to
represent the length of each message.

For the output channel, the guest writes to the length I/O port. This acts as a
doorbell to notify the hypervisor that a new message is available. The code
assumes that the hypervisor implementation will ensure that this guest operation
blocks until the hypervisor has copied the message out of the buffer.

The guest reads from the length I/O port for the input channel. The hypervisor
I/O handler implementation for this port writes a message to the input buffer
(if one is availble) and returns the actual message length via the port. The
returned length must not exceed the length of the input buffer. If there aren't
any messages, the hypervisor must return a length of 0.
