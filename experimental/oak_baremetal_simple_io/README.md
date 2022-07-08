# Simple I/O Channel

This library provides a simple guest driver that can be used as a communications
channel between a bare-metal guest VM and the host.

The communication is based on shared memory. There are two separate channels,
one for input and one for output. Each channel has one buffer in shared memory.
The guest-physical addresses of the shared pages used for input and output
buffers are communicated via pre-agreed 32-bit I/O ports. This only has to be
done once at startup. Since each address is 64 bits long each address will be
split across 2 ports, the first containing the most significant 4 bytes, and the
next containing the least significant 4 bytes.

The current implementation assumes an identity mapping for the memory so that
guest-phsyical and guest-virtual addresses are the same.

An additional 32-bit I/O port is used for each channel to specify the length of
each message.

For the output channel, writing to the length I/O port will act as a doorbell to
notify the host that a new message is available. It is assumed that the VMM
implementation will ensure that this operation will block until the new message
has been copied out of the buffer.

Reading from the length I/O port for the input channel will cause the VMM to
write a message to the input buffer (if one is availble) and return the actual
message length. The returned length must not exceed the length of the input
buffer. If there aren't any messages, a length of 0 must be returned.
