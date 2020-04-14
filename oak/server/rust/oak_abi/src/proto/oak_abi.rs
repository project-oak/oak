/// Status values exchanged as i32 values across the Node Wasm interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum OakStatus {
    Unspecified = 0,
    /// Success.
    Ok = 1,
    /// Invalid handle provided.
    ErrBadHandle = 2,
    /// Arguments invalid.
    ErrInvalidArgs = 3,
    /// Channel has been closed.
    ErrChannelClosed = 4,
    /// Provided buffer was too small for operation (an output value will indicate required size).
    ErrBufferTooSmall = 5,
    /// Provided handle space was too small for operation (an output value will
    /// indicate required size).
    ErrHandleSpaceTooSmall = 6,
    /// Argument out of valid range.
    ErrOutOfRange = 7,
    /// Internal error.
    ErrInternal = 8,
    /// Node terminated.
    ErrTerminated = 9,
    /// Channel has no messages available to read.
    ErrChannelEmpty = 10,
    /// The node does not have sufficient permissions to perform the requested operation.
    ErrPermissionDenied = 11,
}
/// Single byte values used to indicate the read status of a channel on the
/// `oak.wait_on_channels` host function.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum ChannelReadStatus {
    /// No pending messages available on channel.
    NotReady = 0,
    /// Pending message available on channel.
    ReadReady = 1,
    /// Channel handle does not identify the read half of a current channel.
    InvalidChannel = 2,
    /// Channel has no extant write halves (and is empty).
    Orphaned = 3,
}
