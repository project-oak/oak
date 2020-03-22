/// This message defines the data that is passed as a log message to a logging pseudo-node. It
/// provides a "schema" to keep the logging pseudo-node in sync with the internal representation of
/// log messages in Oak SDK.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct LogMessage {
    /// The source file containing the message.
    #[prost(string, tag="1")]
    pub file: std::string::String,
    /// The line containing the message.
    #[prost(uint32, tag="2")]
    pub line: u32,
    /// The verbosity level of the message.
    #[prost(enumeration="Level", tag="3")]
    pub level: i32,
    /// The message body.
    #[prost(string, tag="4")]
    pub message: std::string::String,
}
/// Logging levels as defined in https://docs.rs/log/0.4.10/log/enum.Level.html.
/// UNKNOWN_LEVEL is added as the default value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, ::prost::Enumeration)]
#[repr(i32)]
pub enum Level {
    UnknownLevel = 0,
    Error = 1,
    Warn = 2,
    Info = 3,
    Debugging = 4,
    Trace = 5,
}
