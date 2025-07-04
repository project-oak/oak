// This file is @generated by prost-build.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Profile {
    /// A description of the samples associated with each Sample.value.
    /// For a cpu profile this might be:
    ///    \[["cpu","nanoseconds"]\] or \[["wall","seconds"]\] or \[["syscall","count"]\]
    /// For a heap profile, this might be:
    ///    \[["allocations","count"\], \["space","bytes"]\],
    /// If one of the values represents the number of events represented
    /// by the sample, by convention it should be at index 0 and use
    /// sample_type.unit == "count".
    #[prost(message, repeated, tag = "1")]
    pub sample_type: ::prost::alloc::vec::Vec<ValueType>,
    /// The set of samples recorded in this profile.
    #[prost(message, repeated, tag = "2")]
    pub sample: ::prost::alloc::vec::Vec<Sample>,
    /// Mapping from address ranges to the image/binary/library mapped
    /// into that address range.  mapping\[0\] will be the main binary.
    #[prost(message, repeated, tag = "3")]
    pub mapping: ::prost::alloc::vec::Vec<Mapping>,
    /// Useful program location
    #[prost(message, repeated, tag = "4")]
    pub location: ::prost::alloc::vec::Vec<Location>,
    /// Functions referenced by locations
    #[prost(message, repeated, tag = "5")]
    pub function: ::prost::alloc::vec::Vec<Function>,
    /// A common table for strings referenced by various messages.
    /// string_table\[0\] must always be "".
    #[prost(string, repeated, tag = "6")]
    pub string_table: ::prost::alloc::vec::Vec<::prost::alloc::string::String>,
    /// frames with Function.function_name fully matching the following
    /// regexp will be dropped from the samples, along with their successors.
    ///
    /// Index into string table.
    #[prost(int64, tag = "7")]
    pub drop_frames: i64,
    /// frames with Function.function_name fully matching the following
    /// regexp will be kept, even if it matches drop_functions.
    ///
    /// Index into string table.
    #[prost(int64, tag = "8")]
    pub keep_frames: i64,
    /// Time of collection (UTC) represented as nanoseconds past the epoch.
    #[prost(int64, tag = "9")]
    pub time_nanos: i64,
    /// Duration of the profile, if a duration makes sense.
    #[prost(int64, tag = "10")]
    pub duration_nanos: i64,
    /// The kind of events between sampled ocurrences.
    /// e.g \[ "cpu","cycles" \] or \[ "heap","bytes" \]
    #[prost(message, optional, tag = "11")]
    pub period_type: ::core::option::Option<ValueType>,
    /// The number of events between sampled occurrences.
    #[prost(int64, tag = "12")]
    pub period: i64,
    /// Freeform text associated to the profile.
    ///
    /// Indices into string table.
    #[prost(int64, repeated, tag = "13")]
    pub comment: ::prost::alloc::vec::Vec<i64>,
    /// Index into the string table of the type of the preferred sample
    /// value. If unset, clients should default to the last sample value.
    #[prost(int64, tag = "14")]
    pub default_sample_type: i64,
}
/// ValueType describes the semantics and measurement units of a value.
#[derive(Clone, Copy, PartialEq, ::prost::Message)]
pub struct ValueType {
    /// Rename it from type to ty to avoid using keyword in Rust.
    ///
    /// Index into string table.
    #[prost(int64, tag = "1")]
    pub ty: i64,
    /// Index into string table.
    #[prost(int64, tag = "2")]
    pub unit: i64,
}
/// Each Sample records values encountered in some program context.
///
/// The program context is typically a stack trace, perhaps
/// augmented with auxiliary information like the thread-id, some
/// indicator of a higher level request being handled etc.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Sample {
    /// The ids recorded here correspond to a Profile.location.id.
    /// The leaf is at location_id\[0\].
    #[prost(uint64, repeated, tag = "1")]
    pub location_id: ::prost::alloc::vec::Vec<u64>,
    /// The type and unit of each value is defined by the corresponding
    /// entry in Profile.sample_type. All samples must have the same
    /// number of values, the same as the length of Profile.sample_type.
    /// When aggregating multiple samples into a single sample, the
    /// result has a list of values that is the elemntwise sum of the
    /// lists of the originals.
    #[prost(int64, repeated, tag = "2")]
    pub value: ::prost::alloc::vec::Vec<i64>,
    /// label includes additional context for this sample. It can include
    /// things like a thread id, allocation size, etc
    #[prost(message, repeated, tag = "3")]
    pub label: ::prost::alloc::vec::Vec<Label>,
}
#[derive(Clone, Copy, PartialEq, ::prost::Message)]
pub struct Label {
    /// Index into string table
    #[prost(int64, tag = "1")]
    pub key: i64,
    /// At most one of the following must be present
    ///
    /// Index into string table
    #[prost(int64, tag = "2")]
    pub str: i64,
    #[prost(int64, tag = "3")]
    pub num: i64,
    /// Should only be present when num is present.
    /// Specifies the units of num.
    /// Use arbitrary string (for example, "requests") as a custom count unit.
    /// If no unit is specified, consumer may apply heuristic to deduce the unit.
    /// Consumers may also  interpret units like "bytes" and "kilobytes" as memory
    /// units and units like "seconds" and "nanoseconds" as time units,
    /// and apply appropriate unit conversions to these.
    ///
    /// Index into string table
    #[prost(int64, tag = "4")]
    pub num_unit: i64,
}
#[derive(Clone, Copy, PartialEq, ::prost::Message)]
pub struct Mapping {
    /// Unique nonzero id for the mapping.
    #[prost(uint64, tag = "1")]
    pub id: u64,
    /// Address at which the binary (or DLL) is loaded into memory.
    #[prost(uint64, tag = "2")]
    pub memory_start: u64,
    /// The limit of the address range occupied by this mapping.
    #[prost(uint64, tag = "3")]
    pub memory_limit: u64,
    /// Offset in the binary that corresponds to the first mapped address.
    #[prost(uint64, tag = "4")]
    pub file_offset: u64,
    /// The object this entry is loaded from.  This can be a filename on
    /// disk for the main binary and shared libraries, or virtual
    /// abstractions like "\[vdso\]".
    ///
    /// Index into string table
    #[prost(int64, tag = "5")]
    pub filename: i64,
    /// A string that uniquely identifies a particular program version
    /// with high probability. E.g., for binaries generated by GNU tools,
    /// it could be the contents of the .note.gnu.build-id field.
    ///
    /// Index into string table
    #[prost(int64, tag = "6")]
    pub build_id: i64,
    /// The following fields indicate the resolution of symbolic info.
    #[prost(bool, tag = "7")]
    pub has_functions: bool,
    #[prost(bool, tag = "8")]
    pub has_filenames: bool,
    #[prost(bool, tag = "9")]
    pub has_line_numbers: bool,
    #[prost(bool, tag = "10")]
    pub has_inline_frames: bool,
}
/// Describes function and line table debug information.
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct Location {
    /// Unique nonzero id for the location.  A profile could use
    /// instruction addresses or any integer sequence as ids.
    #[prost(uint64, tag = "1")]
    pub id: u64,
    /// The id of the corresponding profile.Mapping for this location.
    /// It can be unset if the mapping is unknown or not applicable for
    /// this profile type.
    #[prost(uint64, tag = "2")]
    pub mapping_id: u64,
    /// The instruction address for this location, if available.  It
    /// should be within \[Mapping.memory_start...Mapping.memory_limit\]
    /// for the corresponding mapping. A non-leaf address may be in the
    /// middle of a call instruction. It is up to display tools to find
    /// the beginning of the instruction if necessary.
    #[prost(uint64, tag = "3")]
    pub address: u64,
    /// Multiple line indicates this location has inlined functions,
    /// where the last entry represents the caller into which the
    /// preceding entries were inlined.
    ///
    /// E.g., if memcpy() is inlined into printf:
    ///     line\[0\].function_name == "memcpy"
    ///     line\[1\].function_name == "printf"
    #[prost(message, repeated, tag = "4")]
    pub line: ::prost::alloc::vec::Vec<Line>,
    /// Provides an indication that multiple symbols map to this location's
    /// address, for example due to identical code folding by the linker. In that
    /// case the line information above represents one of the multiple
    /// symbols. This field must be recomputed when the symbolization state of the
    /// profile changes.
    #[prost(bool, tag = "5")]
    pub is_folded: bool,
}
#[derive(Clone, Copy, PartialEq, ::prost::Message)]
pub struct Line {
    /// The id of the corresponding profile.Function for this line.
    #[prost(uint64, tag = "1")]
    pub function_id: u64,
    /// Line number in source code.
    #[prost(int64, tag = "2")]
    pub line: i64,
}
#[derive(Clone, Copy, PartialEq, ::prost::Message)]
pub struct Function {
    /// Unique nonzero id for the function.
    #[prost(uint64, tag = "1")]
    pub id: u64,
    /// Name of the function, in human-readable form if available.
    ///
    /// Index into string table
    #[prost(int64, tag = "2")]
    pub name: i64,
    /// Name of the function, as identified by the system.
    /// For instance, it can be a C++ mangled name.
    ///
    /// Index into string table
    #[prost(int64, tag = "3")]
    pub system_name: i64,
    /// Source file containing the function.
    ///
    /// Index into string table
    #[prost(int64, tag = "4")]
    pub filename: i64,
    /// Line number in source file.
    #[prost(int64, tag = "5")]
    pub start_line: i64,
}
