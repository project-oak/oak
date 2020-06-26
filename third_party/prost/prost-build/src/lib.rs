#![doc(html_root_url = "https://docs.rs/prost-build/0.6.1")]
#![allow(clippy::option_as_ref_deref)]

//! `prost-build` compiles `.proto` files into Rust.
//!
//! `prost-build` is designed to be used for build-time code generation as part of a Cargo
//! build-script.
//!
//! ## Example
//!
//! Let's create a small crate, `snazzy`, that defines a collection of
//! snazzy new items in a protobuf file.
//!
//! ```bash
//! $ cargo new snazzy && cd snazzy
//! ```
//!
//! First, add `prost-build`, `prost` and its public dependencies to `Cargo.toml`
//! (see [crates.io](https://crates.io/crates/prost) for the current versions):
//!
//! ```toml
//! [dependencies]
//! bytes = <bytes-version>
//! prost = <prost-version>
//!
//! [build-dependencies]
//! prost-build = { version = <prost-version> }
//! ```
//!
//! Next, add `src/items.proto` to the project:
//!
//! ```proto
//! syntax = "proto3";
//!
//! package snazzy.items;
//!
//! // A snazzy new shirt!
//! message Shirt {
//! enum Size {
//!     SMALL = 0;
//!     MEDIUM = 1;
//!     LARGE = 2;
//! }
//!
//! string color = 1;
//! Size size = 2;
//! }
//! ```
//!
//! To generate Rust code from `items.proto`, we use `prost-build` in the crate's
//! `build.rs` build-script:
//!
//! ```rust,no_run
//! # use std::io::Result;
//! fn main() -> Result<()> {
//!   prost_build::compile_protos(&["src/items.proto"], &["src/"])?;
//!   Ok(())
//! }
//! ```
//!
//! And finally, in `lib.rs`, include the generated code:
//!
//! ```rust,ignore
//! // Include the `items` module, which is generated from items.proto.
//! pub mod items {
//!     include!(concat!(env!("OUT_DIR"), "/snazzy.items.rs"));
//! }
//!
//! pub fn create_large_shirt(color: String) -> items::Shirt {
//!     let mut shirt = items::Shirt::default();
//!     shirt.color = color;
//!     shirt.set_size(items::shirt::Size::Large);
//!     shirt
//! }
//! ```
//!
//! That's it! Run `cargo doc` to see documentation for the generated code. The full
//! example project can be found on [GitHub](https://github.com/danburkert/snazzy).
//!
//! ## Sourcing `protoc`
//!
//! `prost-build` depends on the Protocol Buffers compiler, `protoc`, to parse `.proto` files into
//! a representation that can be transformed into Rust. If set, `prost-build` uses the `PROTOC` and
//! `PROTOC_INCLUDE` environment variables for locating `protoc` and the Protobuf includes
//! directory. For example, on a macOS system where Protobuf is installed with Homebrew, set the
//! environment to:
//!
//! ```bash
//! PROTOC=/usr/local/bin/protoc
//! PROTOC_INCLUDE=/usr/local/include
//! ```
//!
//! and in a typical Linux installation:
//!
//! ```bash
//! PROTOC=/usr/bin/protoc
//! PROTOC_INCLUDE=/usr/include
//! ```
//!
//! If `PROTOC` is not found in the environment, then a pre-compiled `protoc` binary bundled in
//! the prost-build crate is used. Pre-compiled `protoc` binaries exist for Linux, macOS, and
//! Windows systems. If no pre-compiled `protoc` is available for the host platform, then the
//! `protoc` or `protoc.exe` binary on the `PATH` is used. If `protoc` is not available in any of
//! these fallback locations, then the build fails.
//!
//! If `PROTOC_INCLUDE` is not found in the environment, then the Protobuf include directory bundled
//! in the prost-build crate is be used.

mod ast;
mod code_generator;
mod extern_paths;
mod ident;
mod message_graph;

use std::collections::HashMap;
use std::default;
use std::env;
use std::fmt;
use std::fs;
use std::io::{Error, ErrorKind, Result};
use std::path::{Path, PathBuf};
use std::process::Command;

use log::trace;
use prost::Message;
use prost_types::{FileDescriptorProto, FileDescriptorSet};

pub use crate::ast::{Comments, Method, Service};
use crate::code_generator::CodeGenerator;
use crate::extern_paths::ExternPaths;
use crate::ident::to_snake;
use crate::message_graph::MessageGraph;

type Module = Vec<String>;

/// A service generator takes a service descriptor and generates Rust code.
///
/// `ServiceGenerator` can be used to generate application-specific interfaces
/// or implementations for Protobuf service definitions.
///
/// Service generators are registered with a code generator using the
/// `Config::service_generator` method.
///
/// A viable scenario is that an RPC framework provides a service generator. It generates a trait
/// describing methods of the service and some glue code to call the methods of the trait, defining
/// details like how errors are handled or if it is asynchronous. Then the user provides an
/// implementation of the generated trait in the application code and plugs it into the framework.
///
/// Such framework isn't part of Prost at present.
pub trait ServiceGenerator {
    /// Generates a Rust interface or implementation for a service, writing the
    /// result to `buf`.
    fn generate(&mut self, service: Service, buf: &mut String);

    /// Finalizes the generation process.
    ///
    /// In case there's something that needs to be output at the end of the generation process, it
    /// goes here. Similar to [`generate`](#method.generate), the output should be appended to
    /// `buf`.
    ///
    /// An example can be a module or other thing that needs to appear just once, not for each
    /// service generated.
    ///
    /// This still can be called multiple times in a lifetime of the service generator, because it
    /// is called once per `.proto` file.
    ///
    /// The default implementation is empty and does nothing.
    fn finalize(&mut self, _buf: &mut String) {}

    /// Finalizes the generation process for an entire protobuf package.
    ///
    /// This differs from [`finalize`](#method.finalize) by where (and how often) it is called
    /// during the service generator life cycle. This method is called once per protobuf package,
    /// making it ideal for grouping services within a single package spread across multiple
    /// `.proto` files.
    ///
    /// The default implementation is empty and does nothing.
    fn finalize_package(&mut self, _package: &str, _buf: &mut String) {}
}

/// Configuration options for Protobuf code generation.
///
/// This configuration builder can be used to set non-default code generation options.
pub struct Config {
    service_generator: Option<Box<dyn ServiceGenerator>>,
    btree_map: Vec<String>,
    type_attributes: Vec<(String, String)>,
    field_attributes: Vec<(String, String)>,
    prost_types: bool,
    strip_enum_prefix: bool,
    out_dir: Option<PathBuf>,
    extern_paths: Vec<(String, String)>,
}

impl Config {
    /// Creates a new code generator configuration with default options.
    pub fn new() -> Config {
        Config::default()
    }

    /// Configure the code generator to generate Rust [`BTreeMap`][1] fields for Protobuf
    /// [`map`][2] type fields.
    ///
    /// # Arguments
    ///
    /// **`paths`** - paths to specific fields, messages, or packages which should use a Rust
    /// `BTreeMap` for Protobuf `map` fields. Paths are specified in terms of the Protobuf type
    /// name (not the generated Rust type name). Paths with a leading `.` are treated as fully
    /// qualified names. Paths without a leading `.` are treated as relative, and are suffix
    /// matched on the fully qualified field name. If a Protobuf map field matches any of the
    /// paths, a Rust `BTreeMap` field is generated instead of the default [`HashMap`][3].
    ///
    /// The matching is done on the Protobuf names, before converting to Rust-friendly casing
    /// standards.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # let mut config = prost_build::Config::new();
    /// // Match a specific field in a message type.
    /// config.btree_map(&[".my_messages.MyMessageType.my_map_field"]);
    ///
    /// // Match all map fields in a message type.
    /// config.btree_map(&[".my_messages.MyMessageType"]);
    ///
    /// // Match all map fields in a package.
    /// config.btree_map(&[".my_messages"]);
    ///
    /// // Match all map fields. Expecially useful in `no_std` contexts.
    /// config.btree_map(&["."]);
    ///
    /// // Match all map fields in a nested message.
    /// config.btree_map(&[".my_messages.MyMessageType.MyNestedMessageType"]);
    ///
    /// // Match all fields named 'my_map_field'.
    /// config.btree_map(&["my_map_field"]);
    ///
    /// // Match all fields named 'my_map_field' in messages named 'MyMessageType', regardless of
    /// // package or nesting.
    /// config.btree_map(&["MyMessageType.my_map_field"]);
    ///
    /// // Match all fields named 'my_map_field', and all fields in the 'foo.bar' package.
    /// config.btree_map(&["my_map_field", ".foo.bar"]);
    /// ```
    ///
    /// [1]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
    /// [2]: https://developers.google.com/protocol-buffers/docs/proto3#maps
    /// [3]: https://doc.rust-lang.org/std/collections/struct.HashMap.html
    pub fn btree_map<I, S>(&mut self, paths: I) -> &mut Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        self.btree_map = paths.into_iter().map(|s| s.as_ref().to_string()).collect();
        self
    }

    /// Add additional attribute to matched fields.
    ///
    /// # Arguments
    ///
    /// **`path`** - a patch matching any number of fields. These fields get the attribute.
    /// For details about matching fields see [`btree_map`](#method.btree_map).
    ///
    /// **`attribute`** - an arbitrary string that'll be placed before each matched field. The
    /// expected usage are additional attributes, usually in concert with whole-type
    /// attributes set with [`type_attribute`](method.type_attribute), but it is not
    /// checked and anything can be put there.
    ///
    /// Note that the calls to this method are cumulative ‒ if multiple paths from multiple calls
    /// match the same field, the field gets all the corresponding attributes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # let mut config = prost_build::Config::new();
    /// // Prost renames fields named `in` to `in_`. But if serialized through serde,
    /// // they should as `in`.
    /// config.field_attribute("in", "#[serde(rename = \"in\")]");
    /// ```
    pub fn field_attribute<P, A>(&mut self, path: P, attribute: A) -> &mut Self
    where
        P: AsRef<str>,
        A: AsRef<str>,
    {
        self.field_attributes
            .push((path.as_ref().to_string(), attribute.as_ref().to_string()));
        self
    }

    /// Add additional attribute to matched messages, enums and one-ofs.
    ///
    /// # Arguments
    ///
    /// **`paths`** - a path matching any number of types. It works the same way as in
    /// [`btree_map`](#method.btree_map), just with the field name omitted.
    ///
    /// **`attribute`** - an arbitrary string to be placed before each matched type. The
    /// expected usage are additional attributes, but anything is allowed.
    ///
    /// The calls to this method are cumulative. They don't overwrite previous calls and if a
    /// type is matched by multiple calls of the method, all relevant attributes are added to
    /// it.
    ///
    /// For things like serde it might be needed to combine with [field
    /// attributes](#method.field_attribute).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # let mut config = prost_build::Config::new();
    /// // Nothing around uses floats, so we can derive real `Eq` in addition to `PartialEq`.
    /// config.type_attribute(".", "#[derive(Eq)]");
    /// // Some messages want to be serializable with serde as well.
    /// config.type_attribute("my_messages.MyMessageType",
    ///                       "#[derive(Serialize)] #[serde(rename-all = \"snake_case\")]");
    /// config.type_attribute("my_messages.MyMessageType.MyNestedMessageType",
    ///                       "#[derive(Serialize)] #[serde(rename-all = \"snake_case\")]");
    /// ```
    ///
    /// # Oneof fields
    ///
    /// The `oneof` fields don't have a type name of their own inside Protobuf. Therefore, the
    /// field name can be used both with `type_attribute` and `field_attribute` ‒ the first is
    /// placed before the `enum` type definition, the other before the field inside corresponding
    /// message `struct`.
    ///
    /// In other words, to place an attribute on the `enum` implementing the `oneof`, the match
    /// would look like `my_messages.MyMessageType.oneofname`.
    pub fn type_attribute<P, A>(&mut self, path: P, attribute: A) -> &mut Self
    where
        P: AsRef<str>,
        A: AsRef<str>,
    {
        self.type_attributes
            .push((path.as_ref().to_string(), attribute.as_ref().to_string()));
        self
    }

    /// Configures the code generator to use the provided service generator.
    pub fn service_generator(&mut self, service_generator: Box<dyn ServiceGenerator>) -> &mut Self {
        self.service_generator = Some(service_generator);
        self
    }

    /// Configures the code generator to not use the `prost_types` crate for Protobuf well-known
    /// types, and instead generate Protobuf well-known types from their `.proto` definitions.
    pub fn compile_well_known_types(&mut self) -> &mut Self {
        self.prost_types = false;
        self
    }

    /// Declare an externally provided Protobuf package or type.
    ///
    /// `extern_path` allows `prost` types in external crates to be referenced in generated code.
    ///
    /// When `prost` compiles a `.proto` which includes an import of another `.proto`, it will
    /// automatically recursively compile the imported file as well. `extern_path` can be used
    /// to instead substitute types from an external crate.
    ///
    /// # Example
    ///
    /// As an example, consider a crate, `uuid`, with a `prost`-generated `Uuid` type:
    ///
    /// ```proto
    /// // uuid.proto
    ///
    /// syntax = "proto3";
    /// package uuid;
    ///
    /// message Uuid {
    ///     string uuid_str = 1;
    /// }
    /// ```
    ///
    /// The `uuid` crate implements some traits for `Uuid`, and publicly exports it:
    ///
    /// ```rust,ignore
    /// // lib.rs in the uuid crate
    ///
    /// include!(concat!(env!("OUT_DIR"), "/uuid.rs"));
    ///
    /// pub trait DoSomething {
    ///     fn do_it(&self);
    /// }
    ///
    /// impl DoSomething for Uuid {
    ///     fn do_it(&self) {
    ///         println!("Done");
    ///     }
    /// }
    /// ```
    ///
    /// A separate crate, `my_application`, uses `prost` to generate message types which reference
    /// `Uuid`:
    ///
    /// ```proto
    /// // my_application.proto
    ///
    /// syntax = "proto3";
    /// package my_application;
    ///
    /// import "uuid.proto";
    ///
    /// message MyMessage {
    ///     uuid.Uuid message_id = 1;
    ///     string some_payload = 2;
    /// }
    /// ```
    ///
    /// Additionally, `my_application` depends on the trait impls provided by the `uuid` crate:
    ///
    /// ```rust,ignore
    /// // `main.rs` of `my_application`
    ///
    /// use uuid::{DoSomething, Uuid};
    ///
    /// include!(concat!(env!("OUT_DIR"), "/my_application.rs"));
    ///
    /// pub fn process_message(msg: MyMessage) {
    ///     if let Some(uuid) = msg.message_id {
    ///         uuid.do_it();
    ///     }
    /// }
    /// ```
    ///
    /// Without configuring `uuid` as an external path in `my_application`'s `build.rs`, `prost`
    /// would compile a completely separate version of the `Uuid` type, and `process_message` would
    /// fail to compile. However, if `my_application` configures `uuid` as an extern path with a
    /// call to `.extern_path(".uuid", "::uuid")`, `prost` will use the external type instead of
    /// compiling a new version of `Uuid`. Note that the configuration could also be specified as
    /// `.extern_path(".uuid.Uuid", "::uuid::Uuid")` if only the `Uuid` type were externally
    /// provided, and not the whole `uuid` package.
    ///
    /// # Usage
    ///
    /// `extern_path` takes a fully-qualified Protobuf path, and the corresponding Rust path that
    /// it will be substituted with in generated code. The Protobuf path can refer to a package or
    /// a type, and the Rust path should correspondingly refer to a Rust module or type.
    ///
    /// ```rust
    /// # let mut config = prost_build::Config::new();
    /// // Declare the `uuid` Protobuf package and all nested packages and types as externally
    /// // provided by the `uuid` crate.
    /// config.extern_path(".uuid", "::uuid");
    ///
    /// // Declare the `foo.bar.baz` Protobuf package and all nested packages and types as
    /// // externally provided by the `foo_bar_baz` crate.
    /// config.extern_path(".foo.bar.baz", "::foo_bar_baz");
    ///
    /// // Declare the `uuid.Uuid` Protobuf type (and all nested types) as externally provided
    /// // by the `uuid` crate's `Uuid` type.
    /// config.extern_path(".uuid.Uuid", "::uuid::Uuid");
    /// ```
    pub fn extern_path<P1, P2>(&mut self, proto_path: P1, rust_path: P2) -> &mut Self
    where
        P1: Into<String>,
        P2: Into<String>,
    {
        self.extern_paths
            .push((proto_path.into(), rust_path.into()));
        self
    }

    /// Configures the code generator to not strip the enum name from variant names.
    ///
    /// Protobuf enum definitions commonly include the enum name as a prefix of every variant name.
    /// This style is non-idiomatic in Rust, so by default `prost` strips the enum name prefix from
    /// variants which include it. Configuring this option prevents `prost` from stripping the
    /// prefix.
    pub fn retain_enum_prefix(&mut self) -> &mut Self {
        self.strip_enum_prefix = false;
        self
    }

    /// Configures the output directory where generated Rust files will be written.
    ///
    /// If unset, defaults to the `OUT_DIR` environment variable. `OUT_DIR` is set by Cargo when
    /// executing build scripts, so `out_dir` typically does not need to be configured.
    pub fn out_dir<P>(&mut self, path: P) -> &mut Self
    where
        P: Into<PathBuf>,
    {
        self.out_dir = Some(path.into());
        self
    }

    /// Compile `.proto` files into Rust files during a Cargo build with additional code generator
    /// configuration options.
    ///
    /// This method is like the `prost_build::compile_protos` function, with the added ability to
    /// specify non-default code generation options. See that function for more information about
    /// the arguments and generated outputs.
    ///
    /// # Example `build.rs`
    ///
    /// ```rust,no_run
    /// # use std::io::Result;
    /// fn main() -> Result<()> {
    ///   let mut prost_build = prost_build::Config::new();
    ///   prost_build.btree_map(&["."]);
    ///   prost_build.compile_protos(&["src/frontend.proto", "src/backend.proto"], &["src"])?;
    ///   Ok(())
    /// }
    /// ```
    pub fn compile_protos<P>(&mut self, protos: &[P], includes: &[P]) -> Result<()>
    where
        P: AsRef<Path>,
    {
        let target: PathBuf = self.out_dir.clone().map(Ok).unwrap_or_else(|| {
            env::var_os("OUT_DIR")
                .ok_or_else(|| {
                    Error::new(ErrorKind::Other, "OUT_DIR environment variable is not set")
                })
                .map(Into::into)
        })?;

        // TODO: This should probably emit 'rerun-if-changed=PATH' directives for cargo, however
        // according to [1] if any are output then those paths replace the default crate root,
        // which is undesirable. Figure out how to do it in an additive way; perhaps gcc-rs has
        // this figured out.
        // [1]: http://doc.crates.io/build-script.html#outputs-of-the-build-script

        let tmp = tempfile::Builder::new().prefix("prost-build").tempdir()?;
        let descriptor_set = tmp.path().join("prost-descriptor-set");

        let mut cmd = Command::new(protoc());
        cmd.arg("--include_imports")
            .arg("--include_source_info")
            .arg("-o")
            .arg(&descriptor_set);

        for include in includes {
            cmd.arg("-I").arg(include.as_ref());
        }

        // Set the protoc include after the user includes in case the user wants to
        // override one of the built-in .protos.
        cmd.arg("-I").arg(protoc_include());

        for proto in protos {
            cmd.arg(proto.as_ref());
        }

        let output = cmd.output()?;
        if !output.status.success() {
            return Err(Error::new(
                ErrorKind::Other,
                format!("protoc failed: {}", String::from_utf8_lossy(&output.stderr)),
            ));
        }

        let buf = fs::read(descriptor_set)?;
        let descriptor_set = FileDescriptorSet::decode(&*buf).map_err(|error| {
            Error::new(
                ErrorKind::InvalidInput,
                format!("invalid FileDescriptorSet: {}", error.to_string()),
            )
        })?;

        let modules = self.generate(descriptor_set.file)?;
        for (module, content) in modules {
            let mut filename = module.join(".");
            filename.push_str(".rs");

            let output_path = target.join(&filename);

            let previous_content = fs::read(&output_path);

            if previous_content
                .map(|previous_content| previous_content == content.as_bytes())
                .unwrap_or(false)
            {
                trace!("unchanged: {:?}", filename);
            } else {
                trace!("writing: {:?}", filename);
                fs::write(output_path, content)?;
            }
        }

        Ok(())
    }

    fn generate(&mut self, files: Vec<FileDescriptorProto>) -> Result<HashMap<Module, String>> {
        let mut modules = HashMap::new();
        let mut packages = HashMap::new();

        let message_graph = MessageGraph::new(&files)
            .map_err(|error| Error::new(ErrorKind::InvalidInput, error))?;
        let extern_paths = ExternPaths::new(&self.extern_paths, self.prost_types)
            .map_err(|error| Error::new(ErrorKind::InvalidInput, error))?;

        for file in files {
            let module = self.module(&file);

            // Only record packages that have services
            if !file.service.is_empty() {
                packages.insert(module.clone(), file.package().to_string());
            }

            let mut buf = modules.entry(module).or_insert_with(String::new);
            CodeGenerator::generate(self, &message_graph, &extern_paths, file, &mut buf);
        }

        if let Some(ref mut service_generator) = self.service_generator {
            for (module, package) in packages {
                let buf = modules.get_mut(&module).unwrap();
                service_generator.finalize_package(&package, buf);
            }
        }

        Ok(modules)
    }

    fn module(&self, file: &FileDescriptorProto) -> Module {
        file.package()
            .split('.')
            .filter(|s| !s.is_empty())
            .map(to_snake)
            .collect()
    }
}

impl default::Default for Config {
    fn default() -> Config {
        Config {
            service_generator: None,
            btree_map: Vec::new(),
            type_attributes: Vec::new(),
            field_attributes: Vec::new(),
            prost_types: true,
            strip_enum_prefix: true,
            out_dir: None,
            extern_paths: Vec::new(),
        }
    }
}

impl fmt::Debug for Config {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_struct("Config")
            .field("btree_map", &self.btree_map)
            .field("type_attributes", &self.type_attributes)
            .field("field_attributes", &self.field_attributes)
            .field("prost_types", &self.prost_types)
            .field("strip_enum_prefix", &self.strip_enum_prefix)
            .field("out_dir", &self.out_dir)
            .field("extern_paths", &self.extern_paths)
            .finish()
    }
}

/// Compile `.proto` files into Rust files during a Cargo build.
///
/// The generated `.rs` files are written to the Cargo `OUT_DIR` directory, suitable for use with
/// the [include!][1] macro. See the [Cargo `build.rs` code generation][2] example for more info.
///
/// This function should be called in a project's `build.rs`.
///
/// # Arguments
///
/// **`protos`** - Paths to `.proto` files to compile. Any transitively [imported][3] `.proto`
/// files are automatically be included.
///
/// **`includes`** - Paths to directories in which to search for imports. Directories are searched
/// in order. The `.proto` files passed in **`protos`** must be found in one of the provided
/// include directories.
///
/// # Errors
///
/// This function can fail for a number of reasons:
///
///   - Failure to locate or download `protoc`.
///   - Failure to parse the `.proto`s.
///   - Failure to locate an imported `.proto`.
///   - Failure to compile a `.proto` without a [package specifier][4].
///
/// It's expected that this function call be `unwrap`ed in a `build.rs`; there is typically no
/// reason to gracefully recover from errors during a build.
///
/// # Example `build.rs`
///
/// ```rust,no_run
/// # use std::io::Result;
/// fn main() -> Result<()> {
///   prost_build::compile_protos(&["src/frontend.proto", "src/backend.proto"], &["src"])?;
///   Ok(())
/// }
/// ```
///
/// [1]: https://doc.rust-lang.org/std/macro.include.html
/// [2]: http://doc.crates.io/build-script.html#case-study-code-generation
/// [3]: https://developers.google.com/protocol-buffers/docs/proto3#importing-definitions
/// [4]: https://developers.google.com/protocol-buffers/docs/proto#packages
pub fn compile_protos<P>(protos: &[P], includes: &[P]) -> Result<()>
where
    P: AsRef<Path>,
{
    Config::new().compile_protos(protos, includes)
}

/// Returns the path to the `protoc` binary.
pub fn protoc() -> PathBuf {
    match env::var_os("PROTOC") {
        Some(protoc) => PathBuf::from(protoc),
        None => PathBuf::from(env!("PROTOC")),
    }
}

/// Returns the path to the Protobuf include directory.
pub fn protoc_include() -> PathBuf {
    match env::var_os("PROTOC_INCLUDE") {
        Some(include) => PathBuf::from(include),
        None => PathBuf::from(env!("PROTOC_INCLUDE")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    /// An example service generator that generates a trait with methods corresponding to the
    /// service methods.
    struct ServiceTraitGenerator;
    impl ServiceGenerator for ServiceTraitGenerator {
        fn generate(&mut self, service: Service, buf: &mut String) {
            // Generate a trait for the service.
            service.comments.append_with_indent(0, buf);
            buf.push_str(&format!("trait {} {{\n", &service.name));

            // Generate the service methods.
            for method in service.methods {
                method.comments.append_with_indent(1, buf);
                buf.push_str(&format!(
                    "    fn {}({}) -> {};\n",
                    method.name, method.input_type, method.output_type
                ));
            }

            // Close out the trait.
            buf.push_str("}\n");
        }
        fn finalize(&mut self, buf: &mut String) {
            // Needs to be present only once, no matter how many services there are
            buf.push_str("pub mod utils { }\n");
        }
    }

    /// Implements `ServiceGenerator` and provides some state for assertions.
    struct MockServiceGenerator {
        state: Rc<RefCell<MockState>>,
    }

    /// Holds state for `MockServiceGenerator`
    #[derive(Default)]
    struct MockState {
        service_names: Vec<String>,
        package_names: Vec<String>,
        finalized: u32,
    }

    impl MockServiceGenerator {
        fn new(state: Rc<RefCell<MockState>>) -> Self {
            Self { state }
        }
    }

    impl ServiceGenerator for MockServiceGenerator {
        fn generate(&mut self, service: Service, _buf: &mut String) {
            let mut state = self.state.borrow_mut();
            state.service_names.push(service.name);
        }

        fn finalize(&mut self, _buf: &mut String) {
            let mut state = self.state.borrow_mut();
            state.finalized += 1;
        }

        fn finalize_package(&mut self, package: &str, _buf: &mut String) {
            let mut state = self.state.borrow_mut();
            state.package_names.push(package.to_string());
        }
    }

    #[test]
    fn smoke_test() {
        let _ = env_logger::try_init();
        Config::new()
            .service_generator(Box::new(ServiceTraitGenerator))
            .compile_protos(&["src/smoke_test.proto"], &["src"])
            .unwrap();
    }

    #[test]
    fn finalize_package() {
        let _ = env_logger::try_init();

        let state = Rc::new(RefCell::new(MockState::default()));
        let gen = MockServiceGenerator::new(Rc::clone(&state));

        Config::new()
            .service_generator(Box::new(gen))
            .compile_protos(&["src/hello.proto", "src/goodbye.proto"], &["src"])
            .unwrap();

        let state = state.borrow();
        assert_eq!(&state.service_names, &["Greeting", "Farewell"]);
        assert_eq!(&state.package_names, &["helloworld"]);
        assert_eq!(state.finalized, 3);
    }
}
