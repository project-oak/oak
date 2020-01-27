extern crate tempdir;

extern crate grpc_compiler;

extern crate protobuf;
extern crate protoc;
extern crate protoc_rust;

use std::fs;
use std::io;
use std::io::Read;
use std::io::Write;

pub type Error = io::Error;
pub type Result<T> = io::Result<T>;

#[derive(Debug, Default)]
pub struct Args<'a> {
    /// --lang_out= param
    pub out_dir: &'a str,
    /// -I args
    pub includes: &'a [&'a str],
    /// List of .proto files to compile
    pub input: &'a [&'a str],
    /// Generate rust-protobuf files along with rust-gprc
    pub rust_protobuf: bool,
    /// Customize rust-protobuf codegen
    pub rust_protobuf_customize: protoc_rust::Customize,
}

pub fn run(args: Args) -> Result<()> {
    let protoc = protoc::Protoc::from_env_path();
    let version = protoc.version().expect("protoc version");
    if !version.is_3() {
        panic!("protobuf must have version 3");
    }

    if args.rust_protobuf {
        protoc_rust::run(protoc_rust::Args {
            out_dir: args.out_dir,
            includes: args.includes,
            input: args.input,
            customize: args.rust_protobuf_customize,
            ..Default::default()
        })?;
    }

    let temp_dir = tempdir::TempDir::new("protoc-rust")?;
    let temp_file = temp_dir.path().join("descriptor.pbbin");
    let temp_file = temp_file.to_str().expect("utf-8 file name");

    protoc.write_descriptor_set(protoc::DescriptorSetOutArgs {
        out: temp_file,
        includes: args.includes,
        input: args.input,
        include_imports: true,
    })?;

    let mut fds = Vec::new();
    let mut file = fs::File::open(temp_file)?;
    file.read_to_end(&mut fds)?;

    drop(file);
    drop(temp_dir);

    let fds: protobuf::descriptor::FileDescriptorSet =
        protobuf::parse_from_bytes(&fds).map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;

    let mut includes = args.includes;
    if includes.is_empty() {
        static DOT_SLICE: &'static [&'static str] = &["."];
        includes = DOT_SLICE;
    }

    let mut files_to_generate = Vec::new();
    'outer: for file in args.input {
        for include in includes {
            if let Some(truncated) = remove_path_prefix(file, include) {
                files_to_generate.push(truncated.to_owned());
                continue 'outer;
            }
        }

        return Err(Error::new(
            io::ErrorKind::Other,
            format!(
                "file {:?} is not found in includes {:?}",
                file, args.includes
            ),
        ));
    }

    let gen_result = grpc_compiler::codegen::gen(fds.get_file(), &files_to_generate);

    for r in gen_result {
        let r: protobuf::compiler_plugin::GenResult = r;
        let file = format!("{}/{}", args.out_dir, r.name);
        let mut file = fs::File::create(&file)?;
        file.write_all(&r.content)?;
        file.flush()?;
    }

    Ok(())
}

fn remove_dot_slash(path: &str) -> &str {
    if path == "." {
        ""
    } else if path.starts_with("./") || path.starts_with(".\\") {
        &path[2..]
    } else {
        path
    }
}

fn remove_path_prefix<'a>(mut path: &'a str, mut prefix: &str) -> Option<&'a str> {
    path = remove_dot_slash(path);
    prefix = remove_dot_slash(prefix);

    if prefix == "" {
        return Some(path);
    }

    if prefix.ends_with("/") || prefix.ends_with("\\") {
        prefix = &prefix[..prefix.len() - 1];
    }

    if !path.starts_with(prefix) {
        return None;
    }

    if path.len() <= prefix.len() {
        return None;
    }

    if path.as_bytes()[prefix.len()] == b'/' || path.as_bytes()[prefix.len()] == b'\\' {
        return Some(&path[prefix.len() + 1..]);
    } else {
        return None;
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn remove_path_prefix() {
        assert_eq!(
            Some("abc.proto"),
            super::remove_path_prefix("xxx/abc.proto", "xxx")
        );
        assert_eq!(
            Some("abc.proto"),
            super::remove_path_prefix("xxx/abc.proto", "xxx/")
        );
        assert_eq!(
            Some("abc.proto"),
            super::remove_path_prefix("../xxx/abc.proto", "../xxx/")
        );
        assert_eq!(
            Some("abc.proto"),
            super::remove_path_prefix("abc.proto", ".")
        );
        assert_eq!(
            Some("abc.proto"),
            super::remove_path_prefix("abc.proto", "./")
        );
        assert_eq!(None, super::remove_path_prefix("xxx/abc.proto", "yyy"));
        assert_eq!(None, super::remove_path_prefix("xxx/abc.proto", "yyy/"));
    }
}
