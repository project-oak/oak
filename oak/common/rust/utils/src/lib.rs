use std::collections::HashMap;
use std::path::{Path, PathBuf};

// ...
// Current version doesn't support nested directories since `protoc_rust` doesn't ...
// pub fn run_protoc_rust(args: protoc_rust::Args) -> std::io::Result<()> {

//     let temp_dir = tempfile::tempdir()?;
//     let temp_path = temp_dir.path();
//     let mut temp_args = args;
//     temp_args.out_dir = temp_path.to_str().unwrap_or(Err(()));
//     protoc_rust::run(temp_args)?;

//     // get_files(out_dir).zip(get_files).into_iter()
//     let old_files = get_files(args.out_dir);
//     let new_files = get_files(temp_path).iter()
//         .filter_map(|(filename, content)| {
//             old_files.get(filename)
//                 .map_or(None, |old_content| {
//                     if content == old_content {
//                         None
//                     } else {
//                         Some((filename, content))
//                     }
//                 })
//         })

//     // drop(temp_dir);
//     Ok(())
// }

// fn get_updated_files() {
// }

fn get_files(dir: &Path) -> HashMap<String, String> {
    walkdir::WalkDir::new(dir)
        .into_iter()
        .filter_map(|entry| entry.ok())
        .filter(|entry| entry.path().is_file())
        .map(|entry| {
            let path = entry.into_path();
            let content = std::fs::read_to_string(&path).unwrap();
            (String::from(path.file_name().unwrap()), content)
        })
        .collect::<HashMap<PathBuf, String>>()
}

const TEMP_FILES: [&str; 3] = ["1", "2", "3"];

#[test]
fn get_files_test() {
    let temp_dir = tempfile::tempdir().unwrap();
    println!("{}", temp_dir.path().display());
    for filename in TEMP_FILES.iter() {
        let path = temp_dir.path().join(filename);
        let file = std::fs::File::create(path).unwrap();
        file.write_all(filename);
    }
    let files = get_files(temp_dir.path());
    for (key, value) in files {
        println!("{}: {}", key.to_str().unwrap(), value);
    }
    for filename in TEMP_FILES.iter() {
        assert_eq!(files.get(filename), Some(String::from(*filename)));
    }
}
