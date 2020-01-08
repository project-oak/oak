use std::process::Command;

fn main() {
    run_process(
        "fidlc",
        &[
            "--json",
            "../fidl/abitest.json",
            "--files",
            "../fidl/abitest.fidl",
        ],
    );

    run_process(
        "fidlgen",
        &[
            "--json",
            "../fidl/abitest.json",
            "--generators",
            "rust",
            "--include-base",
            ".",
            "--output-base",
            "src/fidl",
        ],
    );
}

fn run_process(executable: &str, args: &[&str]) {
    let child = Command::new(executable)
        .args(args)
        .spawn()
        .expect("could not spawn command");
    let output = child
        .wait_with_output()
        .expect("could not wait for command to terminate");
    if !output.status.success() {
        panic!(
            "could not run command: {}",
            std::str::from_utf8(&output.stdout).expect("could not parse command output")
        );
    }
}
