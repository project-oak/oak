//
// Copyright 2021 The Project Oak Authors
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

use crate::{files::*, internal::*};
use maplit::hashmap;
use std::collections::HashMap;
use strum::IntoEnumIterator;

#[cfg(target_os = "macos")]
const DEFAULT_SERVER_RUST_TARGET: &str = "x86_64-apple-darwin";
#[cfg(not(target_os = "macos"))]
const DEFAULT_SERVER_RUST_TARGET: &str = "x86_64-unknown-linux-musl";

#[cfg(target_os = "macos")]
const DEFAULT_EXAMPLE_BACKEND_RUST_TARGET: &str = "x86_64-apple-darwin";
#[cfg(not(target_os = "macos"))]
const DEFAULT_EXAMPLE_BACKEND_RUST_TARGET: &str = "x86_64-unknown-linux-gnu";

pub const ALL_CLIENTS: &str = "all";
pub const NO_CLIENTS: &str = "none";

/// Holds the components for running an example in Oak: a `server` running the given
/// `applications` listening to the `clients` and passing requests to `backends`.
/// Configured through `example.toml` files.
#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct OakExample {
    name: String,
    #[serde(default)]
    server: Server,
    #[serde(default)]
    backends: HashMap<String, Executable>,
    applications: HashMap<String, Application>,
    clients: HashMap<String, Executable>,
}

impl OakExample {
    fn has_oak_functions_application(&self) -> bool {
        self.applications.values().any(|app| match app {
            Application::OakFunctions(_) => true,
        })
    }
}

/// Identify the application the server runs.
#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
#[serde(tag = "type")]
enum Application {
    OakFunctions(OakFunctionsApplication),
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct OakFunctionsApplication {
    target: Target,
    wizer: Option<WizerOpt>,
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct WizerOpt {
    input: String,
    output: String,
}

#[derive(serde::Deserialize, Debug, Default)]
#[serde(deny_unknown_fields)]
struct Server {
    #[serde(default)]
    additional_args: Vec<String>,
    #[serde(default)]
    server_variant: ServerVariant,
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub enum Target {
    Bazel {
        bazel_target: String,
        #[serde(default)]
        config: String,
    },
    Cargo {
        cargo_manifest: String,
        #[serde(default)]
        additional_build_args: Vec<String>,
    },
    Npm {
        package_directory: String,
    },
    Shell {
        run_script: String,
        build_script: String,
    },
}

#[derive(serde::Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct Executable {
    #[serde(flatten)]
    target: Target,
    #[serde(default)]
    additional_args: Vec<String>,
}

impl OakFunctionsApplication {
    fn construct_application_build_steps(&self, example_name: &str) -> Vec<Step> {
        let mut result = vec![build_wasm_module(example_name, &self.target, example_name)];
        // If Wizer configuration is specified, run Wizer after the build.
        if let Some(wizer) = &self.wizer {
            result.push(run_wizer(&wizer.input, &wizer.output));
        }
        result
    }

    fn construct_server_run_step(&self, example: &OakFunctionsExample, run_clients: Step) -> Step {
        let opt = &example.options;
        let run_server = run_oak_functions_server(&example.example.server);

        if opt.build_client.client_variant == NO_CLIENTS {
            Step::Single {
                name: "run server".to_string(),
                command: run_server,
            }
        } else {
            Step::WithBackground {
                name: "background server".to_string(),
                background: run_server,
                foreground: Box::new(run_clients),
            }
        }
    }
}

/// Construct run and build steps an `OakExample`.
trait OakExampleSteps {
    fn get_backends(&self) -> &HashMap<String, Executable>;

    fn get_build_client(&self) -> &BuildClient;

    /// Constructs application build steps.
    fn construct_application_build_steps(&self) -> Vec<Step>;

    /// Constructs run step for the example server.
    fn construct_server_run_step(&self, run_clients: Step) -> Step;

    /// Constructs build steps for the backends.
    fn construct_backend_build_steps(&self) -> Vec<Step> {
        self.get_backends()
            .iter()
            .map(move |(name, backend)| Step::Single {
                name: name.to_string(),
                command: build(&backend.target, self.get_build_client()),
            })
            .collect()
    }

    /// Recursively constructs run steps for the backends.
    fn construct_backend_run_steps(&self, run_server_clients: Step) -> Step {
        self.get_backends()
            .iter()
            // First iteration includes `run_server_clients` as a foreground step.
            .fold(run_server_clients, |backend_steps, (name, backend)| {
                Step::WithBackground {
                    name: name.to_string(),
                    // Each `backend` is included as background step.
                    background: run(backend, self.get_build_client(), Vec::new()),
                    foreground: Box::new(backend_steps),
                }
            })
    }
}
pub struct OakFunctionsExample<'a> {
    example: &'a OakExample,
    applications: HashMap<String, &'a OakFunctionsApplication>,
    options: RunOakExamplesOpt,
}

impl<'a> OakFunctionsExample<'a> {
    fn new(example: &'a OakExample, options: RunOakExamplesOpt) -> Self {
        let applications =
            example
                .applications
                .iter()
                .fold(hashmap! {}, |mut apps, app| match app {
                    (name, Application::OakFunctions(ref app)) => {
                        apps.insert(name.clone(), app);
                        apps
                    }
                });

        OakFunctionsExample {
            example,
            applications,
            options,
        }
    }
}

impl OakExampleSteps for OakFunctionsExample<'_> {
    fn get_backends(&self) -> &HashMap<String, Executable> {
        &self.example.backends
    }

    fn get_build_client(&self) -> &BuildClient {
        &self.options.build_client
    }

    fn construct_application_build_steps(&self) -> Vec<Step> {
        let app_variant = self.options.application_variant.as_str();
        match self.applications.get(app_variant) {
            None => vec![],
            Some(app) => app.construct_application_build_steps(&self.example.name),
        }
    }

    fn construct_server_run_step(&self, run_clients: Step) -> Step {
        let app_variant = self.options.application_variant.as_str();
        match self.applications.get(app_variant) {
            None => run_clients,
            Some(app) => app.construct_server_run_step(self, run_clients),
        }
    }
}

pub fn run_oak_functions_examples(opt: &RunOakExamplesOpt, scope: &Scope) -> Step {
    let examples: Vec<OakExample> = example_toml_files(scope)
        .map(|path| {
            toml::from_str(&read_file(&path)).unwrap_or_else(|err| {
                panic!("could not parse example manifest file {:?}: {}", path, err)
            })
        })
        .filter(|example: &OakExample| example.has_oak_functions_application())
        .collect();

    Step::Multiple {
        name: "oak-functions examples".to_string(),
        steps: examples
            .iter()
            .filter(|example| match &opt.example_name {
                Some(example_name) => &example.name == example_name,
                None => true,
            })
            .map(|example| OakFunctionsExample::new(example, opt.clone()))
            .map(|example| run_oak_functions_example(&example))
            .collect(),
    }
}

/// Build every variant of the function server.
/// It's easier to always build all variants than to keep track of which variant to build and
/// the overhead of building all variants is acceptable.
pub fn build_oak_functions_server_variants(opt: &BuildServerOpt) -> Step {
    Step::Multiple {
        name: "cargo build all variants of function server".to_string(),
        steps: ServerVariant::iter()
            .map(|variant| build_rust_binary(variant.path_to_manifest(), opt))
            .collect(),
    }
}

fn run_oak_functions_example(example: &OakFunctionsExample) -> Step {
    let opt = &example.options;

    // Build steps for running clients
    let run_clients = run_clients(
        example.example,
        &opt.build_client,
        opt.client_additional_args.clone(),
    );

    // Build any backend server
    #[allow(clippy::collapsible_if)]
    let run_backend_server_clients: Step = if opt.run_server.unwrap_or(true) {
        let run_server_clients = example.construct_server_run_step(run_clients);
        example.construct_backend_run_steps(run_server_clients)
    } else {
        run_clients
    };

    Step::Multiple {
        name: example.example.name.to_string(),
        steps: vec![
            example.construct_application_build_steps(),
            if opt.run_server.unwrap_or(true) {
                // Build (all variants of) the server first so that when running a variant in the
                // next step it will start up faster.
                vec![build_oak_functions_server_variants(&opt.build_server)]
            } else {
                vec![]
            },
            if opt.build_docker {
                vec![build_docker(example.example)]
            } else {
                vec![]
            },
            example.construct_backend_build_steps(),
            vec![Step::Multiple {
                name: "run".to_string(),
                steps: vec![run_backend_server_clients],
            }],
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>(),
    }
}

pub fn build_oak_functions_example(opt: &RunOakExamplesOpt, scope: &Scope) -> Step {
    let example_name = &opt
        .example_name
        .as_ref()
        .expect("--example-name must be specified")
        .clone();

    let example: OakExample = example_toml_files(scope)
        .map(|path| {
            toml::from_str(&read_file(&path)).unwrap_or_else(|err| {
                panic!("could not parse example manifest file {:?}: {}", path, err)
            })
        })
        .find(|example: &OakExample| &example.name == example_name)
        .filter(|example| example.has_oak_functions_application())
        .expect("could not find the specified functions example, try with `--scope=all`");

    // Build steps for building clients
    let build_client = Step::Multiple {
        name: "build clients".to_string(),
        steps: example
            .clients
            .iter()
            .filter(|(name, _)| match opt.build_client.client_variant.as_str() {
                ALL_CLIENTS => true,
                client => *name == client,
            })
            .map(|(name, client)| Step::Single {
                name: format!("build{}", name),
                command: build(&client.target, &opt.build_client),
            })
            .collect(),
    };

    let oak_functions_example = OakFunctionsExample::new(&example, opt.clone());

    Step::Multiple {
        name: example.name.to_string(),
        steps: vec![
            oak_functions_example.construct_application_build_steps(),
            // Build the server first so that when running it in the next step it will start up
            // faster.
            vec![build_oak_functions_server_variants(&opt.build_server)],
            if opt.build_docker {
                vec![build_docker(&example)]
            } else {
                vec![]
            },
            oak_functions_example.construct_backend_build_steps(),
            vec![build_client],
        ]
        .into_iter()
        .flatten()
        .collect::<Vec<_>>(),
    }
}

pub fn build_wasm_module(name: &str, target: &Target, example_name: &str) -> Step {
    match target {
        Target::Cargo {
            cargo_manifest,
            additional_build_args,
        } => {
            let metadata = cargo_metadata::MetadataCommand::new()
                .manifest_path(cargo_manifest)
                .exec()
                .unwrap();
            Step::Single {
                name: format!("wasm:{}:{}", name, cargo_manifest),
                command: Cmd::new(
                    "cargo",
                    // Keep this in sync with `/oak_functions/sdk/test/utils/src/lib.rs`.
                    spread![
                        // `--out-dir` is unstable and requires `-Zunstable-options`.
                        "-Zunstable-options".to_string(),
                        "build".to_string(),
                        "--target=wasm32-unknown-unknown".to_string(),
                        // Use a fixed `--target-dir`, because it influences the SHA256 hash of the
                        // Wasm module.
                        //
                        // This directory is separate from `examples/target` because it is used by
                        // `cargo test`, which also executes [`oak_tests::compile_rust_wasm`] and
                        // thus runs `cargo build` inside it. It may lead to errors, since
                        // dependencies may be recompiled by `cargo build` and `cargo test` will
                        // fail to continue.
                        format!("--target-dir={}/wasm", metadata.target_directory),
                        format!("--manifest-path={}", cargo_manifest),
                        format!("--out-dir={}/bin", metadata.workspace_root),
                        "--release".to_string(),
                        ...additional_build_args
                    ],
                ),
            }
        }
        Target::Bazel {
            bazel_target,
            config,
        } => Step::Multiple {
            name: "wasm".to_string(),
            steps: vec![
                Step::Single {
                    name: format!("wasm:{}:{}", name, bazel_target),
                    command: Cmd::new(
                        "bazel",
                        vec![
                            "build".to_string(),
                            format!("--config={}", config),
                            bazel_target.to_string(),
                        ],
                    ),
                },
                Step::Single {
                    name: "create bin folder".to_string(),
                    command: Cmd::new(
                        "mkdir",
                        vec!["-p".to_string(), format!("examples/{}/bin", example_name)],
                    ),
                },
                Step::Single {
                    name: "copy wasm module".to_string(),
                    command: Cmd::new(
                        "cp",
                        vec![
                            "-f".to_string(),
                            format!(
                                "bazel-{}-bin/{}",
                                match config.as_ref() {
                                    "emscripten" => "emscripten",
                                    "wasm32" => "wasm",
                                    _ => panic!("unsupported Bazel config: {}", config),
                                },
                                bazel_target.replace("//", "").replace(':', "/")
                            ),
                            format!("examples/{}/bin", example_name),
                        ],
                    ),
                },
            ],
        },
        Target::Npm { .. } => todo!(),
        Target::Shell { .. } => todo!(),
    }
}

fn run_wizer(input: &str, output: &str) -> Step {
    Step::Single {
        name: format!("wizer:{}:{}", input, output),
        command: Cmd::new(
            "wizer",
            // See https://github.com/bytecodealliance/wizer#example-usage.
            spread![format!("{}", input), format!("-o={}", output),],
        ),
    }
}

fn run_oak_functions_server(server: &Server) -> Box<dyn Runnable> {
    Cmd::new(
        server.server_variant.path_to_executable(),
        spread![
            ...server.additional_args.clone(),
        ],
    )
}

fn run_clients(
    example: &OakExample,
    build_client: &BuildClient,
    client_additional_args: Vec<String>,
) -> Step {
    Step::Multiple {
        name: "run clients".to_string(),
        steps: example
            .clients
            .iter()
            .filter(|(name, _)| match build_client.client_variant.as_str() {
                ALL_CLIENTS => true,
                client => *name == client,
            })
            .map(|(name, client)| {
                run_client(name, client, build_client, client_additional_args.clone())
            })
            .collect(),
    }
}

fn run_client(
    name: &str,
    executable: &Executable,
    opt: &BuildClient,
    additional_args: Vec<String>,
) -> Step {
    Step::Multiple {
        name: name.to_string(),
        steps: vec![
            Step::Single {
                name: "build".to_string(),
                command: build(&executable.target, opt),
            },
            Step::Single {
                name: "run".to_string(),
                command: run(executable, opt, additional_args),
            },
        ],
    }
}

fn build_docker(example: &OakExample) -> Step {
    Step::Multiple {
        name: "docker".to_string(),
        steps: vec![
            Step::Single {
                name: "build server image".to_string(),
                command: Cmd::new(
                    "docker",
                    &[
                        "build",
                        "--tag=oak_docker",
                        "--file=./oak_loader/Dockerfile",
                        "./oak_loader",
                    ],
                ),
            },
            Step::Single {
                name: "build example image".to_string(),
                command: Cmd::new(
                    "docker",
                    &[
                        "build",
                        &format!("--tag={}", example.name),
                        "--file=./examples/Dockerfile",
                        // An example may have more than one application, and the applications may
                        // have arbitrary names, so this is an approximation of the expected
                        // application file name of one of them.
                        &format!("--build-arg=application_file_name={}.oak", example.name),
                        &format!("./examples/{}", example.name),
                    ],
                ),
            },
            Step::Single {
                name: "save example image".to_string(),
                command: Cmd::new(
                    "docker",
                    &[
                        "save",
                        &example.name,
                        &format!(
                            "--output=./examples/{}/bin/{}.tar",
                            example.name, example.name
                        ),
                    ],
                ),
            },
        ],
    }
}

fn build(target: &Target, opt: &BuildClient) -> Box<dyn Runnable> {
    match target {
        Target::Cargo {
            cargo_manifest,
            additional_build_args,
        } => Cmd::new(
            "cargo",
            spread![
                "build".to_string(),
                "--release".to_string(),
                format!(
                    "--target={}",
                    opt.client_rust_target
                        .as_deref()
                        .unwrap_or(DEFAULT_EXAMPLE_BACKEND_RUST_TARGET)
                ),
                format!("--manifest-path={}", cargo_manifest),
                ...additional_build_args,
            ],
        ),
        Target::Bazel {
            bazel_target,
            config,
        } => Cmd::new(
            "bazel",
            spread![
                "build".to_string(),
                ...if config.is_empty() {
                    vec![]
                } else {
                    vec![format!("--config={}", config)]
                },
                bazel_target.to_string(),
            ],
        ),
        Target::Npm { package_directory } => Cmd::new(
            "npm",
            vec!["ci".to_string(), format!("--prefix={}", package_directory)],
        ),
        Target::Shell { build_script, .. } => Cmd::new("bash", &["-c", build_script]),
    }
}

fn run(
    executable: &Executable,
    opt: &BuildClient,
    additional_args: Vec<String>,
) -> Box<dyn Runnable> {
    match &executable.target {
        Target::Cargo {
            cargo_manifest,
            additional_build_args,
        } => Cmd::new(
            "cargo",
            spread![
                "run".to_string(),
                "--release".to_string(),
                format!("--target={}", opt.client_rust_target.as_deref().unwrap_or(DEFAULT_EXAMPLE_BACKEND_RUST_TARGET)),
                format!("--manifest-path={}", cargo_manifest),
                ...additional_build_args,
                "--".to_string(),
                ...executable.additional_args.clone(),
                ...additional_args,
            ],
        ),
        Target::Bazel {
            bazel_target,
            config,
        } => Cmd::new(
            "bazel",
            spread![
                "run".to_string(),
                ...if config.is_empty() {
                    vec![]
                } else {
                    vec![format!("--config={}", config)]
                },
                "--".to_string(),
                bazel_target.to_string(),
                "--ca_cert_path=../../../../../../../../../examples/certs/local/ca.pem".to_string(),
                ...executable.additional_args.clone(),
                ...additional_args,
            ],
        ),
        Target::Npm { package_directory } => Cmd::new(
            "npm",
            vec![
                "start".to_string(),
                format!("--prefix={}", package_directory),
            ],
        ),
        Target::Shell { run_script, .. } => Cmd::new("bash", &["-c", run_script]),
    }
}

fn build_rust_binary(manifest_dir: &str, opt: &BuildServerOpt) -> Step {
    Step::Single {
        name: format!("build rust binary {}", manifest_dir),
        command: Cmd::new(
            "cargo",
            spread![
                ...match &opt.server_rust_toolchain {
                    // This overrides the toolchain used by `rustup` to invoke the actual
                    // `cargo` binary.
                    // See https://github.com/rust-lang/rustup#toolchain-override-shorthand
                    Some(server_rust_toolchain) => vec![format!("+{}", server_rust_toolchain)],
                    None => vec![],
                },
                "build".to_string(),
                format!("--manifest-path={}/Cargo.toml", manifest_dir),
                format!("--target={}", opt.server_rust_target.as_deref().unwrap_or(DEFAULT_SERVER_RUST_TARGET)),
                "--release".to_string(),
            ],
        ),
    }
}
