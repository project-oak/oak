//
// Copyright 2023 The Project Oak Authors
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

use log::info;
use std::{
    fs::File,
    io::{BufRead, BufReader},
};
use subprocess::Exec;

mod init;

const DOCKER_COMMAND_PATH: &str = "/docker_cmd";

fn main() -> ! {
    simple_logger::SimpleLogger::new().init().unwrap();

    // Set up the Linux environment, since we expect to be the initial process.
    init::init().unwrap();

    // For now, just set PATH to some common locations. Docker image has information about
    // the environment variables that need to be set up before the container is launched. We
    // should use that information to set up all the necessary environment variables.
    std::env::set_var("PATH", "/usr/local/bin:/sbin:/usr/sbin:/bin:/usr/bin");

    let file = File::open(DOCKER_COMMAND_PATH).expect("Error reading file");
    let content_vec = BufReader::new(file)
        .lines()
        .map(|line| line.expect("Could not read line from docker command file!"))
        .collect::<Vec<_>>();
    let (cmd, args) = content_vec.split_at(1);

    info!("Docker command: {:?} {:?}", &cmd[0], args);

    let exit_status = Exec::cmd(&cmd[0]).args(args).join();
    match exit_status {
        Ok(_) => println!("Docker command finished successfully!"),
        Err(error) => println!("Error running docker command: {:?}", error),
    }

    // Linux does not expect the initial process to ever exit, so we keep sleeping 1 second at a
    // time.
    loop {
        nix::unistd::sleep(1);
    }
}
