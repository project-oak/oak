//
// Copyright 2026 The Project Oak Authors
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

//! Linux VM management for benchmarking.

use std::{
    os::fd::AsFd,
    path::Path,
    process::{Child, Command, ExitStatus, Stdio},
};

use anyhow::{Context, Result, anyhow};

/// Configuration for launching a Linux VM.
pub struct VmConfig<'a> {
    /// Path to the VM image (qcow2).
    pub image: &'a Path,
    /// Path to run_vm.sh script.
    pub run_vm_script: &'a Path,
    /// Memory size (e.g., "1G").
    pub memory_size: &'a str,
    /// Port for benchmark server.
    pub port: u16,
    /// Number of vCPUs to give the VM.
    ///
    /// The restricted kernel runs on a single vCPU and cannot be given more,
    /// so a comparison is only matched when the VM gets one as well.
    pub cpus: u8,
    /// Enable AMD SEV-SNP.
    pub enable_snp: bool,
}

/// A running Linux VM instance.
pub struct LinuxVm {
    child: Child,
}

impl LinuxVm {
    /// Boot a new Linux VM with the given configuration.
    pub fn boot(config: &VmConfig) -> Result<Self> {
        // Verify script exists
        if !config.run_vm_script.exists() {
            return Err(anyhow!(
                "run_vm.sh script not found: {}. Are you running from the workspace root?",
                config.run_vm_script.display()
            ));
        }

        let mut cmd = Command::new(config.run_vm_script);
        cmd.args([
            &format!("--image={}", config.image.display()),
            &format!("--port={}", config.port),
            &format!("--memory={}", config.memory_size),
            &format!("--cpus={}", config.cpus),
            "--headless",
        ]);

        if config.enable_snp {
            cmd.arg("--enable-snp");
        }

        // The script reports its own failures on stdout, so discarding stdout
        // turns "QEMU is not on the path" into a readiness timeout minutes
        // later. It is sent to our stderr instead of our stdout, which carries
        // the benchmark's CSV.
        let script_output = std::io::stderr()
            .as_fd()
            .try_clone_to_owned()
            .context("duplicating stderr for the VM script")?;

        let child = cmd
            .stdin(Stdio::null())
            .stdout(Stdio::from(script_output))
            .stderr(Stdio::inherit())
            .spawn()
            .context("starting run_vm.sh")?;

        Ok(Self { child })
    }

    /// Returns how the VMM exited, or `None` while it is still running.
    ///
    /// A readiness loop needs this: without it, a VMM that never started is
    /// indistinguishable from a guest that is still booting, and the caller
    /// waits out its whole timeout before reporting the wrong cause.
    pub fn exited(&mut self) -> Result<Option<ExitStatus>> {
        self.child.try_wait().context("checking whether the VM is still running")
    }

    /// Get the process ID of the VM.
    pub fn pid(&self) -> Option<u32> {
        Some(self.child.id())
    }

    /// Shut down the VM.
    pub fn shutdown(mut self) -> Result<()> {
        self.child.kill().ok();
        self.child.wait()?;
        Ok(())
    }
}

impl Drop for LinuxVm {
    fn drop(&mut self) {
        // Best effort cleanup if not explicitly shut down.
        self.child.kill().ok();
    }
}
