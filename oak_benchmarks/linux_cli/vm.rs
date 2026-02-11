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
    path::Path,
    process::{Child, Command, Stdio},
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
            "--headless",
        ]);

        if config.enable_snp {
            cmd.arg("--enable-snp");
        }

        // Suppress script output (the script uses exec, so QEMU replaces it)
        let child = cmd
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped()) // Keep stderr for debugging
            .spawn()
            .context("Failed to start run_vm.sh")?;

        Ok(Self { child })
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
