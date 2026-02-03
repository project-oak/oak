//
// Copyright 2024 The Project Oak Authors
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

use std::{
    borrow::Borrow,
    io::BufReader,
    os::{linux::fs::MetadataExt, unix::fs::FileTypeExt},
    path::Path,
};

use anyhow::{Context, Result};
use oci_spec::runtime::{LinuxDeviceType, Spec};

mod cdi_spec {
    use std::collections::HashMap;

    use anyhow::{Context, Result, bail};
    use oci_spec::runtime::{
        HookBuilder, Linux, LinuxDeviceBuilder, LinuxDeviceCgroupBuilder, LinuxDeviceType,
        LinuxResources, MountBuilder, Spec,
    };
    use serde::Deserialize;

    /// CDI specification, version 0.7.0
    ///
    /// See <https://github.com/cncf-tags/container-device-interface/blob/main/SPEC.md> for more details.
    #[derive(Deserialize)]
    #[allow(dead_code)]
    #[serde(rename_all = "camelCase")]
    pub struct Cdi {
        pub cdi_version: String,
        pub kind: String,
        pub devices: Vec<Device>,
        pub container_edits: Option<ContainerEdits>,
        #[serde(default)]
        pub annotations: HashMap<String, String>,
    }

    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct Device {
        pub name: String,
        pub container_edits: Option<ContainerEdits>,
    }

    impl Device {
        pub fn inject(&self, fs: &dyn super::Fs, target: &mut Spec) -> Result<()> {
            if let Some(container_edits) = &self.container_edits {
                container_edits.inject(fs, target)?;
            }
            Ok(())
        }
    }

    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase")]
    #[allow(dead_code)]
    pub struct ContainerEdits {
        #[serde(default)]
        pub env: Vec<String>,
        pub device_nodes: Vec<DeviceNode>,
        #[serde(default)]
        pub mounts: Vec<Mounts>,
        #[serde(default)]
        pub hooks: Vec<Hooks>,
        #[serde(default, rename = "additionalGIDs")]
        pub additional_gids: Vec<u32>,
        pub intel_rdt: Option<IntelRdt>,
    }

    impl ContainerEdits {
        pub fn inject(&self, fs: &dyn super::Fs, target: &mut Spec) -> Result<()> {
            let process =
                target.process_mut().as_mut().context("OCI spec does not specify process")?;
            let env = process.env_mut().get_or_insert_with(Vec::new);
            env.extend_from_slice(&self.env);

            for node in &self.device_nodes {
                node.inject(fs, target)?;
            }

            for mount in &self.mounts {
                mount.inject(target)?;
            }

            for hook in &self.hooks {
                hook.inject(target)?;
            }
            Ok(())
        }
    }

    #[derive(Clone, Deserialize)]
    #[serde(rename_all = "camelCase")]
    #[allow(dead_code)]
    pub struct DeviceNode {
        pub path: String,
        pub host_path: Option<String>,
        pub r#type: Option<LinuxDeviceType>,
        pub major: Option<u64>,
        pub minor: Option<u64>,
        pub file_mode: Option<u64>,
        pub permissions: Option<String>,
        pub uid: Option<u32>,
        pub gid: Option<u32>,
    }

    impl DeviceNode {
        pub fn inject(&self, fs: &dyn super::Fs, target: &mut Spec) -> Result<()> {
            let mut builder = LinuxDeviceBuilder::default();
            let mut cgroup_builder = LinuxDeviceCgroupBuilder::default().allow(true).access("rwm");
            // Fill in any blanks that would still be required.
            builder = builder.path(&self.path);
            let host_path = self.host_path.as_ref().unwrap_or(&self.path);

            let typ = self.r#type.map_or_else(|| fs.file_type(host_path), Ok)?;
            builder = builder.typ(typ);
            cgroup_builder = cgroup_builder.typ(typ);
            if typ != LinuxDeviceType::P {
                let major = self.major.map_or_else(|| fs.major(host_path), Ok)?.try_into()?;
                let minor = self.minor.map_or_else(|| fs.minor(host_path), Ok)?.try_into()?;
                builder = builder.major::<i64>(major);
                builder = builder.minor::<i64>(minor);
                cgroup_builder = cgroup_builder.major(major);
                cgroup_builder = cgroup_builder.minor(minor);
            }

            let linux = target.linux_mut().get_or_insert_with(Linux::default);
            linux.devices_mut().get_or_insert_with(Vec::new).push(builder.build()?);
            linux
                .resources_mut()
                .get_or_insert_with(LinuxResources::default)
                .devices_mut()
                .get_or_insert_with(Vec::new)
                .push(cgroup_builder.build()?);

            Ok(())
        }
    }

    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase")]
    #[allow(dead_code)]
    pub struct Mounts {
        pub host_path: String,
        pub container_path: String,
        pub r#type: Option<String>,
        #[serde(default)]
        pub options: Vec<String>,
    }

    impl Mounts {
        pub fn inject(&self, target: &mut Spec) -> Result<()> {
            let mounts = target.mounts_mut().get_or_insert_with(Vec::new);
            let builder = MountBuilder::default()
                .source(&self.host_path)
                .destination(&self.container_path)
                .options(&self.options[..]);
            mounts.push(builder.build()?);
            Ok(())
        }
    }

    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase")]
    pub struct Hooks {
        pub hook_name: String,
        pub path: String,
        #[serde(default)]
        pub args: Vec<String>,
        pub env: Option<Vec<String>>,
        pub timeout: Option<i64>,
    }

    impl Hooks {
        pub fn inject(&self, target: &mut Spec) -> Result<()> {
            if self.hook_name == "createContainer" {
                let hooks = target.hooks_mut().get_or_insert_with(Default::default);
                let mut builder = HookBuilder::default().path(&self.path).args(&self.args[..]);
                if let Some(env) = &self.env {
                    builder = builder.env(&env[..]);
                }
                if let Some(timeout) = self.timeout {
                    builder = builder.timeout(timeout);
                }
                hooks.create_container_mut().get_or_insert_with(Vec::new).push(builder.build()?);
            } else {
                bail!("only createContainer hooks are currently supported by the orchestrator");
            }
            Ok(())
        }
    }

    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase")]
    #[allow(dead_code)]
    pub struct IntelRdt {
        #[serde(rename = "closID")]
        pub clos_id: Option<String>,
        pub l3_cache_schema: Option<String>,
        pub mem_bw_schema: Option<String>,
        #[serde(rename = "enableCMT")]
        pub enable_cmt: Option<bool>,
        #[serde(rename = "enableMBM")]
        pub enable_mbm: Option<bool>,
    }
}

// Filesystem wrapper to abstract away the fact that we probably won't have
// nvidia devices on the test machine.
trait Fs {
    fn file_type(&self, path: &str) -> Result<LinuxDeviceType>;
    fn major(&self, path: &str) -> Result<u64>;
    fn minor(&self, path: &str) -> Result<u64>;
}
struct RealFileSystem {}
impl Fs for RealFileSystem {
    fn file_type(&self, path: &str) -> Result<LinuxDeviceType> {
        let stat = std::fs::metadata(path)
            .context(format!("reading host path metadata for device: {}", path))?;
        if stat.file_type().is_char_device() {
            Ok(LinuxDeviceType::C)
        } else if stat.file_type().is_block_device() {
            Ok(LinuxDeviceType::B)
        } else if stat.file_type().is_fifo() {
            Ok(LinuxDeviceType::P)
        } else {
            anyhow::bail!("unexpected device type")
        }
    }

    fn major(&self, path: &str) -> Result<u64> {
        let stat = std::fs::metadata(path)
            .context(format!("reading host path metadata for device: {}", path))?;
        Ok(nix::sys::stat::major(stat.st_rdev()))
    }

    fn minor(&self, path: &str) -> Result<u64> {
        let stat = std::fs::metadata(path)
            .context(format!("reading host path metadata for device: {}", path))?;
        Ok(nix::sys::stat::minor(stat.st_rdev()))
    }
}

pub struct CdiSpec {
    spec: cdi_spec::Cdi,
    fs: Box<dyn Fs>,
}

#[allow(dead_code)]
impl CdiSpec {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self> {
        let file = std::fs::File::open(path).context("could not open CDI spec file")?;
        let rdr = BufReader::new(file);
        Ok(Self {
            spec: serde_json::from_reader(rdr).context("could not parse CDI spec")?,
            fs: Box::new(RealFileSystem {}),
        })
    }

    fn new_from_str(fs: Box<dyn Fs>, contents: &str) -> Result<Self> {
        Ok(Self { spec: serde_json::from_str(contents).context("could not parse CDI spec")?, fs })
    }

    pub fn kind(&self) -> &str {
        &self.spec.kind
    }

    pub fn devices(&self) -> Vec<&str> {
        self.spec.devices.iter().map(|device| device.name.as_str()).collect()
    }

    pub fn inject(&self, name: &str, oci_spec: &mut Spec) -> Result<bool> {
        if let Some(device) = self.spec.devices.iter().find(|dev| dev.name == name) {
            if let Some(container_edits) = &self.spec.container_edits {
                container_edits.inject(self.fs.borrow(), oci_spec)?;
            }
            device.inject(self.fs.borrow(), oci_spec)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use anyhow::anyhow;

    use super::*;

    struct FakeFileSystem {
        pub fakes: HashMap<&'static str, (LinuxDeviceType, u64, u64)>,
    }
    impl Fs for FakeFileSystem {
        fn file_type(&self, path: &str) -> Result<LinuxDeviceType> {
            self.fakes.get(path).ok_or(anyhow!("path not found")).map(|(typ, _, _)| *typ)
        }

        fn major(&self, path: &str) -> Result<u64> {
            self.fakes.get(path).ok_or(anyhow!("path not found")).map(|(_, major, _)| *major)
        }

        fn minor(&self, path: &str) -> Result<u64> {
            self.fakes.get(path).ok_or(anyhow!("path not found")).map(|(_, _, minor)| *minor)
        }
    }

    static DEVICES: [(&str, (LinuxDeviceType, u64, u64)); 4] = [
        ("/dev/nvidia0", (LinuxDeviceType::C, 195, 0)),
        ("/dev/nvidia-uvm", (LinuxDeviceType::C, 249, 0)),
        ("/dev/nvidia-uvm-tools", (LinuxDeviceType::C, 249, 1)),
        ("/dev/nvidiactl", (LinuxDeviceType::C, 195, 255)),
    ];

    static SPEC_STR: &str = include_str!("../testdata/cdi.json");
    static BASE_OCI_SPEC: &str = include_str!("../testdata/oci_spec_base.json");
    static TARGET_OCI_SPEC: &str = include_str!("../testdata/oci_spec_target.json");

    #[test]
    pub fn construct_from_str() {
        let spec = CdiSpec::new_from_str(
            Box::new(FakeFileSystem { fakes: HashMap::from(DEVICES) }),
            SPEC_STR,
        )
        .unwrap();
        assert_eq!(spec.kind(), "nvidia.com/gpu");
        assert_eq!(spec.devices(), vec!("0", "GPU-955ef018-3bd9-5f27-80b3-fa20ee8d19c5", "all"));
    }

    #[test]
    pub fn inject() {
        let mut oci_spec = serde_json::from_str(BASE_OCI_SPEC).unwrap();
        let cdi_spec = CdiSpec::new_from_str(
            Box::new(FakeFileSystem { fakes: HashMap::from(DEVICES) }),
            SPEC_STR,
        )
        .unwrap();
        cdi_spec.inject("all", &mut oci_spec).unwrap();
        let mut target_oci_spec: Spec = serde_json::from_str(TARGET_OCI_SPEC).unwrap();

        // Remove some ambiguity: sort some fields.
        oci_spec
            .mounts_mut()
            .as_mut()
            .unwrap()
            .sort_by_key(|mount| mount.source().as_ref().unwrap().clone());
        target_oci_spec
            .mounts_mut()
            .as_mut()
            .unwrap()
            .sort_by_key(|mount| mount.source().as_ref().unwrap().clone());
        // Ignore capatibilites as they're a pain to sort.
        oci_spec.process_mut().as_mut().unwrap().set_capabilities(None);
        target_oci_spec.process_mut().as_mut().unwrap().set_capabilities(None);

        // Otherwise, the results should be equal.
        assert_eq!(oci_spec, target_oci_spec);
    }
}
