//
// Copyright 2020 The Project Oak Authors
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

/// This module defines a trait and an implementation for representing the [`Runtime`] as
/// a Graphviz dot graph. This is used in the introspection service.
use crate::{ChannelHalf, ChannelHalfDirection, NodeId, NodeInfo, Runtime};
use itertools::Itertools;
use log::info;
use std::{collections::HashSet, fmt::Write, string::String};

/// Trait that gives an identifier for a data structure that is suitable for
/// use with Graphviz/Dot.
pub trait DotIdentifier {
    fn dot_id(&self) -> String;
}

/// Trait that returns the path at which the debug introspection server will
/// show a page for a data structure.
pub trait HtmlPath {
    fn html_path(&self) -> String;
}

impl DotIdentifier for NodeId {
    fn dot_id(&self) -> String {
        format!("node{}", self.0)
    }
}

impl HtmlPath for NodeId {
    fn html_path(&self) -> String {
        format!("/node/{}", self.0)
    }
}

impl DotIdentifier for (NodeId, oak_abi::Handle) {
    fn dot_id(&self) -> String {
        format!("{}_{}", self.0.dot_id(), self.1)
    }
}

impl HtmlPath for (NodeId, oak_abi::Handle) {
    fn html_path(&self) -> String {
        format!("{}/{}", self.0.html_path(), self.1)
    }
}

// Graph-related methods for the Runtime.
impl Runtime {
    /// Generate a Graphviz dot graph that shows the current shape of the Nodes and Channels in
    /// the `Runtime`.
    pub fn graph(&self) -> String {
        let mut s = String::new();
        writeln!(&mut s, "digraph Runtime {{").unwrap();
        // Graph nodes for Oak Nodes and ABI handles.
        {
            writeln!(&mut s, "  {{").unwrap();
            writeln!(
                &mut s,
                "    node [shape=box style=filled fillcolor=red fontsize=24]"
            )
            .unwrap();
            let node_infos = self.node_infos.read().unwrap();
            for node_id in node_infos.keys().sorted() {
                let node_info = node_infos.get(node_id).unwrap();
                write!(
                    &mut s,
                    r###"    {} [label="{}" URL="{}"]"###,
                    node_id.dot_id(),
                    NodeInfo::construct_debug_id(&node_info.name, *node_id),
                    node_id.html_path(),
                )
                .unwrap();
                if node_info.node_stopper.is_none() {
                    write!(&mut s, " [style=dashed]").unwrap();
                }
                writeln!(&mut s).unwrap();
            }
            writeln!(&mut s, "  }}").unwrap();
        }
        {
            writeln!(&mut s, "  {{").unwrap();
            writeln!(
                &mut s,
                "    node [shape=hexagon style=filled fillcolor=orange]"
            )
            .unwrap();
            let node_infos = self.node_infos.read().unwrap();
            for node_id in node_infos.keys().sorted() {
                let node_info = node_infos.get(node_id).unwrap();
                for handle in node_info.abi_handles.keys() {
                    writeln!(
                        &mut s,
                        r###"    {} [label="{}:{}" URL="{}"]"###,
                        (*node_id, *handle).dot_id(),
                        node_id.0,
                        handle,
                        (*node_id, *handle).html_path(),
                    )
                    .unwrap();
                }
            }
            writeln!(&mut s, "  }}").unwrap();
        }
        {
            writeln!(&mut s, "  {{").unwrap();
            writeln!(
                &mut s,
                "    node [shape=ellipse style=filled fillcolor=green]"
            )
            .unwrap();
            let mut seen = HashSet::new();
            let node_infos = self.node_infos.read().unwrap();
            for node_id in node_infos.keys().sorted() {
                let node_info = node_infos.get(node_id).unwrap();
                for half in node_info.abi_handles.values() {
                    if seen.insert(half.dot_id()) {
                        writeln!(
                            &mut s,
                            r###"    {} [label="{}"]"###,
                            half.dot_id(),
                            half.get_channel_name(),
                        )
                        .unwrap();
                    }
                }
            }
            writeln!(&mut s, "  }}").unwrap();
        }

        // Edges for connections between Nodes and channels and messages.
        let mut msg_counter = 0;
        {
            let node_infos = self.node_infos.read().unwrap();
            for node_id in node_infos.keys().sorted() {
                let node_info = node_infos.get(node_id).unwrap();
                for (handle, half) in &node_info.abi_handles {
                    match half.direction {
                        ChannelHalfDirection::Write => {
                            writeln!(
                                &mut s,
                                "  {} -> {} -> {}",
                                node_id.dot_id(),
                                (*node_id, *handle).dot_id(),
                                half.dot_id()
                            )
                            .unwrap();
                        }
                        ChannelHalfDirection::Read => {
                            writeln!(
                                &mut s,
                                "  {} -> {} -> {}",
                                half.dot_id(),
                                (*node_id, *handle).dot_id(),
                                node_id.dot_id()
                            )
                            .unwrap();
                        }
                    }
                    // Include messages in the channel.
                    let messages = half.get_messages();
                    if messages.len() > 0 {
                        writeln!(&mut s, "  {{").unwrap();
                        writeln!(
                            &mut s,
                            r###"    node [shape=rect fontsize=10 label="msg"]"###
                        )
                        .unwrap();
                        // Messages have no identifier, so just use a count (and don't make it
                        // visible to the user).
                        let mut prev_graph_node = half.dot_id();
                        for msg in messages.iter() {
                            msg_counter += 1;
                            let graph_node = format!("msg{}", msg_counter);
                            writeln!(
                                &mut s,
                                "    {} -> {} [style=dashed arrowhead=none]",
                                graph_node, prev_graph_node
                            )
                            .unwrap();
                            for half in &msg.channels {
                                match half.direction {
                                    ChannelHalfDirection::Write => {
                                        writeln!(&mut s, "    {} -> {}", graph_node, half.dot_id())
                                            .unwrap();
                                    }
                                    ChannelHalfDirection::Read => {
                                        writeln!(&mut s, "    {} -> {}", half.dot_id(), graph_node)
                                            .unwrap();
                                    }
                                }
                            }
                            prev_graph_node = graph_node;
                        }
                        writeln!(&mut s, "  }}").unwrap();
                    }
                }
            }
        }

        writeln!(&mut s, "}}").unwrap();
        s
    }

    /// Generate an HTML page that describes the internal state of the [`Runtime`].
    pub fn html(&self) -> String {
        let mut s = String::new();
        writeln!(&mut s, "<h2>Nodes</h2>").unwrap();
        writeln!(&mut s, r###"<p><a href="/graph">Show as graph</a><ul>"###).unwrap();
        {
            let node_infos = self.node_infos.read().unwrap();
            for node_id in node_infos.keys().sorted() {
                let node_info = node_infos.get(node_id).unwrap();
                write!(
                    &mut s,
                    r###"<li><a href="{}">{:?}</a> => <tt>{:?}</tt>"###,
                    node_id.html_path(),
                    node_id,
                    node_info
                )
                .unwrap();
            }
        }
        writeln!(&mut s, "</ul>").unwrap();
        s
    }

    /// Generate an HTML page that includes the current counts of Nodes and channels.
    /// May be slow to generate, as it involves exploring reachable channels recursively.
    pub(crate) fn html_counts(&self) -> String {
        let (node_count, channel_count) = self.object_counts();
        format!(
            "<p>Object Counts: Nodes={} Channels={}",
            node_count, channel_count,
        )
    }

    /// Return counts of the number of Nodes and channels currently in existence.
    /// May be slow to generate, as it involves exploring reachable channels recursively.
    pub fn object_counts(&self) -> (u32, u32) {
        let mut node_count = 0;
        let mut channel_ids = HashSet::<String>::new();
        let mut visitor = |half: &ChannelHalf| {
            let channel_id = half.dot_id();
            if channel_ids.contains(&channel_id) {
                false
            } else {
                channel_ids.insert(channel_id);
                // Not seen this ChannelId before, so need to visit its children.
                true
            }
        };
        {
            let node_infos = self.node_infos.read().unwrap();
            for node_id in node_infos.keys().sorted() {
                node_count += 1;
                let node_info = node_infos.get(node_id).unwrap();
                for half in node_info.abi_handles.values() {
                    half.visit_halves(&mut visitor);
                }
            }
        }
        info!(
            "Counted {} nodes and {} channels",
            node_count,
            channel_ids.len()
        );
        (node_count as u32, channel_ids.len() as u32)
    }

    /// Generate an HTML page that describes the internal state of a specific Node.
    pub(crate) fn html_for_node(&self, id: u64) -> Option<String> {
        let node_id = NodeId(id);
        let node_infos = self.node_infos.read().unwrap();
        let node_info = node_infos.get(&node_id)?;
        let mut s = String::new();
        write!(
            &mut s,
            "<h2>{}</h2>",
            NodeInfo::construct_debug_id(&node_info.name, node_id),
        )
        .unwrap();
        if let Some(node_stopper) = &node_info.node_stopper {
            write!(
                &mut s,
                "<p>Node thread is currently running, join_handle={:?}",
                node_stopper.join_handle
            )
            .unwrap();
        } else {
            write!(&mut s, "<p>No current thread for Node.").unwrap();
        }
        write!(&mut s, "<p>Label={:?}<p>Handles:<ul>", node_info.label).unwrap();
        for (handle, half) in &node_info.abi_handles {
            write!(
                &mut s,
                r###"<li>Handle <a href="{}">{}</a> => {:?}"###,
                (node_id, *handle).html_path(),
                handle,
                half
            )
            .unwrap();
        }
        Some(s)
    }

    /// Generate an HTML page that describes the channel accessible via an ABI handle for the
    /// specified Node.
    pub(crate) fn html_for_handle(&self, node_id: u64, handle: oak_abi::Handle) -> Option<String> {
        let node_id = NodeId(node_id);
        let node_infos = self.node_infos.read().unwrap();
        let node_info = node_infos.get(&node_id)?;
        let half = node_info.abi_handles.get(&handle)?;
        let mut s = String::new();
        write!(
            &mut s,
            r###"<h2><a href="{}">Node {}</a> Handle {}</h2>"###,
            node_id.html_path(),
            NodeInfo::construct_debug_id(&node_info.name, node_id),
            handle,
        )
        .unwrap();
        write!(&mut s, r###"<p>Maps to {:?}"###, half).unwrap();
        Some(s)
    }
}
