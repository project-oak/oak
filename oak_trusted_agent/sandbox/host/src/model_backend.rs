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

//! Model backends that serve the guest's `oak:agent/model` `call-model`
//! requests.
//!
//! The guest sends a Gemini `GenerateContent`-style JSON request (`contents`,
//! optional `systemInstruction` and `tools`, plus the configured `model` name)
//! and expects a `GenerateContent`-style JSON response (`candidates`).

use std::time::Duration;

use anyhow::Context;
use serde_json::{Value, json};

/// Executes model requests issued by the agent guest.
pub trait ModelBackend: Send + Sync {
    /// Runs a `GenerateContent`-style JSON request and returns a
    /// `GenerateContent`-style JSON response.
    fn generate_content(&self, request: &str) -> anyhow::Result<String>;
}

/// Model backend for the Ollama chat API (`POST {base_url}/api/chat`), as
/// served by the attested model server behind an Oak Proxy client.
pub struct OllamaModelBackend {
    chat_url: String,
    agent: ureq::Agent,
}

impl OllamaModelBackend {
    pub fn new(base_url: &str, timeout: Duration) -> Self {
        Self {
            chat_url: format!("{}/api/chat", base_url.trim_end_matches('/')),
            agent: ureq::AgentBuilder::new().timeout(timeout).build(),
        }
    }
}

impl ModelBackend for OllamaModelBackend {
    fn generate_content(&self, request: &str) -> anyhow::Result<String> {
        let request: Value = serde_json::from_str(request).context("invalid model request JSON")?;
        let chat_request = to_ollama_chat_request(&request)?;
        let response = self
            .agent
            .post(&self.chat_url)
            .set("Content-Type", "application/json")
            .send_string(&chat_request.to_string())
            .map_err(|e| match e {
                ureq::Error::Status(code, response) => anyhow::anyhow!(
                    "Ollama returned HTTP {code}: {}",
                    response.into_string().unwrap_or_default()
                ),
                other => anyhow::Error::new(other).context("failed to reach Ollama"),
            })?;
        let chat_response: Value = serde_json::from_str(&response.into_string()?)
            .context("invalid Ollama response JSON")?;
        Ok(from_ollama_chat_response(&chat_response)?.to_string())
    }
}

/// Converts a `GenerateContent`-style request into an Ollama chat request.
fn to_ollama_chat_request(request: &Value) -> anyhow::Result<Value> {
    let model = request["model"].as_str().context("model request is missing `model`")?;

    let mut messages = Vec::new();
    if let Some(system) = system_instruction_text(&request["systemInstruction"]) {
        messages.push(json!({"role": "system", "content": system}));
    }
    for content in request["contents"].as_array().into_iter().flatten() {
        let mut text = String::new();
        let mut tool_calls = Vec::new();
        for part in content["parts"].as_array().into_iter().flatten() {
            if let Some(part_text) = part["text"].as_str() {
                if part["thought"].as_bool() != Some(true) {
                    text.push_str(part_text);
                }
            } else if let Some(call) = part.get("functionCall") {
                let arguments = call.get("args").cloned().unwrap_or_else(|| json!({}));
                tool_calls
                    .push(json!({"function": {"name": call["name"], "arguments": arguments}}));
            } else if let Some(response) = part.get("functionResponse") {
                messages.push(json!({
                    "role": "tool",
                    "tool_name": response["name"],
                    "content": response["response"].to_string(),
                }));
            }
        }
        if !text.is_empty() || !tool_calls.is_empty() {
            let role = if content["role"] == "model" { "assistant" } else { "user" };
            let mut message = json!({"role": role, "content": text});
            if !tool_calls.is_empty() {
                message["tool_calls"] = json!(tool_calls);
            }
            messages.push(message);
        }
    }

    let tools: Vec<Value> = request["tools"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|tool| tool["functionDeclarations"].as_array())
        .flatten()
        .map(|declaration| {
            let parameters = declaration
                .get("parametersJsonSchema")
                .or_else(|| declaration.get("parameters"))
                .cloned()
                .unwrap_or_else(|| json!({"type": "object", "properties": {}}));
            json!({
                "type": "function",
                "function": {
                    "name": declaration["name"],
                    "description": declaration["description"],
                    "parameters": parameters,
                },
            })
        })
        .collect();

    let mut chat_request = json!({"model": model, "messages": messages, "stream": false});
    if !tools.is_empty() {
        chat_request["tools"] = json!(tools);
    }
    Ok(chat_request)
}

/// Extracts the system instruction, which may be a plain string or a
/// `Content` object with text parts.
fn system_instruction_text(instruction: &Value) -> Option<String> {
    match instruction {
        Value::String(text) => Some(text.clone()),
        Value::Object(_) => {
            let text = instruction["parts"]
                .as_array()?
                .iter()
                .filter_map(|part| part["text"].as_str())
                .collect::<Vec<_>>()
                .join("\n");
            (!text.is_empty()).then_some(text)
        }
        _ => None,
    }
}

/// Converts an Ollama chat response into a `GenerateContent`-style response.
fn from_ollama_chat_response(response: &Value) -> anyhow::Result<Value> {
    let message = response.get("message").context("Ollama response is missing `message`")?;

    let mut parts = Vec::new();
    if let Some(text) = message["content"].as_str().filter(|text| !text.is_empty()) {
        parts.push(json!({"text": text}));
    }
    for call in message["tool_calls"].as_array().into_iter().flatten() {
        parts.push(json!({
            "functionCall": {"name": call["function"]["name"], "args": call["function"]["arguments"]},
        }));
    }

    let finish_reason = match response["done_reason"].as_str() {
        Some("length") => "MAX_TOKENS",
        _ => "STOP",
    };
    Ok(json!({
        "candidates": [{"content": {"role": "model", "parts": parts}, "finishReason": finish_reason}],
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_ollama_chat_request() {
        let request = json!({
            "model": "gemma4:e2b-it-qat",
            "provider": 0,
            "systemInstruction": "Be helpful.",
            "contents": [
                {"role": "user", "parts": [{"text": "Look up key 7"}]},
                {"role": "model", "parts": [
                    {"text": "thinking", "thought": true},
                    {"functionCall": {"name": "lookup", "args": {"key": "7"}}},
                ]},
                {"role": "user", "parts": [
                    {"functionResponse": {"name": "lookup", "response": {"value": "seven"}}},
                ]},
            ],
            "tools": [{"functionDeclarations": [{
                "name": "lookup",
                "description": "Looks up a key",
                "parametersJsonSchema": {"type": "object"},
            }]}],
        });

        assert_eq!(
            to_ollama_chat_request(&request).unwrap(),
            json!({
                "model": "gemma4:e2b-it-qat",
                "stream": false,
                "messages": [
                    {"role": "system", "content": "Be helpful."},
                    {"role": "user", "content": "Look up key 7"},
                    {"role": "assistant", "content": "", "tool_calls": [
                        {"function": {"name": "lookup", "arguments": {"key": "7"}}},
                    ]},
                    {"role": "tool", "tool_name": "lookup", "content": "{\"value\":\"seven\"}"},
                ],
                "tools": [{"type": "function", "function": {
                    "name": "lookup",
                    "description": "Looks up a key",
                    "parameters": {"type": "object"},
                }}],
            })
        );
    }

    #[test]
    fn test_system_instruction_content_object() {
        let instruction = json!({"parts": [{"text": "a"}, {"text": "b"}]});
        assert_eq!(system_instruction_text(&instruction).as_deref(), Some("a\nb"));
    }

    #[test]
    fn test_from_ollama_chat_response() {
        let response = json!({
            "message": {
                "role": "assistant",
                "content": "Calling a tool.",
                "tool_calls": [{"function": {"name": "lookup", "arguments": {"key": "7"}}}],
            },
            "done_reason": "stop",
        });

        assert_eq!(
            from_ollama_chat_response(&response).unwrap(),
            json!({"candidates": [{
                "content": {"role": "model", "parts": [
                    {"text": "Calling a tool."},
                    {"functionCall": {"name": "lookup", "args": {"key": "7"}}},
                ]},
                "finishReason": "STOP",
            }]})
        );
    }
}
