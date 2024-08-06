//! Environment variables resource detector
//!
//! Implementation of `ResourceDetector` to extract a `Resource` from environment
//! variables.
use crate::resource::{Resource, ResourceDetector};
use alloc::{borrow::ToOwned, string::String};
use opentelemetry_rk::KeyValue;

const _OTEL_RESOURCE_ATTRIBUTES: &str = "OTEL_RESOURCE_ATTRIBUTES";
const _OTEL_SERVICE_NAME: &str = "OTEL_SERVICE_NAME";

/// EnvResourceDetector extract resource from environment variable
/// `OTEL_RESOURCE_ATTRIBUTES`. See [OpenTelemetry Resource
/// Spec](https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/resource/sdk.md#specifying-resource-information-via-an-environment-variable)
/// for details.
#[derive(Debug)]
pub struct EnvResourceDetector {
    _private: (),
}

impl ResourceDetector for EnvResourceDetector {
    fn detect(&self) -> Resource {
        // match env::var(OTEL_RESOURCE_ATTRIBUTES) {
        //     Ok(s) if !s.is_empty() => construct_otel_resources(s),
        //     Ok(_) | Err(_) => Resource::new(vec![]), // return empty resource
        // }
        Resource::new(vec![])
    }
}

impl EnvResourceDetector {
    /// Create `EnvResourceDetector` instance.
    pub fn new() -> Self {
        EnvResourceDetector { _private: () }
    }
}

impl Default for EnvResourceDetector {
    fn default() -> Self {
        EnvResourceDetector::new()
    }
}

/// Extract key value pairs and construct a resource from resources string like
/// key1=value1,key2=value2,...
fn _construct_otel_resources(s: String) -> Resource {
    Resource::new(s.split_terminator(',').filter_map(|entry| {
        let mut parts = entry.splitn(2, '=');
        let key = parts.next()?.trim();
        let value = parts.next()?.trim();
        if value.find('=').is_some() {
            return None;
        }

        Some(KeyValue::new(key.to_owned(), value.to_owned()))
    }))
}

/// There are attributes which MUST be provided by the SDK as specified in
/// [the Resource SDK specification]. This detector detects those attributes and
/// if the attribute cannot be detected, it uses the default value.
///
/// This detector will first try `OTEL_SERVICE_NAME` env. If it's not available,
/// then it will check the `OTEL_RESOURCE_ATTRIBUTES` env and see if it contains
/// `service.name` resource. If it's also not available, it will use `unknown_service`.
///
/// If users want to set an empty service name, they can provide
/// a resource with empty value and `service.name` key.
///
/// [the Resource SDK specification]:https://github.com/open-telemetry/opentelemetry-specification/blob/main/specification/resource/sdk.md#sdk-provided-resource-attributes
#[derive(Debug)]
pub struct SdkProvidedResourceDetector;

impl ResourceDetector for SdkProvidedResourceDetector {
    fn detect(&self) -> Resource {
        Resource::new(vec![])
    }
}
