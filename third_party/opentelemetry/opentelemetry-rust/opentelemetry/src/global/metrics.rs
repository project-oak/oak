extern crate alloc;

use crate::metrics::{self, Meter, MeterProvider};
use crate::KeyValue;
use alloc::{borrow::Cow, sync::Arc, vec::Vec};
use core::fmt;
use oak_core::sync::OnceCell;

/// The global `MeterProvider` singleton.
static GLOBAL_METER_PROVIDER: OnceCell<GlobalMeterProvider> = OnceCell::new();

/// Allows a specific [MeterProvider] to be used generically by the
/// [GlobalMeterProvider] by mirroring the interface and boxing the return types.
pub trait ObjectSafeMeterProvider {
    /// Creates a versioned named meter instance that is a trait object through the underlying
    /// [MeterProvider].
    fn versioned_meter_cow(
        &self,
        name: Cow<'static, str>,
        version: Option<Cow<'static, str>>,
        schema_url: Option<Cow<'static, str>>,
        attributes: Option<Vec<KeyValue>>,
    ) -> Meter;
}

impl<P> ObjectSafeMeterProvider for P
where
    P: MeterProvider,
{
    /// Return a versioned boxed tracer
    fn versioned_meter_cow(
        &self,
        name: Cow<'static, str>,
        version: Option<Cow<'static, str>>,
        schema_url: Option<Cow<'static, str>>,
        attributes: Option<Vec<KeyValue>>,
    ) -> Meter {
        self.versioned_meter(name, version, schema_url, attributes)
    }
}

/// Represents the globally configured [`MeterProvider`] instance for this
/// application.
#[derive(Clone)]
pub struct GlobalMeterProvider {
    provider: Arc<dyn ObjectSafeMeterProvider + Send + Sync>,
}

impl fmt::Debug for GlobalMeterProvider {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GlobalMeterProvider").finish()
    }
}

impl MeterProvider for GlobalMeterProvider {
    fn versioned_meter(
        &self,
        name: impl Into<Cow<'static, str>>,
        version: Option<impl Into<Cow<'static, str>>>,
        schema_url: Option<impl Into<Cow<'static, str>>>,
        attributes: Option<Vec<KeyValue>>,
    ) -> Meter {
        self.provider.versioned_meter_cow(
            name.into(),
            version.map(Into::into),
            schema_url.map(Into::into),
            attributes,
        )
    }
}

impl GlobalMeterProvider {
    /// Create a new global meter provider
    pub fn new<P>(provider: P) -> Self
    where
        P: MeterProvider + Send + Sync + 'static,
    {
        GlobalMeterProvider {
            provider: Arc::new(provider),
        }
    }
}

/// Sets the given [`MeterProvider`] instance as the current global meter
/// provider.
pub fn set_meter_provider<P>(new_provider: P)
where
    P: metrics::MeterProvider + Send + Sync + 'static,
{
    GLOBAL_METER_PROVIDER
        .set(GlobalMeterProvider::new(new_provider))
        .expect("Couldn't set GLOBAL_METER_PROVIDER");
}

/// Returns an instance of the currently configured global [`MeterProvider`]
/// through [`GlobalMeterProvider`].
pub fn meter_provider() -> GlobalMeterProvider {
    if GLOBAL_METER_PROVIDER.get().is_none() {
        let _ = GLOBAL_METER_PROVIDER.set(GlobalMeterProvider::new(
            metrics::noop::NoopMeterProvider::new(),
        ));
    }

    GLOBAL_METER_PROVIDER
        .get()
        .expect("GLOBAL_METER_PROVIDER not initialized")
        .clone()
}

/// Creates a named [`Meter`] via the configured [`GlobalMeterProvider`].
///
/// If the name is an empty string, the provider will use a default name.
///
/// This is a more convenient way of expressing `global::meter_provider().meter(name)`.
pub fn meter(name: impl Into<Cow<'static, str>>) -> Meter {
    meter_provider().meter(name.into())
}

/// Creates a [`Meter`] with the name, version and schema url.
///
/// - name SHOULD uniquely identify the instrumentation scope, such as the instrumentation library (e.g. io.opentelemetry.contrib.mongodb), package, module or class name.
/// - version specifies the version of the instrumentation scope if the scope has a version
/// - schema url specifies the Schema URL that should be recorded in the emitted telemetry.
///
/// This is a convenient way of `global::meter_provider().versioned_meter(...)`
///
/// # Example
///
/// ```
/// use opentelemetry_rk::global::meter_with_version;
/// use opentelemetry_rk::KeyValue;
///
/// let meter = meter_with_version(
///     "io.opentelemetry",
///     Some("0.17"),
///     Some("https://opentelemetry.io/schemas/1.2.0"),
///     Some(vec![KeyValue::new("key", "value")]),
/// );
/// ```
pub fn meter_with_version(
    name: impl Into<Cow<'static, str>>,
    version: Option<impl Into<Cow<'static, str>>>,
    schema_url: Option<impl Into<Cow<'static, str>>>,
    attributes: Option<Vec<KeyValue>>,
) -> Meter {
    meter_provider().versioned_meter(
        name.into(),
        version.map(Into::into),
        schema_url.map(Into::into),
        attributes,
    )
}
