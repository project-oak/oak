use alloc::{boxed::Box, string::String};
use core::fmt;
use oak_core::sync::OnceCell;

#[cfg(feature = "logs")]
use crate::logs::LogError;
#[cfg(feature = "metrics")]
use crate::metrics::MetricsError;
#[cfg(feature = "trace")]
use crate::trace::TraceError;

static GLOBAL_ERROR_HANDLER: OnceCell<Option<ErrorHandler>> = OnceCell::new();

/// Wrapper for error from both tracing and metrics part of open telemetry.
#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    #[cfg(feature = "trace")]
    #[cfg_attr(docsrs, doc(cfg(feature = "trace")))]

    /// Failed to export traces.
    Trace(#[from] TraceError),
    #[cfg(feature = "metrics")]
    #[cfg_attr(docsrs, doc(cfg(feature = "metrics")))]

    /// An issue raised by the metrics module.
    Metric(MetricsError),

    #[cfg(feature = "logs")]
    #[cfg_attr(docsrs, doc(cfg(feature = "logs")))]
    /// Failed to export logs.
    Log(LogError),

    /// Other types of failures not covered by the variants above.
    Other(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            #[cfg(feature = "trace")]
            Error::Trace(err) => write!(f, "OpenTelemetry trace error occurred: {}", err),
            #[cfg(feature = "metrics")]
            Error::Metric(err) => write!(f, "OpenTelemetry metrics error occurred: {}", err),
            #[cfg(feature = "logs")]
            Error::Log(err) => write!(f, "OpenTelemetry log error occurred: {}", err),
            Error::Other(msg) => write!(f, "OpenTelemetry error occurred: {}", msg),
        }
    }
}

#[cfg(feature = "metrics")]
impl From<MetricsError> for Error {
    fn from(err: MetricsError) -> Self {
        Error::Metric(err)
    }
}

struct ErrorHandler(Box<dyn Fn(Error) + Send + Sync>);

/// Handle error using the globally configured error handler.
///
/// Writes to stderr if unset.
pub fn handle_error<T: Into<Error>>(err: T) {
    if let Some(handler) = GLOBAL_ERROR_HANDLER.get() {
        (handler.as_ref().unwrap().0)(err.into());
    } else {
        match err.into() {
            #[cfg(feature = "metrics")]
            #[cfg_attr(docsrs, doc(cfg(feature = "metrics")))]
            Error::Metric(err) => log::error!("OpenTelemetry error occurred. {}", err),
            #[cfg(feature = "trace")]
            #[cfg_attr(docsrs, doc(cfg(feature = "trace")))]
            Error::Trace(err) => log::error!("OpenTelemetry trace error occurred. {}", err),
            #[cfg(feature = "logs")]
            #[cfg_attr(docsrs, doc(cfg(feature = "logs")))]
            Error::Log(err) => log::error!("OpenTelemetry log error occurred. {}", err),

            Error::Other(err_msg) => {
                log::error!("OpenTelemetry error occurred. {}", err_msg);
            }
        }
    }
}

/// Set global error handler.
pub fn set_error_handler<F>(f: F) -> Result<(), Error>
where
    F: Fn(Error) + Send + Sync + 'static,
{
    GLOBAL_ERROR_HANDLER
        .set(Some(ErrorHandler(Box::new(f))))
        .map_err(|_| Error::Other(String::from("Couldn't set GLOBAL_ERROR_HANDLER")))
}
