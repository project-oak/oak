#[cfg(feature = "extra")]
pub mod extra;
#[cfg(feature = "jekyll")]
pub mod jekyll;
#[cfg(feature = "shopify")]
pub mod shopify;
#[cfg(feature = "stdlib")]
pub mod stdlib;

use liquid_core::Error;

pub(crate) fn invalid_input<S>(cause: S) -> Error
where
    S: Into<kstring::KString>,
{
    Error::with_msg("Invalid input").context("cause", cause)
}

pub(crate) fn invalid_argument<S>(argument: S, cause: S) -> Error
where
    S: Into<kstring::KString>,
{
    Error::with_msg("Invalid argument")
        .context("argument", argument)
        .context("cause", cause)
}
