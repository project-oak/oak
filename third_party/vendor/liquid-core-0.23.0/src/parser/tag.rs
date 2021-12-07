use crate::error::Result;
use crate::runtime::Renderable;

use super::Language;
use super::TagTokenIter;

pub trait TagReflection {
    fn tag(&self) -> &str;

    fn description(&self) -> &str;

    fn example(&self) -> Option<&str> {
        None
    }

    fn spec(&self) -> Option<&str> {
        None
    }
}

/// A trait for creating custom tags. This is a simple type alias for a function.
///
/// This function will be called whenever the parser encounters a tag and returns
/// a new [Renderable] based on its parameters. The received parameters
/// specify the name of the tag, the argument [Tokens](crate::TagTokenIter) passed to
/// the tag and the global [`Language`].
pub trait ParseTag: Send + Sync + ParseTagClone {
    fn parse(&self, arguments: TagTokenIter, options: &Language) -> Result<Box<dyn Renderable>>;

    fn reflection(&self) -> &dyn TagReflection;
}

pub trait ParseTagClone {
    fn clone_box(&self) -> Box<dyn ParseTag>;
}

impl<T> ParseTagClone for T
where
    T: 'static + ParseTag + Clone,
{
    fn clone_box(&self) -> Box<dyn ParseTag> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn ParseTag> {
    fn clone(&self) -> Box<dyn ParseTag> {
        self.clone_box()
    }
}

impl<T> From<T> for Box<dyn ParseTag>
where
    T: 'static + ParseTag,
{
    fn from(filter: T) -> Self {
        Box::new(filter)
    }
}
