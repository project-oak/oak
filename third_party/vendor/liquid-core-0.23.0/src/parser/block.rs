use crate::error::Result;
use crate::runtime::Renderable;

use super::Language;
use super::TagBlock;
use super::TagTokenIter;

pub trait BlockReflection {
    fn start_tag(&self) -> &str;

    fn end_tag(&self) -> &str;

    fn description(&self) -> &str;

    fn example(&self) -> Option<&str> {
        None
    }

    fn spec(&self) -> Option<&str> {
        None
    }
}

/// A trait for creating custom custom block-size tags (`{% if something %}{% endif %}`).
/// This is a simple type alias for a function.
///
/// This function will be called whenever the parser encounters a block and returns
/// a new `Renderable` based on its parameters. The received parameters specify the name
/// of the block, the argument [Tokens](crate::TagTokenIter) passed to
/// the block, a [TagBlock](crate::TagBlock) inside the block and
/// the global [`Language`].
pub trait ParseBlock: Send + Sync + ParseBlockClone {
    fn parse(
        &self,
        arguments: TagTokenIter,
        block: TagBlock,
        options: &Language,
    ) -> Result<Box<dyn Renderable>>;

    fn reflection(&self) -> &dyn BlockReflection;
}

pub trait ParseBlockClone {
    fn clone_box(&self) -> Box<dyn ParseBlock>;
}

impl<T> ParseBlockClone for T
where
    T: 'static + ParseBlock + Clone,
{
    fn clone_box(&self) -> Box<dyn ParseBlock> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn ParseBlock> {
    fn clone(&self) -> Box<dyn ParseBlock> {
        self.clone_box()
    }
}

impl<T> From<T> for Box<dyn ParseBlock>
where
    T: 'static + ParseBlock,
{
    fn from(filter: T) -> Self {
        Box::new(filter)
    }
}
