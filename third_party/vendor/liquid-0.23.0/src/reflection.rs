use liquid_core::parser;

pub use parser::BlockReflection;
pub use parser::FilterReflection;
pub use parser::TagReflection;

pub trait ParserReflection {
    fn blocks<'r>(&'r self) -> Box<dyn Iterator<Item = &dyn parser::BlockReflection> + 'r>;

    fn tags<'r>(&'r self) -> Box<dyn Iterator<Item = &dyn parser::TagReflection> + 'r>;

    fn filters<'r>(&'r self) -> Box<dyn Iterator<Item = &dyn parser::FilterReflection> + 'r>;

    fn partials<'r>(&'r self) -> Box<dyn Iterator<Item = &str> + 'r>;
}
