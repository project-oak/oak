use std::fs::File;
use std::io::prelude::Read;
use std::path;
use std::sync;

use liquid_core::error::{Result, ResultLiquidExt, ResultLiquidReplaceExt};
use liquid_core::parser;
use liquid_core::runtime;

use super::Template;
use crate::reflection;
use liquid_core::partials;
#[cfg(feature = "stdlib")]
use liquid_lib::stdlib;

type Partials = partials::EagerCompiler<partials::InMemorySource>;

pub struct ParserBuilder<P = Partials>
where
    P: partials::PartialCompiler,
{
    blocks: parser::PluginRegistry<Box<dyn parser::ParseBlock>>,
    tags: parser::PluginRegistry<Box<dyn parser::ParseTag>>,
    filters: parser::PluginRegistry<Box<dyn parser::ParseFilter>>,
    partials: Option<P>,
}

impl ParserBuilder<Partials> {
    /// Create an empty Liquid parser
    pub fn new() -> Self {
        Self::default()
    }

    #[cfg(feature = "stdlib")]
    pub fn with_stdlib() -> Self {
        Self::new().stdlib()
    }
}

impl<P> ParserBuilder<P>
where
    P: partials::PartialCompiler,
{
    #[cfg(feature = "stdlib")]
    /// Create a Liquid parser with built-in Liquid features
    pub fn stdlib(self) -> Self {
        self.tag(stdlib::AssignTag)
            .tag(stdlib::BreakTag)
            .tag(stdlib::ContinueTag)
            .tag(stdlib::CycleTag)
            .tag(stdlib::IncludeTag)
            .tag(stdlib::IncrementTag)
            .tag(stdlib::DecrementTag)
            .block(stdlib::RawBlock)
            .block(stdlib::IfBlock)
            .block(stdlib::UnlessBlock)
            .block(stdlib::IfChangedBlock)
            .block(stdlib::ForBlock)
            .block(stdlib::TableRowBlock)
            .block(stdlib::CommentBlock)
            .block(stdlib::CaptureBlock)
            .block(stdlib::CaseBlock)
            .filter(stdlib::Abs)
            .filter(stdlib::Append)
            .filter(stdlib::AtLeast)
            .filter(stdlib::AtMost)
            .filter(stdlib::Capitalize)
            .filter(stdlib::Ceil)
            .filter(stdlib::Compact)
            .filter(stdlib::Concat)
            .filter(stdlib::Date)
            .filter(stdlib::Default)
            .filter(stdlib::DividedBy)
            .filter(stdlib::Downcase)
            .filter(stdlib::Escape)
            .filter(stdlib::EscapeOnce)
            .filter(stdlib::First)
            .filter(stdlib::Floor)
            .filter(stdlib::Join)
            .filter(stdlib::Last)
            .filter(stdlib::Lstrip)
            .filter(stdlib::Map)
            .filter(stdlib::Minus)
            .filter(stdlib::Modulo)
            .filter(stdlib::NewlineToBr)
            .filter(stdlib::Plus)
            .filter(stdlib::Prepend)
            .filter(stdlib::Remove)
            .filter(stdlib::RemoveFirst)
            .filter(stdlib::Replace)
            .filter(stdlib::ReplaceFirst)
            .filter(stdlib::Reverse)
            .filter(stdlib::Round)
            .filter(stdlib::Rstrip)
            .filter(stdlib::Size)
            .filter(stdlib::Slice)
            .filter(stdlib::Sort)
            .filter(stdlib::SortNatural)
            .filter(stdlib::Split)
            .filter(stdlib::Strip)
            .filter(stdlib::StripHtml)
            .filter(stdlib::StripNewlines)
            .filter(stdlib::Times)
            .filter(stdlib::Truncate)
            .filter(stdlib::TruncateWords)
            .filter(stdlib::Uniq)
            .filter(stdlib::Upcase)
            .filter(stdlib::UrlDecode)
            .filter(stdlib::UrlEncode)
            .filter(stdlib::Where)
    }

    /// Inserts a new custom block into the parser
    pub fn block<B: Into<Box<dyn parser::ParseBlock>>>(mut self, block: B) -> Self {
        let block = block.into();
        self.blocks
            .register(block.reflection().start_tag().to_owned(), block);
        self
    }

    /// Inserts a new custom tag into the parser
    pub fn tag<T: Into<Box<dyn parser::ParseTag>>>(mut self, tag: T) -> Self {
        let tag = tag.into();
        self.tags.register(tag.reflection().tag().to_owned(), tag);
        self
    }

    /// Inserts a new custom filter into the parser
    pub fn filter<F: Into<Box<dyn parser::ParseFilter>>>(mut self, filter: F) -> Self {
        let filter = filter.into();
        self.filters
            .register(filter.reflection().name().to_owned(), filter);
        self
    }

    /// Set which partial-templates will be available.
    pub fn partials<N: partials::PartialCompiler>(self, partials: N) -> ParserBuilder<N> {
        let Self {
            blocks,
            tags,
            filters,
            partials: _partials,
        } = self;
        ParserBuilder {
            blocks,
            tags,
            filters,
            partials: Some(partials),
        }
    }

    /// Create a parser
    pub fn build(self) -> Result<Parser> {
        let Self {
            blocks,
            tags,
            filters,
            partials,
        } = self;

        let mut options = parser::Language::empty();
        options.blocks = blocks;
        options.tags = tags;
        options.filters = filters;
        let options = sync::Arc::new(options);
        let partials = partials
            .map(|p| p.compile(options.clone()))
            .map_or(Ok(None), |r| r.map(Some))?
            .map(|p| p.into());
        let p = Parser { options, partials };
        Ok(p)
    }
}

impl<P> Default for ParserBuilder<P>
where
    P: partials::PartialCompiler,
{
    fn default() -> Self {
        Self {
            blocks: Default::default(),
            tags: Default::default(),
            filters: Default::default(),
            partials: Default::default(),
        }
    }
}

impl<P> reflection::ParserReflection for ParserBuilder<P>
where
    P: partials::PartialCompiler,
{
    fn blocks<'r>(&'r self) -> Box<dyn Iterator<Item = &dyn parser::BlockReflection> + 'r> {
        Box::new(self.blocks.plugins().map(|p| p.reflection()))
    }

    fn tags<'r>(&'r self) -> Box<dyn Iterator<Item = &dyn parser::TagReflection> + 'r> {
        Box::new(self.tags.plugins().map(|p| p.reflection()))
    }

    fn filters<'r>(&'r self) -> Box<dyn Iterator<Item = &dyn parser::FilterReflection> + 'r> {
        Box::new(self.filters.plugins().map(|p| p.reflection()))
    }

    fn partials<'r>(&'r self) -> Box<dyn Iterator<Item = &str> + 'r> {
        Box::new(
            self.partials
                .as_ref()
                .into_iter()
                .flat_map(|s| s.source().names()),
        )
    }
}

#[derive(Default, Clone)]
pub struct Parser {
    options: sync::Arc<parser::Language>,
    partials: Option<sync::Arc<dyn runtime::PartialStore + Send + Sync>>,
}

impl Parser {
    pub fn new() -> Self {
        Default::default()
    }

    /// Parses a liquid template, returning a Template object.
    /// # Examples
    ///
    /// ## Minimal Template
    ///
    /// ```
    /// let template = liquid::ParserBuilder::with_stdlib()
    ///     .build().unwrap()
    ///     .parse("Liquid!").unwrap();
    ///
    /// let globals = liquid::Object::new();
    /// let output = template.render(&globals).unwrap();
    /// assert_eq!(output, "Liquid!".to_string());
    /// ```
    ///
    pub fn parse(&self, text: &str) -> Result<Template> {
        let template = parser::parse(text, &self.options).map(runtime::Template::new)?;
        Ok(Template {
            template,
            partials: self.partials.clone(),
        })
    }

    /// Parse a liquid template from a file, returning a `Result<Template, Error>`.
    /// # Examples
    ///
    /// ## Minimal Template
    ///
    /// `template.txt`:
    ///
    /// ```text
    /// "Liquid {{data}}"
    /// ```
    ///
    /// Your rust code:
    ///
    /// ```rust,no_run
    /// let template = liquid::ParserBuilder::with_stdlib()
    ///     .build().unwrap()
    ///     .parse_file("path/to/template.txt").unwrap();
    ///
    /// let globals = liquid::object!({
    ///     "data": 4f64,
    /// });
    /// let output = template.render(&globals).unwrap();
    /// assert_eq!(output, "Liquid! 4\n".to_string());
    /// ```
    ///
    pub fn parse_file<P: AsRef<path::Path>>(&self, file: P) -> Result<Template> {
        self.parse_file_path(file.as_ref())
    }

    fn parse_file_path(&self, file: &path::Path) -> Result<Template> {
        let mut f = File::open(file)
            .replace("Cannot open file")
            .context_key("path")
            .value_with(|| file.to_string_lossy().into_owned().into())?;
        let mut buf = String::new();
        f.read_to_string(&mut buf)
            .replace("Cannot read file")
            .context_key("path")
            .value_with(|| file.to_string_lossy().into_owned().into())?;

        self.parse(&buf)
    }
}

impl reflection::ParserReflection for Parser {
    fn blocks<'r>(&'r self) -> Box<dyn Iterator<Item = &dyn parser::BlockReflection> + 'r> {
        Box::new(self.options.blocks.plugins().map(|p| p.reflection()))
    }

    fn tags<'r>(&'r self) -> Box<dyn Iterator<Item = &dyn parser::TagReflection> + 'r> {
        Box::new(self.options.tags.plugins().map(|p| p.reflection()))
    }

    fn filters<'r>(&'r self) -> Box<dyn Iterator<Item = &dyn parser::FilterReflection> + 'r> {
        Box::new(self.options.filters.plugins().map(|p| p.reflection()))
    }

    fn partials<'r>(&'r self) -> Box<dyn Iterator<Item = &str> + 'r> {
        Box::new(self.partials.as_ref().into_iter().flat_map(|s| s.names()))
    }
}
