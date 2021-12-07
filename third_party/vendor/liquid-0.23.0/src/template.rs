use std::io::Write;
use std::sync;

use liquid_core::error::Result;
use liquid_core::runtime;
use liquid_core::runtime::PartialStore;
use liquid_core::runtime::Renderable;

pub struct Template {
    pub(crate) template: runtime::Template,
    pub(crate) partials: Option<sync::Arc<dyn PartialStore + Send + Sync>>,
}

impl Template {
    /// Renders an instance of the Template, using the given globals.
    pub fn render(&self, globals: &dyn crate::ObjectView) -> Result<String> {
        const BEST_GUESS: usize = 10_000;
        let mut data = Vec::with_capacity(BEST_GUESS);
        self.render_to(&mut data, globals)?;

        Ok(convert_buffer(data))
    }

    /// Renders an instance of the Template, using the given globals.
    pub fn render_to(&self, writer: &mut dyn Write, globals: &dyn crate::ObjectView) -> Result<()> {
        let runtime = runtime::RuntimeBuilder::new().set_globals(globals);
        let runtime = match self.partials {
            Some(ref partials) => runtime.set_partials(partials.as_ref()),
            None => runtime,
        };
        let runtime = runtime.build();
        self.template.render_to(writer, &runtime)
    }
}

#[cfg(debug_assertions)]
fn convert_buffer(buffer: Vec<u8>) -> String {
    String::from_utf8(buffer)
        .expect("render can only write UTF-8 because all inputs and processing preserve utf-8")
}

#[cfg(not(debug_assertions))]
fn convert_buffer(buffer: Vec<u8>) -> String {
    unsafe { String::from_utf8_unchecked(buffer) }
}
