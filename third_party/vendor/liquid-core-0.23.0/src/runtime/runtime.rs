use std::sync;

use crate::error::Error;
use crate::error::Result;
use crate::model::{Object, ObjectView, Scalar, ScalarCow, Value, ValueCow, ValueView};

use super::PartialStore;
use super::Renderable;

/// State for rendering a template
pub trait Runtime {
    /// Partial templates for inclusion.
    fn partials(&self) -> &dyn PartialStore;

    /// The name of the currently active template.
    fn name(&self) -> Option<kstring::KStringRef<'_>>;

    /// All available values
    fn roots(&self) -> std::collections::BTreeSet<kstring::KStringCow<'_>>;
    /// Recursively index into the stack.
    fn try_get(&self, path: &[ScalarCow<'_>]) -> Option<ValueCow<'_>>;
    /// Recursively index into the stack.
    fn get(&self, path: &[ScalarCow<'_>]) -> Result<ValueCow<'_>>;

    /// Sets a value in the global runtime.
    fn set_global(
        &self,
        name: kstring::KString,
        val: crate::model::Value,
    ) -> Option<crate::model::Value>;

    /// Used by increment and decrement tags
    fn set_index(&self, name: kstring::KString, val: Value) -> Option<Value>;
    /// Used by increment and decrement tags
    fn get_index<'a>(&'a self, name: &str) -> Option<ValueCow<'a>>;

    /// Unnamed state for plugins during rendering
    fn registers(&self) -> &Registers;
}

impl<'r, R: Runtime + ?Sized> Runtime for &'r R {
    fn partials(&self) -> &dyn super::PartialStore {
        <R as Runtime>::partials(self)
    }

    fn name(&self) -> Option<kstring::KStringRef<'_>> {
        <R as Runtime>::name(self)
    }

    fn roots(&self) -> std::collections::BTreeSet<kstring::KStringCow<'_>> {
        <R as Runtime>::roots(self)
    }

    fn try_get(&self, path: &[ScalarCow<'_>]) -> Option<ValueCow<'_>> {
        <R as Runtime>::try_get(self, path)
    }

    fn get(&self, path: &[ScalarCow<'_>]) -> Result<ValueCow<'_>> {
        <R as Runtime>::get(self, path)
    }

    fn set_global(
        &self,
        name: kstring::KString,
        val: crate::model::Value,
    ) -> Option<crate::model::Value> {
        <R as Runtime>::set_global(self, name, val)
    }

    fn set_index(&self, name: kstring::KString, val: Value) -> Option<Value> {
        <R as Runtime>::set_index(self, name, val)
    }

    fn get_index<'a>(&'a self, name: &str) -> Option<ValueCow<'a>> {
        <R as Runtime>::get_index(self, name)
    }

    fn registers(&self) -> &super::Registers {
        <R as Runtime>::registers(self)
    }
}

/// Create processing runtime for a template.
pub struct RuntimeBuilder<'g, 'p> {
    globals: Option<&'g dyn ObjectView>,
    partials: Option<&'p dyn PartialStore>,
}

impl<'c, 'g: 'c, 'p: 'c> RuntimeBuilder<'g, 'p> {
    /// Creates a new, empty rendering runtime.
    pub fn new() -> Self {
        Self {
            globals: None,
            partials: None,
        }
    }

    /// Initialize the stack with the given globals.
    pub fn set_globals<'n>(self, values: &'n dyn ObjectView) -> RuntimeBuilder<'n, 'p> {
        RuntimeBuilder {
            globals: Some(values),
            partials: self.partials,
        }
    }

    /// Initialize partial-templates available for including.
    pub fn set_partials<'n>(self, values: &'n dyn PartialStore) -> RuntimeBuilder<'g, 'n> {
        RuntimeBuilder {
            globals: self.globals,
            partials: Some(values),
        }
    }

    /// Create the `Runtime`.
    pub fn build(self) -> impl Runtime + 'c {
        let partials = self.partials.unwrap_or(&NullPartials);
        let runtime = RuntimeCore {
            partials,
            ..Default::default()
        };
        let runtime = super::IndexFrame::new(runtime);
        let runtime = super::StackFrame::new(runtime, self.globals.unwrap_or(&NullObject));
        super::GlobalFrame::new(runtime)
    }
}

#[derive(Copy, Clone, Debug)]
struct NullObject;

impl ValueView for NullObject {
    fn as_debug(&self) -> &dyn std::fmt::Debug {
        self
    }

    fn render(&self) -> crate::model::DisplayCow<'_> {
        Value::Nil.render()
    }
    fn source(&self) -> crate::model::DisplayCow<'_> {
        Value::Nil.source()
    }
    fn type_name(&self) -> &'static str {
        "object"
    }
    fn query_state(&self, state: crate::model::State) -> bool {
        match state {
            crate::model::State::Truthy => true,
            crate::model::State::DefaultValue
            | crate::model::State::Empty
            | crate::model::State::Blank => false,
        }
    }

    fn to_kstr(&self) -> kstring::KStringCow<'_> {
        kstring::KStringCow::from_static("")
    }
    fn to_value(&self) -> Value {
        Value::Object(Object::new())
    }

    fn as_object(&self) -> Option<&dyn ObjectView> {
        Some(self)
    }
}

impl ObjectView for NullObject {
    fn as_value(&self) -> &dyn ValueView {
        self
    }

    fn size(&self) -> i64 {
        0
    }

    fn keys<'k>(&'k self) -> Box<dyn Iterator<Item = kstring::KStringCow<'k>> + 'k> {
        let keys = Vec::new().into_iter();
        Box::new(keys)
    }

    fn values<'k>(&'k self) -> Box<dyn Iterator<Item = &'k dyn ValueView> + 'k> {
        let i = Vec::new().into_iter();
        Box::new(i)
    }

    fn iter<'k>(
        &'k self,
    ) -> Box<dyn Iterator<Item = (kstring::KStringCow<'k>, &'k dyn ValueView)> + 'k> {
        let i = Vec::new().into_iter();
        Box::new(i)
    }

    fn contains_key(&self, _index: &str) -> bool {
        false
    }

    fn get<'s>(&'s self, _index: &str) -> Option<&'s dyn ValueView> {
        None
    }
}

impl Default for RuntimeBuilder<'static, 'static> {
    fn default() -> Self {
        Self::new()
    }
}

/// Processing runtime for a template.
pub struct RuntimeCore<'g> {
    partials: &'g dyn PartialStore,

    registers: Registers,
}

impl<'g> RuntimeCore<'g> {
    /// Create a default `RuntimeCore`.
    ///
    /// See `RuntimeBuilder` for more control.
    pub fn new() -> Self {
        RuntimeCore::default()
    }

    /// Partial templates for inclusion.
    pub fn partials(&self) -> &dyn PartialStore {
        self.partials
    }
}

impl<'g> Runtime for RuntimeCore<'g> {
    fn partials(&self) -> &dyn PartialStore {
        self.partials
    }

    fn name(&self) -> Option<kstring::KStringRef<'_>> {
        None
    }

    fn roots(&self) -> std::collections::BTreeSet<kstring::KStringCow<'_>> {
        // Indexes don't count
        std::collections::BTreeSet::new()
    }

    fn try_get(&self, _path: &[ScalarCow<'_>]) -> Option<ValueCow<'_>> {
        None
    }

    fn get(&self, path: &[ScalarCow<'_>]) -> Result<ValueCow<'_>> {
        let key = path.first().cloned().unwrap_or_else(|| Scalar::new("nil"));
        Error::with_msg("Unknown variable")
            .context("requested variable", key.to_kstr())
            .into_err()
    }

    fn set_global(
        &self,
        _name: kstring::KString,
        _val: crate::model::Value,
    ) -> Option<crate::model::Value> {
        unreachable!("Must be masked by a global frame");
    }

    fn set_index(&self, _name: kstring::KString, _val: Value) -> Option<Value> {
        unreachable!("Must be masked by a global frame");
    }

    fn get_index<'a>(&'a self, _name: &str) -> Option<ValueCow<'a>> {
        None
    }

    fn registers(&self) -> &Registers {
        &self.registers
    }
}

impl<'g> Default for RuntimeCore<'g> {
    fn default() -> Self {
        Self {
            partials: &NullPartials,
            registers: Default::default(),
        }
    }
}

/// Unnamed state for plugins during rendering
pub struct Registers {
    registers: std::cell::RefCell<anymap2::AnyMap>,
}

impl Registers {
    /// Data store for stateful tags/blocks.
    ///
    /// If a plugin needs state, it creates a `struct Register : Default` and accesses it via
    /// `get_mut`.
    pub fn get_mut<T: std::any::Any + Default>(&self) -> std::cell::RefMut<'_, T> {
        std::cell::RefMut::map(self.registers.borrow_mut(), |registers| {
            registers.entry::<T>().or_insert_with(Default::default)
        })
    }
}

impl Default for Registers {
    fn default() -> Self {
        Self {
            registers: std::cell::RefCell::new(anymap2::AnyMap::new()),
        }
    }
}

/// The current interrupt state. The interrupt state is used by
/// the `break` and `continue` tags to halt template rendering
/// at a given point and unwind the `render` call stack until
/// it reaches an enclosing `for_loop`. At that point the interrupt
/// is cleared, and the `for_loop` carries on processing as directed.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InterruptRegister {
    interrupt: Option<Interrupt>,
}

impl InterruptRegister {
    /// An interrupt state is active.
    pub fn interrupted(&self) -> bool {
        self.interrupt.is_some()
    }

    /// Sets the interrupt state. Any previous state is obliterated.
    pub fn set(&mut self, interrupt: Interrupt) {
        self.interrupt.replace(interrupt);
    }

    /// Fetches and clears the interrupt state.
    pub fn reset(&mut self) -> Option<Interrupt> {
        self.interrupt.take()
    }
}

/// Block processing interrupt state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Interrupt {
    /// Restart processing the current block.
    Continue,
    /// Stop processing the current block.
    Break,
}

#[derive(Copy, Clone, Debug)]
struct NullPartials;

impl PartialStore for NullPartials {
    fn contains(&self, _name: &str) -> bool {
        false
    }

    fn names(&self) -> Vec<&str> {
        Vec::new()
    }

    fn try_get(&self, _name: &str) -> Option<sync::Arc<dyn Renderable>> {
        None
    }

    fn get(&self, name: &str) -> Result<sync::Arc<dyn Renderable>> {
        Err(Error::with_msg("Partial does not exist").context("name", name.to_owned()))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::model::Scalar;
    use crate::model::Value;
    use crate::model::ValueViewCmp;

    #[test]
    fn mask_variables() {
        let test_path = [Scalar::new("test")];

        let rt = RuntimeBuilder::new().build();
        rt.set_global("test".into(), Value::scalar(42f64));
        assert_eq!(&rt.get(&test_path).unwrap(), &ValueViewCmp::new(&42f64));

        {
            let data = crate::object!({"test": 3});
            let new_scope = super::super::StackFrame::new(&rt, &data);

            // assert that values are chained to the parent scope
            assert_eq!(&new_scope.get(&test_path).unwrap(), &ValueViewCmp::new(&3));
        }

        // assert that the value has reverted to the old one
        assert_eq!(&rt.get(&test_path).unwrap(), &ValueViewCmp::new(&42));
    }

    #[test]
    fn global_variables() {
        let global_path = [Scalar::new("global")];

        let rt = RuntimeBuilder::new().build();

        {
            let data = crate::object!({"test": 3});
            let new_scope = super::super::StackFrame::new(&rt, &data);

            // sat a new val that we will pick up outside the scope
            new_scope.set_global("global".into(), Value::scalar("some value"));
        }
        assert_eq!(
            &rt.get(&global_path).unwrap(),
            &ValueViewCmp::new(&"some value")
        );
    }
}
