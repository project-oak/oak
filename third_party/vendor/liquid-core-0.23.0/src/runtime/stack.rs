use crate::error::Error;
use crate::error::Result;
use crate::model::{Object, ObjectView, ScalarCow, Value, ValueCow, ValueView};

/// Layer variables on top of the existing runtime
pub struct StackFrame<P, O> {
    parent: P,
    name: Option<kstring::KString>,
    data: O,
}

impl<P: super::Runtime, O: ObjectView> StackFrame<P, O> {
    /// Layer variables on top of the existing runtime
    pub fn new(parent: P, data: O) -> Self {
        Self {
            parent,
            name: None,
            data,
        }
    }

    /// Name the current context
    pub fn with_name<S: Into<kstring::KString>>(mut self, name: S) -> Self {
        self.name = Some(name.into());
        self
    }
}

impl<P: super::Runtime, O: ObjectView> super::Runtime for StackFrame<P, O> {
    fn partials(&self) -> &dyn super::PartialStore {
        self.parent.partials()
    }

    fn name(&self) -> Option<kstring::KStringRef<'_>> {
        self.name
            .as_ref()
            .map(|n| n.as_ref())
            .or_else(|| self.parent.name())
    }

    fn roots(&self) -> std::collections::BTreeSet<kstring::KStringCow<'_>> {
        let mut roots = self.parent.roots();
        roots.extend(self.data.keys());
        roots
    }

    fn try_get(&self, path: &[ScalarCow<'_>]) -> Option<ValueCow<'_>> {
        let key = path.first()?;
        let key = key.to_kstr();
        let data = &self.data;
        if data.contains_key(key.as_str()) {
            crate::model::try_find(data.as_value(), path)
        } else {
            self.parent.try_get(path)
        }
    }

    fn get(&self, path: &[ScalarCow<'_>]) -> Result<ValueCow<'_>> {
        let key = path.first().ok_or_else(|| {
            Error::with_msg("Unknown variable").context("requested variable", "nil")
        })?;
        let key = key.to_kstr();
        let data = &self.data;
        if data.contains_key(key.as_str()) {
            crate::model::find(data.as_value(), path).map(|v| v.into_owned().into())
        } else {
            self.parent.get(path)
        }
    }

    fn set_global(
        &self,
        name: kstring::KString,
        val: crate::model::Value,
    ) -> Option<crate::model::Value> {
        self.parent.set_global(name, val)
    }

    fn set_index(&self, name: kstring::KString, val: Value) -> Option<Value> {
        self.parent.set_index(name, val)
    }

    fn get_index<'a>(&'a self, name: &str) -> Option<ValueCow<'a>> {
        self.parent.get_index(name)
    }

    fn registers(&self) -> &super::Registers {
        self.parent.registers()
    }
}

pub(crate) struct GlobalFrame<P> {
    parent: P,
    data: std::cell::RefCell<Object>,
}

impl<P: super::Runtime> GlobalFrame<P> {
    pub fn new(parent: P) -> Self {
        Self {
            parent,
            data: Default::default(),
        }
    }
}

impl<P: super::Runtime> super::Runtime for GlobalFrame<P> {
    fn partials(&self) -> &dyn super::PartialStore {
        self.parent.partials()
    }

    fn name(&self) -> Option<kstring::KStringRef<'_>> {
        self.parent.name()
    }

    fn roots(&self) -> std::collections::BTreeSet<kstring::KStringCow<'_>> {
        let mut roots = self.parent.roots();
        roots.extend(self.data.borrow().keys().map(|k| k.clone().into()));
        roots
    }

    fn try_get(&self, path: &[ScalarCow<'_>]) -> Option<ValueCow<'_>> {
        let key = path.first()?;
        let key = key.to_kstr();
        let data = self.data.borrow();
        if data.contains_key(key.as_str()) {
            crate::model::try_find(data.as_value(), path).map(|v| v.into_owned().into())
        } else {
            self.parent.try_get(path)
        }
    }

    fn get(&self, path: &[ScalarCow<'_>]) -> Result<ValueCow<'_>> {
        let key = path.first().ok_or_else(|| {
            Error::with_msg("Unknown variable").context("requested variable", "nil")
        })?;
        let key = key.to_kstr();
        let data = self.data.borrow();
        if data.contains_key(key.as_str()) {
            crate::model::find(data.as_value(), path).map(|v| v.into_owned().into())
        } else {
            self.parent.get(path)
        }
    }

    fn set_global(
        &self,
        name: kstring::KString,
        val: crate::model::Value,
    ) -> Option<crate::model::Value> {
        let mut data = self.data.borrow_mut();
        data.insert(name, val)
    }

    fn set_index(&self, name: kstring::KString, val: Value) -> Option<Value> {
        self.parent.set_index(name, val)
    }

    fn get_index<'a>(&'a self, name: &str) -> Option<ValueCow<'a>> {
        self.parent.get_index(name)
    }

    fn registers(&self) -> &super::Registers {
        self.parent.registers()
    }
}

pub(crate) struct IndexFrame<P> {
    parent: P,
    data: std::cell::RefCell<Object>,
}

impl<P: super::Runtime> IndexFrame<P> {
    pub fn new(parent: P) -> Self {
        Self {
            parent,
            data: Default::default(),
        }
    }
}

impl<P: super::Runtime> super::Runtime for IndexFrame<P> {
    fn partials(&self) -> &dyn super::PartialStore {
        self.parent.partials()
    }

    fn name(&self) -> Option<kstring::KStringRef<'_>> {
        self.parent.name()
    }

    fn roots(&self) -> std::collections::BTreeSet<kstring::KStringCow<'_>> {
        let mut roots = self.parent.roots();
        roots.extend(self.data.borrow().keys().map(|k| k.clone().into()));
        roots
    }

    fn try_get(&self, path: &[ScalarCow<'_>]) -> Option<ValueCow<'_>> {
        let key = path.first()?;
        let key = key.to_kstr();
        let data = self.data.borrow();
        if data.contains_key(key.as_str()) {
            crate::model::try_find(data.as_value(), path).map(|v| v.into_owned().into())
        } else {
            self.parent.try_get(path)
        }
    }

    fn get(&self, path: &[ScalarCow<'_>]) -> Result<ValueCow<'_>> {
        let key = path.first().ok_or_else(|| {
            Error::with_msg("Unknown variable").context("requested variable", "nil")
        })?;
        let key = key.to_kstr();
        let data = self.data.borrow();
        if data.contains_key(key.as_str()) {
            crate::model::find(data.as_value(), path).map(|v| v.into_owned().into())
        } else {
            self.parent.get(path)
        }
    }

    fn set_global(
        &self,
        name: kstring::KString,
        val: crate::model::Value,
    ) -> Option<crate::model::Value> {
        self.parent.set_global(name, val)
    }

    fn set_index(&self, name: kstring::KString, val: Value) -> Option<Value> {
        let mut data = self.data.borrow_mut();
        data.insert(name, val)
    }

    fn get_index<'a>(&'a self, name: &str) -> Option<ValueCow<'a>> {
        self.data.borrow().get(name).map(|v| v.to_value().into())
    }

    fn registers(&self) -> &super::Registers {
        self.parent.registers()
    }
}
