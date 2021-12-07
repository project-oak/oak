use std::fmt;

use crate::error::{Error, Result};
use crate::model::Path;
use crate::model::Scalar;
use crate::model::{ValueCow, ValueView};

use super::Expression;
use super::Runtime;

/// A `Value` reference.
#[derive(Clone, Debug, PartialEq)]
pub struct Variable {
    variable: Scalar,
    indexes: Vec<Expression>,
}

impl Variable {
    /// Create a `Value` reference.
    pub fn with_literal<S: Into<Scalar>>(value: S) -> Self {
        Self {
            variable: value.into(),
            indexes: Default::default(),
        }
    }

    /// Append a literal.
    pub fn push_literal<S: Into<Scalar>>(mut self, value: S) -> Self {
        self.indexes.push(Expression::with_literal(value));
        self
    }

    /// Convert to a `Path`.
    pub fn try_evaluate<'c>(&'c self, runtime: &'c dyn Runtime) -> Option<Path<'c>> {
        let mut path = Path::with_index(self.variable.as_ref());
        path.reserve(self.indexes.len());
        for expr in &self.indexes {
            let v = expr.try_evaluate(runtime)?;
            let s = match v {
                ValueCow::Owned(v) => v.into_scalar(),
                ValueCow::Borrowed(v) => v.as_scalar(),
            }?;
            path.push(s);
        }
        Some(path)
    }

    /// Convert to a `Path`.
    pub fn evaluate<'c>(&'c self, runtime: &'c dyn Runtime) -> Result<Path<'c>> {
        let mut path = Path::with_index(self.variable.as_ref());
        path.reserve(self.indexes.len());
        for expr in &self.indexes {
            let v = expr.evaluate(runtime)?;
            let s = match v {
                ValueCow::Owned(v) => v.into_scalar(),
                ValueCow::Borrowed(v) => v.as_scalar(),
            }
            .ok_or_else(|| {
                let v = expr.evaluate(runtime).expect("lookup already verified");
                let v = v.source();
                let msg = format!("Expected scalar, found `{}`", v);
                Error::with_msg(msg)
            })?;
            path.push(s);
        }
        Ok(path)
    }
}

impl Extend<Scalar> for Variable {
    fn extend<T: IntoIterator<Item = Scalar>>(&mut self, iter: T) {
        let path = iter.into_iter().map(Expression::with_literal);
        self.indexes.extend(path);
    }
}

impl Extend<Expression> for Variable {
    fn extend<T: IntoIterator<Item = Expression>>(&mut self, iter: T) {
        let path = iter.into_iter();
        self.indexes.extend(path);
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.variable.render())?;
        for index in self.indexes.iter() {
            write!(f, "[{}]", index)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::model::Object;
    use crate::model::ValueViewCmp;

    use super::super::RuntimeBuilder;
    use super::super::StackFrame;

    #[test]
    fn identifier_path_array_index() {
        let globals: Object = serde_yaml::from_str(
            r#"
test_a: ["test"]
"#,
        )
        .unwrap();
        let mut var = Variable::with_literal("test_a");
        let index = vec![Scalar::new(0)];
        var.extend(index);

        let runtime = RuntimeBuilder::new().build();
        let runtime = StackFrame::new(&runtime, &globals);
        let actual = var.evaluate(&runtime).unwrap();
        let actual = runtime.get(&actual).unwrap();
        assert_eq!(actual, ValueViewCmp::new(&"test"));
    }

    #[test]
    fn identifier_path_array_index_negative() {
        let globals: Object = serde_yaml::from_str(
            r#"
test_a: ["test1", "test2"]
"#,
        )
        .unwrap();
        let mut var = Variable::with_literal("test_a");
        let index = vec![Scalar::new(-1)];
        var.extend(index);

        let runtime = RuntimeBuilder::new().build();
        let runtime = StackFrame::new(&runtime, &globals);
        let actual = var.evaluate(&runtime).unwrap();
        let actual = runtime.get(&actual).unwrap();
        assert_eq!(actual, ValueViewCmp::new(&"test2"));
    }

    #[test]
    fn identifier_path_object() {
        let globals: Object = serde_yaml::from_str(
            r#"
test_a:
  - test_h: 5
"#,
        )
        .unwrap();
        let mut var = Variable::with_literal("test_a");
        let index = vec![Scalar::new(0), Scalar::new("test_h")];
        var.extend(index);

        let runtime = RuntimeBuilder::new().build();
        let runtime = StackFrame::new(&runtime, &globals);
        let actual = var.evaluate(&runtime).unwrap();
        let actual = runtime.get(&actual).unwrap();
        assert_eq!(actual, ValueViewCmp::new(&5));
    }
}
