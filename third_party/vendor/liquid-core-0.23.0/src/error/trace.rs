/// User-visible call trace
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub(crate) struct Trace {
    trace: Option<kstring::KString>,
    context: Vec<(kstring::KString, kstring::KString)>,
}

impl Trace {
    pub(crate) fn new(trace: kstring::KString) -> Self {
        Self {
            trace: Some(trace),
            context: vec![],
        }
    }

    pub(crate) fn empty() -> Self {
        Self {
            trace: None,
            context: vec![],
        }
    }

    pub(crate) fn append_context(&mut self, key: kstring::KString, value: kstring::KString) {
        self.context.push((key, value));
    }

    pub(crate) fn get_trace(&self) -> Option<&str> {
        self.trace.as_ref().map(|s| s.as_str())
    }

    pub(crate) fn get_context(&self) -> &[(kstring::KString, kstring::KString)] {
        self.context.as_ref()
    }
}
