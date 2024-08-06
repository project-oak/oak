use alloc::vec;
use hashbrown::hash_map::Entry;
use hashbrown::HashMap;
use spinning_top::Spinlock as Mutex;

use crate::{metrics::data::DataPoint, metrics::AttributeSet};
use opentelemetry_rk::{global, metrics::MetricsError, KeyValue};

use super::{
    aggregate::{is_under_cardinality_limit, STREAM_OVERFLOW_ATTRIBUTE_SET},
    Number,
};

/// Timestamped measurement data.
struct DataPointValue<T> {
    value: T,
}

/// Summarizes a set of measurements as the last one made.
#[derive(Default)]
pub(crate) struct LastValue<T> {
    values: Mutex<HashMap<AttributeSet, DataPointValue<T>>>,
}

impl<T: Number<T>> LastValue<T> {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn measure(&self, measurement: T, attrs: AttributeSet) {
        let d: DataPointValue<T> = DataPointValue { value: measurement };
        if let Some(mut values) = self.values.try_lock() {
            let size = values.len();
            match values.entry(attrs) {
                Entry::Occupied(mut occupied_entry) => {
                    occupied_entry.insert(d);
                }
                Entry::Vacant(vacant_entry) => {
                    if is_under_cardinality_limit(size) {
                        vacant_entry.insert(d);
                    } else {
                        values.insert(STREAM_OVERFLOW_ATTRIBUTE_SET.clone(), d);
                        global::handle_error(MetricsError::Other("Warning: Maximum data points for metric stream exceeded. Entry added to overflow.".into()));
                    }
                }
            }
        }
    }

    pub(crate) fn compute_aggregation(&self, dest: &mut vec::Vec<DataPoint<T>>) {
        dest.clear();
        let mut values = match self.values.try_lock() {
            Some(guard) if !guard.is_empty() => guard,
            _ => return,
        };

        let n = values.len();
        if n > dest.capacity() {
            dest.reserve_exact(n - dest.capacity());
        }

        for (attrs, value) in values.drain() {
            dest.push(DataPoint {
                attributes: attrs
                    .iter()
                    .map(|(k, v)| KeyValue::new(k.clone(), v.clone()))
                    .collect(),
                value: value.value,
                exemplars: vec![],
            });
        }
    }
}
