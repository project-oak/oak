//
// Copyright 2026 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

// Utilities for combining endorsement validity windows.

use oak_proto_rust::oak::Validity;
use oak_time::Instant;
use prost_types::Timestamp;

// Returns the later of two optional timestamps. If one is absent (unbounded
// start), the present timestamp wins.
fn latest_timestamp(a: Option<Timestamp>, b: Option<Timestamp>) -> Option<Timestamp> {
    match (a, b) {
        (Some(a), Some(b)) => Some(core::cmp::max_by_key(a, b, |t| Instant::from(*t))),
        (a, b) => a.or(b),
    }
}

// Returns the earlier of two optional timestamps. If one is absent (unbounded
// end), the present timestamp wins.
fn earliest_timestamp(a: Option<Timestamp>, b: Option<Timestamp>) -> Option<Timestamp> {
    match (a, b) {
        (Some(a), Some(b)) => Some(core::cmp::min_by_key(a, b, |t| Instant::from(*t))),
        (a, b) => a.or(b),
    }
}

// Intersects two optional validity windows, yielding the tightest window that
// is common to both.
//
// Conditions
// - If both inputs are `None`, return `None`.
// - If there is a `Some` and a `None`, return the `Some`.
// - If both are `Some`, the result's `not_before` is the *maximum* (latest) of
//   the two starts and its `not_after` is the *minimum* (earliest) of the two
//   expiries. This encodes the rule that the result must not be relied upon
//   once the first of the underlying endorsements expires.
//
// A missing `not_before`/`not_after` on either operand is treated as an
// unbounded edge, so the present timestamp is kept for that edge.
pub(crate) fn intersect_validity(a: Option<Validity>, b: Option<Validity>) -> Option<Validity> {
    match (a, b) {
        (Some(a), Some(b)) => Some(Validity {
            not_before: latest_timestamp(a.not_before, b.not_before),
            not_after: earliest_timestamp(a.not_after, b.not_after),
        }),
        (a, b) => a.or(b),
    }
}

// Folds an iterator of optional validity windows into their intersection.
//
// Endorsement-free reference values contribute `None` and are ignored. When
// the iterator yields no `Some`, the result is `None`, i.e. an unbounded
// window.
pub(crate) fn intersect_all_validity<I>(windows: I) -> Option<Validity>
where
    I: IntoIterator<Item = Option<Validity>>,
{
    windows.into_iter().fold(None, intersect_validity)
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use oak_time::make_instant;

    use super::*;

    fn make_validity(not_before: Option<Instant>, not_after: Option<Instant>) -> Validity {
        Validity {
            not_before: not_before.map(|t| t.into_timestamp()),
            not_after: not_after.map(|t| t.into_timestamp()),
        }
    }

    #[test]
    fn intersect_validity_both_none_returns_none() {
        assert_eq!(intersect_validity(None, None), None);
    }

    #[test]
    fn intersect_validity_single_some_passes_through() {
        let v = make_validity(
            Some(make_instant!("2026-01-01T00:00:00Z")),
            Some(make_instant!("2026-06-01T00:00:00Z")),
        );

        assert_eq!(intersect_validity(Some(v), None), Some(v));
        assert_eq!(intersect_validity(None, Some(v)), Some(v));
    }

    #[test]
    fn intersect_validity_overlapping_windows_takes_latest_start_and_earliest_end() {
        let v1 = make_validity(
            Some(make_instant!("2026-01-01T00:00:00Z")),
            Some(make_instant!("2026-06-01T00:00:00Z")),
        );
        let v2 = make_validity(
            Some(make_instant!("2026-03-01T00:00:00Z")),
            Some(make_instant!("2026-09-01T00:00:00Z")),
        );

        let expected = make_validity(
            Some(make_instant!("2026-03-01T00:00:00Z")),
            Some(make_instant!("2026-06-01T00:00:00Z")),
        );

        assert_eq!(intersect_validity(Some(v1), Some(v2)), Some(expected));
        assert_eq!(intersect_validity(Some(v2), Some(v1)), Some(expected));
    }

    #[test]
    fn intersect_validity_nested_windows_returns_inner_window() {
        let outer = make_validity(
            Some(make_instant!("2026-01-01T00:00:00Z")),
            Some(make_instant!("2026-12-01T00:00:00Z")),
        );
        let inner = make_validity(
            Some(make_instant!("2026-03-01T00:00:00Z")),
            Some(make_instant!("2026-09-01T00:00:00Z")),
        );

        assert_eq!(intersect_validity(Some(outer), Some(inner)), Some(inner));
        assert_eq!(intersect_validity(Some(inner), Some(outer)), Some(inner));
    }

    #[test]
    fn intersect_validity_identical_windows_returns_same_window() {
        let v = make_validity(
            Some(make_instant!("2026-01-01T00:00:00Z")),
            Some(make_instant!("2026-06-01T00:00:00Z")),
        );

        assert_eq!(intersect_validity(Some(v), Some(v)), Some(v));
    }

    #[test]
    fn intersect_validity_missing_bounds_preserves_present_bounds() {
        let only_start = make_validity(Some(make_instant!("2026-01-01T00:00:00Z")), None);
        let only_end = make_validity(None, Some(make_instant!("2026-06-01T00:00:00Z")));

        let expected = make_validity(
            Some(make_instant!("2026-01-01T00:00:00Z")),
            Some(make_instant!("2026-06-01T00:00:00Z")),
        );

        assert_eq!(intersect_validity(Some(only_start), Some(only_end)), Some(expected));

        let full_window = make_validity(
            Some(make_instant!("2026-01-01T00:00:00Z")),
            Some(make_instant!("2026-09-01T00:00:00Z")),
        );
        let tighter_end = make_validity(None, Some(make_instant!("2026-06-01T00:00:00Z")));

        assert_eq!(intersect_validity(Some(full_window), Some(tighter_end)), Some(expected));
    }

    #[test]
    fn intersect_all_validity_empty_iterator_returns_none() {
        assert_eq!(intersect_all_validity(vec![]), None);
    }

    #[test]
    fn intersect_all_validity_all_none_returns_none() {
        assert_eq!(intersect_all_validity(vec![None, None, None]), None);
    }

    #[test]
    fn intersect_all_validity_ignores_none_entries() {
        let v1 = make_validity(
            Some(make_instant!("2026-01-01T00:00:00Z")),
            Some(make_instant!("2026-08-01T00:00:00Z")),
        );
        let v2 = make_validity(
            Some(make_instant!("2026-03-01T00:00:00Z")),
            Some(make_instant!("2026-10-01T00:00:00Z")),
        );

        let expected = make_validity(
            Some(make_instant!("2026-03-01T00:00:00Z")),
            Some(make_instant!("2026-08-01T00:00:00Z")),
        );

        assert_eq!(
            intersect_all_validity(vec![None, Some(v1), None, Some(v2), None]),
            Some(expected)
        );
    }

    #[test]
    fn intersect_all_validity_multiple_windows_combines_to_tightest_bounds() {
        let v1 = make_validity(
            Some(make_instant!("2026-01-01T00:00:00Z")),
            Some(make_instant!("2026-10-01T00:00:00Z")),
        );
        let v2 = make_validity(
            Some(make_instant!("2026-03-01T00:00:00Z")),
            Some(make_instant!("2026-08-01T00:00:00Z")),
        );
        let v3 = make_validity(
            Some(make_instant!("2026-02-01T00:00:00Z")),
            Some(make_instant!("2026-05-01T00:00:00Z")),
        );

        // max(01-01, 03-01, 02-01) = 03-01
        // min(10-01, 08-01, 05-01) = 05-01
        let expected = make_validity(
            Some(make_instant!("2026-03-01T00:00:00Z")),
            Some(make_instant!("2026-05-01T00:00:00Z")),
        );

        assert_eq!(intersect_all_validity(vec![Some(v1), Some(v2), Some(v3)]), Some(expected));
    }
}
