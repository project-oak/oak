//
// Copyright 2024 The Project Oak Authors
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

// Recursively remove properties from the current JSON tree that are not
// present in the previous JSON tree, and record the new properties. This can be
// helpful in order to assert equality on matching fields.
pub fn remove_new_properties(
    current: &mut serde_json::Value,
    previous: &serde_json::Value,
    path: &str,
) -> Vec<String> {
    let mut new_properties = Vec::new();
    match (current, previous) {
        (serde_json::Value::Object(current_obj), serde_json::Value::Object(previous_obj)) => {
            current_obj.retain(|key, value| {
                let new_path =
                    if path.is_empty() { format!("/{}", key) } else { format!("{}/{}", path, key) };
                if let Some(prev_value) = previous_obj.get(key) {
                    new_properties.extend(remove_new_properties(value, prev_value, &new_path));
                    true
                } else {
                    new_properties.push(new_path);
                    false
                }
            });
        }
        (serde_json::Value::Array(current_arr), serde_json::Value::Array(previous_arr)) => {
            for (index, (current_item, previous_item)) in
                current_arr.iter_mut().zip(previous_arr.iter()).enumerate()
            {
                let new_path = format!("{}/{}", path, index);
                new_properties.extend(remove_new_properties(
                    current_item,
                    previous_item,
                    &new_path,
                ));
            }
            if current_arr.len() > previous_arr.len() {
                new_properties.push(format!("{}/{}", path, previous_arr.len()));
                current_arr.truncate(previous_arr.len());
            }
        }
        _ => {}
    }
    new_properties
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn test_remove_new_properties_object() {
        let mut current = json!({
            "existing": "value",
            "new": "property"
        });
        let previous = json!({
            "existing": "value"
        });
        let new_properties = remove_new_properties(&mut current, &previous, "");
        assert_eq!(current, json!({"existing": "value"}));
        assert_eq!(new_properties, vec!["/new"]);
    }

    #[test]
    fn test_remove_new_properties_nested_object() {
        let mut current = json!({
            "nested": {
                "existing": "value",
                "new": "property"
            }
        });
        let previous = json!({
            "nested": {
                "existing": "value"
            }
        });
        let new_properties = remove_new_properties(&mut current, &previous, "");
        assert_eq!(current, json!({"nested": {"existing": "value"}}));
        assert_eq!(new_properties, vec!["/nested/new"]);
    }

    #[test]
    fn test_remove_new_properties_array() {
        let mut current = json!([1, 2, 3, 4]);
        let previous = json!([1, 2, 3]);
        let new_properties = remove_new_properties(&mut current, &previous, "");
        assert_eq!(current, json!([1, 2, 3]));
        assert_eq!(new_properties, vec!["/3"]);
    }

    #[test]
    fn test_remove_new_properties_mixed() {
        let mut current = json!({
            "array": [1, 2, {"new": "item"}],
            "object": {"existing": "value", "new": "property"}
        });
        let previous = json!({
            "array": [1, 2],
            "object": {"existing": "value"}
        });
        let new_properties = remove_new_properties(&mut current, &previous, "");
        assert_eq!(
            current,
            json!({
                "array": [1, 2],
                "object": {"existing": "value"}
            })
        );
        assert_eq!(new_properties, vec!["/array/2", "/object/new"]);
    }

    #[test]
    fn test_remove_new_properties_whole_nested_object() {
        let mut current = json!({
            "existing": "value",
            "new_object": {
                "nested1": "value1",
                "nested2": "value2"
            }
        });
        let previous = json!({
            "existing": "value"
        });
        let new_properties = remove_new_properties(&mut current, &previous, "");
        assert_eq!(current, json!({"existing": "value"}));
        assert_eq!(new_properties, vec!["/new_object"]);
    }
}
