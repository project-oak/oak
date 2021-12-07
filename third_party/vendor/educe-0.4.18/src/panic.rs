#![cfg_attr(not(feature = "default"), allow(dead_code))]

use crate::Trait;

#[inline]
pub fn reuse_a_trait(t: Trait) -> ! {
    panic!("The trait `{:?}` is repeatedly used.", t)
}

#[inline]
pub fn trait_not_used(t: Trait) -> ! {
    panic!("The `{:?}` trait is not used.", t)
}

#[inline]
pub fn trait_not_support_union(t: Trait) -> ! {
    panic!("The `{:?}` trait does not support to a union.", t)
}

#[inline]
pub fn attribute_incorrect_format(attribute_name: &str, correct_usage: &[&str]) -> ! {
    panic!(
        "You are using an incorrect format of the `{}` attribute.{}",
        attribute_name,
        concat_string_slice_array(correct_usage)
    )
}

#[inline]
pub fn parameter_incorrect_format(parameter_name: &str, correct_usage: &[&str]) -> ! {
    panic!(
        "You are using an incorrect format of the `{}` parameter.{}",
        parameter_name,
        concat_string_slice_array(correct_usage)
    )
}

#[inline]
pub fn derive_attribute_not_set_up_yet(attribute_name: &str) -> ! {
    panic!(
        "You are using `{}` in the `derive` attribute, but it has not been set up yet.",
        attribute_name
    )
}

#[inline]
pub fn reset_parameter(parameter_name: &str) -> ! {
    panic!("Try to reset the `{}` parameter.", parameter_name)
}

#[inline]
pub fn unknown_parameter(attribute_name: &str, parameter_name: &str) -> ! {
    panic!("Unknown parameter `{}` used in the `{}` attribute.", parameter_name, attribute_name)
}

#[inline]
pub fn set_value_expression() -> ! {
    panic!("The default value and the expression parameter can not be set at the same time.")
}

#[inline]
pub fn set_expression_bound() -> ! {
    panic!("You don't need to set the expression and the bound at the same time.")
}

#[inline]
pub fn no_default_field() -> ! {
    panic!("There is no field set as default.")
}

#[inline]
pub fn multiple_default_fields() -> ! {
    panic!("Multiple default fields are set.")
}

#[inline]
pub fn no_default_variant() -> ! {
    panic!("There is no variant set as default.")
}

#[inline]
pub fn multiple_default_variants() -> ! {
    panic!("Multiple default variants are set.")
}

#[inline]
pub fn no_deref_field() -> ! {
    panic!("There is no field which is assigned for `Deref`.")
}

#[inline]
pub fn no_deref_field_of_variant(variant_name: &str) -> ! {
    panic!(
        "There is no field for the `{variant_name}` variant which is assigned for `Deref`.",
        variant_name = variant_name
    )
}

#[inline]
pub fn multiple_deref_fields() -> ! {
    panic!("Multiple fields are set for `Deref`.")
}

#[inline]
pub fn multiple_deref_fields_of_variant(variant_name: &str) -> ! {
    panic!(
        "Multiple fields of the `{variant_name}` variant are set for deref.",
        variant_name = variant_name
    )
}

#[inline]
pub fn deref_cannot_support_unit_variant() -> ! {
    panic!("The `Deref` trait cannot be implemented for an enum which has unit variants.")
}

#[inline]
pub fn no_deref_mut_field() -> ! {
    panic!("There is no field which is assigned for `DerefMut`.")
}

#[inline]
pub fn no_deref_mut_field_of_variant(variant_name: &str) -> ! {
    panic!(
        "There is no field for the `{variant_name}` variant which is assigned for `DerefMut`.",
        variant_name = variant_name
    )
}

#[inline]
pub fn multiple_deref_mut_fields() -> ! {
    panic!("Multiple fields are set for `DerefMut`.")
}

#[inline]
pub fn multiple_deref_mut_fields_of_variant(variant_name: &str) -> ! {
    panic!(
        "Multiple fields of the `{variant_name}` variant are set for `DerefMut`.",
        variant_name = variant_name
    )
}

#[inline]
pub fn deref_mut_cannot_support_unit_variant() -> ! {
    panic!("The `DerefMut` trait cannot be implemented for an enum which has unit variants.")
}

#[inline]
pub fn disable_named_field_name() -> ! {
    panic!("You can't disable the name of a named field.")
}

#[inline]
pub fn empty_parameter(parameter_name: &str) -> ! {
    panic!("You can't set the `{}` parameter to empty.", parameter_name)
}

#[inline]
pub fn unit_struct_need_name() -> ! {
    panic!("A unit struct needs to have a name.")
}

#[inline]
pub fn unit_enum_need_name() -> ! {
    panic!("A unit enum needs to have a name.")
}

#[inline]
pub fn unit_variant_need_name() -> ! {
    panic!("A unit variant which doesn't use an enum name needs to have a name.")
}

#[inline]
pub fn ignore_ranked_field() -> ! {
    panic!("You can't ignore a ranked field.")
}

#[inline]
pub fn reuse_a_rank(rank: isize) -> ! {
    panic!("The rank `{}` is repeatedly used.", rank)
}

#[inline]
pub fn reuse_a_value(value: isize) -> ! {
    panic!("The value `{}` is repeatedly used.", value)
}

// TODO patterns

#[inline]
pub fn educe_format_incorrect() -> ! {
    attribute_incorrect_format("educe", &[stringify!(#[educe(Trait1, Trait2, ..., TraitN)])])
}

fn concat_string_slice_array(array: &[&str]) -> String {
    let len = array.len();

    if len == 0 {
        String::new()
    } else {
        let mut string = String::from(" It needs to be formed into ");

        let mut iter = array.iter();

        let first = iter.next().unwrap();

        string.push('`');
        string.push_str(&first.replace("\n", ""));
        string.push('`');

        if len > 2 {
            for s in iter.take(len - 2) {
                string.push_str(", `");
                string.push_str(&s.replace("\n", ""));
                string.push('`');
            }
        }

        if len > 1 {
            string.push_str(", or `");
            string.push_str(&array[len - 1].replace("\n", ""));
            string.push('`');
        }

        string.push('.');

        string
    }
}
