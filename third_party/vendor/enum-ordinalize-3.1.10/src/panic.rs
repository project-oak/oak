#[inline]
pub fn not_enum() -> ! {
    panic!("Only enums can be ordinalized.")
}

#[inline]
pub fn not_unit_variant() -> ! {
    panic!("An ordinalized enum can only have unit variants.")
}

#[inline]
pub fn no_variant() -> ! {
    panic!("An ordinalized enum needs to have at least one variant.")
}

#[inline]
pub fn unsupported_discriminant() -> ! {
    panic!(
        "The discriminant of a variant of an ordinalized enum needs to be a legal literal integer, a constant variable/function or a constant expression."
    )
}

#[inline]
pub fn constant_variable_on_non_determined_size_enum() -> ! {
    panic!(
        "The discriminant of a variant can be assigned not to a literal integer only when the ordinalized enum is using the `repr` attribute to determine it's size before compilation."
    )
}
