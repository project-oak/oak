use crate::internal::*;
use crate::ser::*;
use tract_core::ops;

pub fn register(registry: &mut Registry) {
    registry.register_dumper(TypeId::of::<ops::array::MultiBroadcastTo>(), ser_broadcast);
    registry.register_primitive(
        "tract_core_constant_of_shape",
        &[TypeName::Scalar.tensor().named("input"), TypeName::Integer.array().named("shape")],
        de_broadcast,
    );
}


