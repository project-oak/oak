use crate::infer::*;
use crate::internal::*;

#[derive(Debug, Clone, Hash, new)]
pub struct Cast {
    pub to: DatumType,
}

impl_dyn_hash!(Cast);

impl Expansion for Cast {
    fn name(&self) -> Cow<str> {
        "Cast".into()
    }

    fn rules<'r, 'p: 'r, 's: 'r>(
        &'s self,
        s: &mut Solver<'r>,
        inputs: &'p [TensorProxy],
        outputs: &'p [TensorProxy],
    ) -> InferenceResult {
        check_input_arity(inputs, 1)?;
        check_output_arity(outputs, 1)?;
        s.equals(&inputs[0].shape, &outputs[0].shape)?;
        s.equals(&outputs[0].datum_type, self.to)?;
        Ok(())
    }

    fn wire(
        &self,
        prefix: &str,
        model: &mut TypedModel,
        inputs: &[OutletId],
    ) -> TractResult<TVec<OutletId>> {
        let idt = model.outlet_fact(inputs[0])?.datum_type;
        model.wire_node(prefix, tract_core::ops::cast::Cast::new(idt, self.to), inputs)
    }

    op_hir!();
}
