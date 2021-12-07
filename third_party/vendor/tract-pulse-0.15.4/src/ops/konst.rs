use crate::internal::*;
use tract_core::ops::konst::Const;

submit_op_pulsifier!(Const, konst);

fn konst(
    op: &Const,
    _source: &TypedModel,
    node: &TypedNode,
    target: &mut PulsedModel,
    mapping: &HashMap<OutletId, OutletId>,
    _pulse: usize,
) -> TractResult<TVec<OutletId>> {
    target.wire_node(&*node.name, &op, &[])
}

impl PulsedOp for Const {
    fn pulsed_output_facts(&self, _inputs: &[&PulsedFact]) -> TractResult<TVec<PulsedFact>> {
        Ok(tvec!(self.0.into()))
    }

    as_op!();
    pulsed_op_to_typed_op!();
}
