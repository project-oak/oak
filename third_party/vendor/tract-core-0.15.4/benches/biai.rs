use tract_core::internal::*;

fn mvm() {
    let mut kernels = Tensor::zero_dt(f32::datum_type(), &[256, 128]).unwrap();
    kernels.as_slice_mut::<f32>().unwrap().iter_mut().enumerate().for_each(|(x, y)| *y = x as f32);
    let mut bias = Tensor::zero_dt(f32::datum_type(), &[1, 128]).unwrap();
    bias.as_slice_mut::<f32>().unwrap().iter_mut().enumerate().for_each(|(x, y)| *y = x as f32);
    let op = tract_core::ops::matmul::mir_unary::MatMulUnary {
        a: kernels.into_arc_tensor(),
        a_trans: true,
        b_trans: true,
        c_trans: true,
    };
    let mut model = TypedModel::default();
    let source =
        model.add_source("source", TypedFact::dt_shape(f32::datum_type(), &[1, 256])).unwrap();
    let output = model.wire_node("mmm", op, &[source]).unwrap();
    let output = model
        .wire_node("bias", tract_core::ops::math::add::unary(bias.into_arc_tensor()), &output)
        .unwrap();
    model.set_output_outlets(&*output).unwrap();
    let plan = dbg!(model.into_optimized()).unwrap().into_runnable().unwrap();
    let input = Tensor::zero_dt(f32::datum_type(), &[1, 256]).unwrap();
    plan.run(tvec!(input)).unwrap();
}

iai::main!(mvm);
