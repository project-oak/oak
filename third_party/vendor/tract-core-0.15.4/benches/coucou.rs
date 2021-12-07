extern crate criterion;
extern crate tract_core;
use criterion::*;

use nn::DataFormat::HWC;
use tract_core::internal::*;
use tract_core::ops::{cnn, nn};

/*
   fn im2col(c: &mut Criterion) {
   let mut group = c.benchmark_group("im2col");
   for dil in &[1, 2, 4, 8] {
   group.bench_function(&format!("dil_{}", dil), |b| {
   b.iter_with_setup(
   || {
   let len = 8 + 2 * *dil;
   let input = tvec!(Tensor::zero_dt(f32::datum_type(), &[len, 16])
   .unwrap()
   .into_arc_tensor());
   let op = tract_core::ops::cnn::conv::Im2Col::new(
   cnn::PatchSpec::for_full_shape(HWC, &[len, 16])
   .unwrap()
   .with_kernel_shape(tvec![3])
   .with_dilations(tvec!(*dil))
   .into_patch(),
   HWC, //.shape(tvec![len, 16]).unwrap(),
   64,
   48,
   8,
   1,
   16,
//        tract_linalg::ops().mmm(64, 48, 8, f32::datum_type(), f32::datum_type(), f32::datum_type()),
(tract_linalg::ops().mmm_f32)(64, 48, 8).b_pack(),
tensor0(0.0f32),
)
.unwrap();
(input, op)
},
|(input, op)| {
op.eval(input).unwrap();
},
)
});
}
}
*/

fn mvm(c: &mut Criterion) {
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
    c.bench_function("matvecmul", |b| {
        b.iter_with_setup(
            || {
                let input = Tensor::zero_dt(f32::datum_type(), &[1, 256]).unwrap();
                input
            },
            |input| plan.run(tvec!(input)).unwrap(),
        )
    });
}

fn ruin_cache() {
    for i in 0..10 {
        let _a = (0..1000000).collect::<Vec<i32>>();
    }
}

/*
fn mmm(c: &mut Criterion, m: usize, k: usize, n: usize) {
c.bench_function("matmatmul", |b| {
b.iter_custom(|it| {
let mmm = (tract_linalg::ops().mmm_f32)(m, k, n);
let packed_a = unsafe {
Tensor::uninitialized_aligned_dt(
f32::datum_type(),
&[mmm.a_pack().len(m)],
mmm.a_pack().alignment(),
)
.unwrap()
};
let packed_b = unsafe {
Tensor::uninitialized_aligned_dt(
f32::datum_type(),
&[mmm.b_pack().len(n)],
mmm.b_pack().alignment(),
)
.unwrap()
};
let op = tract_core::ops::matmul::lir_unary::LirMatMulUnary {
c_trans: true,
c_fact: TypedFact::dt_shape(f32::datum_type(), [n, m].as_ref()),
c_prefix_dim_and_stride: None,
packed_as: tract_ndarray::arr1(&[packed_a.into_arc_tensor()]).into_dyn(),
fused_ops: None,
mmm,
k,
};
let packed_b = packed_b.into_arc_tensor();
let mut dur = std::time::Duration::default();
for _ in 0..it {
ruin_cache();
let start = std::time::Instant::now();
op.eval(tvec!(packed_b.clone())).unwrap();
dur += start.elapsed();
}
dur
})
});
}

fn asr_8m_tddn2_packed(c: &mut Criterion) {
mmm(c, 512, 1536, 24)
}
*/

criterion_group!(benches, /* im2col, asr_8m_tddn2_packed, */ mvm);
criterion_main!(benches);
