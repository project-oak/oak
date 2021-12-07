// Currently this test doesn't actually check the output of the functions.
// It's only here for miri to check for any potential undefined behaviour.
// TODO: check function results

#[test]
fn test_transparent_wrapper() {
  // An external type defined in a different crate.
  #[derive(Copy, Clone, Default)]
  struct Foreign(u8);

  use bytemuck::TransparentWrapper;

  #[derive(Copy, Clone)]
  #[repr(transparent)]
  struct Wrapper(Foreign);

  unsafe impl TransparentWrapper<Foreign> for Wrapper {}

  // Traits can be implemented on crate-local wrapper.
  unsafe impl bytemuck::Zeroable for Wrapper {}
  unsafe impl bytemuck::Pod for Wrapper {}

  let _: u8 = bytemuck::cast(Wrapper::wrap(Foreign::default()));
  let _: Foreign = Wrapper::peel(bytemuck::cast(u8::default()));

  let _: &u8 = bytemuck::cast_ref(Wrapper::wrap_ref(&Foreign::default()));
  let _: &Foreign = Wrapper::peel_ref(bytemuck::cast_ref(&u8::default()));

  let _: &mut u8 =
    bytemuck::cast_mut(Wrapper::wrap_mut(&mut Foreign::default()));
  let _: &mut Foreign =
    Wrapper::peel_mut(bytemuck::cast_mut(&mut u8::default()));

  let _: &[u8] =
    bytemuck::cast_slice(Wrapper::wrap_slice(&[Foreign::default()]));
  let _: &[Foreign] =
    Wrapper::peel_slice(bytemuck::cast_slice(&[u8::default()]));

  let _: &mut [u8] =
    bytemuck::cast_slice_mut(Wrapper::wrap_slice_mut(
      &mut [Foreign::default()],
    ));
  let _: &mut [Foreign] =
    Wrapper::peel_slice_mut(bytemuck::cast_slice_mut(&mut [u8::default()]));

  let _: &[u8] = bytemuck::bytes_of(Wrapper::wrap_ref(&Foreign::default()));
  let _: &Foreign = Wrapper::peel_ref(bytemuck::from_bytes(&[u8::default()]));

  let _: &mut [u8] =
    bytemuck::bytes_of_mut(Wrapper::wrap_mut(&mut Foreign::default()));
  let _: &mut Foreign =
    Wrapper::peel_mut(bytemuck::from_bytes_mut(&mut [u8::default()]));

  // not sure if this is the right usage
  let _ =
    bytemuck::pod_align_to::<_, u8>(Wrapper::wrap_slice(&[Foreign::default()]));
  // counterpart?

  // not sure if this is the right usage
  let _ = bytemuck::pod_align_to_mut::<_, u8>(Wrapper::wrap_slice_mut(&mut [
    Foreign::default(),
  ]));
  // counterpart?
}
