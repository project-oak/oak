use gif::{ColorOutput, Decoder, Encoder, Frame};

#[test]
fn encode_roundtrip() {
    const ORIGINAL: &'static [u8] = include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/tests/samples/2x2.gif"));
    round_trip_from_image(ORIGINAL);
}

fn round_trip_from_image(original: &[u8]) {
    let (width, height, global_palette);
    let frames: Vec<Frame> = {
        let mut decoder = Decoder::new(original).unwrap();
        width = decoder.width();
        height = decoder.height();
        global_palette = decoder
            .global_palette()
            .unwrap_or_default()
            .to_vec();
        core::iter::from_fn(move || {
            decoder.read_next_frame().unwrap().cloned()
        }).collect()
    };

    let mut buffer = vec![];
    {
        let mut encoder = Encoder::new(&mut buffer, width, height, &global_palette).unwrap();
        for frame in &frames {
            encoder.write_frame(frame).unwrap();
        }
    }

    {
        let mut decoder = Decoder::new(&buffer[..]).expect("Invalid info encoded");
        assert_eq!(decoder.width(), width);
        assert_eq!(decoder.height(), height);
        assert_eq!(global_palette, decoder.global_palette().unwrap_or_default());
        let new_frames: Vec<_> = core::iter::from_fn(move || {
            decoder.read_next_frame().unwrap().cloned()
        }).collect();
        assert_eq!(new_frames.len(), frames.len(), "Diverging number of frames");
        for (new, reference) in new_frames.iter().zip(&frames) {
            assert_eq!(new.delay, reference.delay);
            assert_eq!(new.dispose, reference.dispose);
            assert_eq!(new.transparent, reference.transparent);
            assert_eq!(new.needs_user_input, reference.needs_user_input);
            assert_eq!(new.top, reference.top);
            assert_eq!(new.left, reference.left);
            assert_eq!(new.width, reference.width);
            assert_eq!(new.height, reference.height);
            assert_eq!(new.interlaced, reference.interlaced);
            assert_eq!(new.palette, reference.palette);
            assert_eq!(new.buffer, reference.buffer);
        }
    }
}

#[test]
fn encode_roundtrip_few_colors() {
    const WIDTH: u16 = 128;
    const HEIGHT: u16 = 128;

    // Build an image with a single red pixel, that NeuQuant won't
    // sample, in order to check that we do appropriatelyq specialise the
    // few-colors case.
    let mut pixels: Vec<u8> = vec![255; WIDTH as usize * HEIGHT as usize * 4];
    // Top-left pixel is always sampled, so use the second pixel.
    pixels[5] = 0;
    pixels[6] = 0;
    // Set speed to 30 to handily avoid sampling that one pixel.
    //
    // We clone "pixels", since the parameter is replaced with a
    // paletted version, and later we want to compare the output with
    // the original RGBA image.
    let frames = [Frame::from_rgba_speed(WIDTH, HEIGHT, &mut pixels.clone(), 30)];

    let mut buffer = vec![];
    {
        let mut encoder = Encoder::new(&mut buffer, WIDTH, HEIGHT, &[]).unwrap();
        for frame in &frames {
            encoder.write_frame(frame).unwrap();
        }
    }

    {
        let mut decoder = {
            let mut builder = Decoder::<&[u8]>::build();
            builder.set_color_output(ColorOutput::RGBA);
            builder.read_info(&buffer[..]).expect("Invalid info encoded")
        };

        // Only check key fields, assuming "round_trip_from_image"
        // covers the rest. We are primarily concerned with quantisation.
        assert_eq!(decoder.width(), WIDTH);
        assert_eq!(decoder.height(), HEIGHT);
        let new_frames: Vec<_> = core::iter::from_fn(move || {
            decoder.read_next_frame().unwrap().cloned()
        }).collect();
        assert_eq!(new_frames.len(), 1, "Diverging number of frames");
        // NB: reference.buffer can't be used as it contains the palette version.
        assert_eq!(new_frames[0].buffer, pixels);
    }
}
