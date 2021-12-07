use std::{env, fs, process};

fn main() {
    let file = env::args().nth(1)
        .unwrap_or_else(|| explain_usage());
    let file = fs::File::open(&file)
        .expect("failed to open input file");
    let mut reader = {
        let mut options = gif::DecodeOptions::new();
        options.allow_unknown_blocks(true);
        options.read_info(file).unwrap()
    };

    loop {
        let frame = match reader.read_next_frame() {
            Ok(Some(frame)) => frame,
            Ok(None) => break,
            Err(error) => {
                println!("Error: {:?}", error);
                break;
            }
        };

        println!(
            " Frame:\n  \
                 delay: {:?}\n  \
                 canvas: {}x{}+{}+{}\n  \
                 dispose: {:?}\n  \
                 needs_input: {:?}",
            frame.delay,
            frame.width, frame.height, frame.left, frame.top,
            frame.dispose,
            frame.needs_user_input
        );
    }
}

fn explain_usage() -> ! {
    println!("Print information on the frames of a gif.\n\nUsage: check <file>");
    process::exit(1)
}
