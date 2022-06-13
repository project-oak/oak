//
// Copyright 2022 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

use super::*;

const BODY_LEN_MULTIPLICATOR: usize = 5;
const MOCK_LARGE_MESSAGE_LEN: usize = MAX_FRAME_BODY_SIZE * BODY_LEN_MULTIPLICATOR;

#[test]
fn test_message_fragmentation() {
    let mock_body = {
        let mut x: u8 = 0;
        let filler = || {
            x = x.overflowing_add(1).0;
            x
        };

        let mut mock_body: Vec<u8> = vec![0; MOCK_LARGE_MESSAGE_LEN];
        mock_body.fill_with(filler);
        mock_body
    };

    let message = Message {
        method_or_status: 0,
        body: mock_body,
    };

    let mut frames: Vec<Frame> = message.clone().into();

    // Large messages should be divided into multiple frames.
    assert_eq!(frames.len(), BODY_LEN_MULTIPLICATOR);

    let mut partial_message = PartialMessage::default();

    // Add all frames, except for the last. This should result in a new
    // [`PartialMessage`] each time.
    for frame in frames.drain(0..frames.len() - 1) {
        let result = partial_message.try_complete(frame).unwrap();
        partial_message = result.unwrap_err()
    }

    // Adding the last frame should return the reconstructed [`Message`].
    let reconstructed_message = partial_message
        .try_complete(frames.pop().unwrap())
        .unwrap()
        .unwrap();

    assert_eq!(message, reconstructed_message);
}

#[test]
fn test_message_reconstruction_for_messages_small_messages() {
    let mock_body: Vec<u8> = vec![0; MAX_FRAME_BODY_SIZE - 1];
    let small_message = Message {
        method_or_status: 0,
        body: mock_body,
    };

    let frames: Vec<Frame> = small_message.clone().into();
    assert_eq!(frames.len(), 1);

    let reconstructed_message = PartialMessage::default()
        .try_complete(frames[0].clone())
        .unwrap()
        .unwrap();

    assert_eq!(small_message, reconstructed_message);
}

#[test]
fn test_message_reconstruction_for_messages_with_an_empty_body() {
    let empty_body_message = Message {
        method_or_status: 0,
        body: Vec::new(),
    };

    let frames: Vec<Frame> = empty_body_message.clone().into();
    assert_eq!(frames.len(), 1);

    let reconstructed_message = PartialMessage::default()
        .try_complete(frames[0].clone())
        .unwrap()
        .unwrap();

    assert_eq!(empty_body_message, reconstructed_message);
}

#[test]
fn test_message_reconstruction_double_start_frame() {
    let start_frame = Frame {
        method_or_status: 0,
        flag: Flag::StreamStart,
        body: Vec::new(),
    };

    let empty_partial_message = PartialMessage::default();
    let resulting_partial_message = empty_partial_message
        .try_complete(start_frame.clone())
        .unwrap()
        .unwrap_err();

    assert_eq!(
        Err(MessageReconstructionErrors::DoubleStartFrame),
        resulting_partial_message.try_complete(start_frame),
    );
}

#[test]
fn test_message_reconstruction_expected_start_frame() {
    assert_eq!(
        Err(MessageReconstructionErrors::ExpectedStartFrame),
        PartialMessage::default().try_complete(Frame {
            method_or_status: 0,
            flag: Flag::StreamContinuance,
            body: Vec::new(),
        })
    );
    assert_eq!(
        Err(MessageReconstructionErrors::ExpectedStartFrame),
        PartialMessage::default().try_complete(Frame {
            method_or_status: 0,
            flag: Flag::StreamEnd,
            body: Vec::new(),
        })
    );
}

#[test]
fn test_message_reconstruction_frame_header_mismatch() {
    let start_frame = Frame {
        method_or_status: 0,
        flag: Flag::StreamStart,
        body: Vec::new(),
    };
    let continuance_frame_of_a_different_method = Frame {
        method_or_status: 1,
        flag: Flag::StreamContinuance,
        body: Vec::new(),
    };

    let empty_partial_message = PartialMessage::default();
    let resulting_partial_message = empty_partial_message
        .try_complete(start_frame)
        .unwrap()
        .unwrap_err();

    assert_eq!(
        Err(MessageReconstructionErrors::MismatchingFrameHeader),
        resulting_partial_message.try_complete(continuance_frame_of_a_different_method),
    );
}
