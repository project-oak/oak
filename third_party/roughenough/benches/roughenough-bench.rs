#[macro_use]
extern crate criterion;
extern crate roughenough;

use criterion::{black_box, Criterion};
use roughenough::RtMessage;
use roughenough::Tag;
use roughenough::merkle::{MerkleTree, root_from_paths};

fn create_empty_message(c: &mut Criterion) {
    c.bench_function("create empty message", |b| b.iter(|| RtMessage::new(0)));
}

fn create_single_field_message(c: &mut Criterion) {
    c.bench_function("create single field message", |b| b.iter(|| {
        let mut msg = RtMessage::new(1);
        msg.add_field(Tag::NONC, "1234".as_bytes()).unwrap();
    }));
}

fn create_two_field_message(c: &mut Criterion) {
    c.bench_function("create two field message", |b| b.iter(|| {
        let mut msg = RtMessage::new(2);
        msg.add_field(Tag::NONC, "1234".as_bytes()).unwrap();
        msg.add_field(Tag::PAD, "abcd".as_bytes()).unwrap();
    }));
}

fn create_four_field_message(c: &mut Criterion) {
    c.bench_function("create four field message", |b| b.iter(|| {
        let mut msg = RtMessage::new(4);
        msg.add_field(Tag::SIG, "0987".as_bytes()).unwrap();
        msg.add_field(Tag::NONC, "wxyz".as_bytes()).unwrap();
        msg.add_field(Tag::DELE, "1234".as_bytes()).unwrap();
        msg.add_field(Tag::PATH, "abcd".as_bytes()).unwrap();
    }));
}

fn create_nested_message(c: &mut Criterion) {
    let pad = [0u8; 400];

    c.bench_function("create nested message", move |b| b.iter(|| {
        let mut msg1 = RtMessage::new(4);
        msg1.add_field(Tag::SIG, "0987".as_bytes()).unwrap();
        msg1.add_field(Tag::NONC, "wxyz".as_bytes()).unwrap();
        msg1.add_field(Tag::DELE, "1234".as_bytes()).unwrap();
        msg1.add_field(Tag::PATH, "abcd".as_bytes()).unwrap();

        let mut msg2 = RtMessage::new(2);
        msg2.add_field(Tag::PUBK, "1234567890".as_bytes()).unwrap();
        msg2.add_field(Tag::PAD, pad.as_ref()).unwrap();
    }));
}

static SIZES: &[u8] = &[1, 3, 9, 17, 200];
static DATA: &[u8] = &[1u8; 64];

fn create_new_merkle_tree(c: &mut Criterion) {
    c.bench_function_over_inputs("create new merkle trees", move |b, &size| {
        b.iter(|| {
            let mut tree = MerkleTree::new();
            for _ in 0..*size {
                tree.push_leaf(DATA);
            }
            black_box(tree.compute_root())
        })
    }, SIZES);
}

fn reuse_merkle_trees(c: &mut Criterion) {
    let mut tree = MerkleTree::new();

    c.bench_function_over_inputs("reuse existing merkle tree", move |b, &size| {
        b.iter(|| {
            tree.reset();
            for _ in 0..*size {
                tree.push_leaf(DATA);
            }
            black_box(tree.compute_root());
        })
    }, SIZES);
}

criterion_group!(message_creation,
  create_empty_message,
  create_single_field_message,
  create_two_field_message,
  create_four_field_message,
  create_nested_message
);

criterion_group!(merkle_tree,
    create_new_merkle_tree,
    reuse_merkle_trees
);

criterion_main!(message_creation, merkle_tree);
