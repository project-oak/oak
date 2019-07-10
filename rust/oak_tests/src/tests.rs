extern crate oak;
extern crate oak_derive;

#[derive(oak_derive::OakNode)]
struct TestNode;
impl oak::Node for TestNode {
    fn new() -> Self {
        TestNode
    }
    fn invoke(&mut self, _grpc_method_name: &str, _grpc_pair: &mut oak::ChannelPair) {}
}

#[test]
fn test_initialize() {
    // oak_derive should ensure that oak_initialize() is defined and calls oak::set_node.
    assert_eq!(false, oak::have_node());
    oak_initialize();
    assert_eq!(true, oak::have_node());
}
