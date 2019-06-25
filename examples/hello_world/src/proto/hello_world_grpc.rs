use protobuf::Message;
use std::io::Write;

// Oak node server interface
pub trait HelloWorldNode {
    fn say_hello(&self, req: super::hello_world::HelloRequest) -> super::hello_world::HelloResponse;

    fn lots_of_replies(&self, req: super::hello_world::HelloRequest) -> Vec<super::hello_world::HelloResponse>;

    fn lots_of_greetings(&self, reqs: Vec<super::hello_world::HelloRequest>) -> super::hello_world::HelloResponse;

    fn bidi_hello(&self, reqs: Vec<super::hello_world::HelloRequest>) -> Vec<super::hello_world::HelloResponse>;
}

pub fn dispatch(node: &HelloWorldNode, grpc_method_name: &str, grpc_channel: &mut oak::Channel) {
    match grpc_method_name {
        "/oak.examples.hello_world.HelloWorld/SayHello" => {
            let req = protobuf::parse_from_reader(grpc_channel).unwrap();
            let rsp = node.say_hello(req);
            rsp.write_to_writer(grpc_channel).unwrap();
        }
        "/oak.examples.hello_world.HelloWorld/LotsOfReplies" => {
            let req = protobuf::parse_from_reader(grpc_channel).unwrap();
            let rsps = node.lots_of_replies(req);
            for rsp in rsps {
                rsp.write_to_writer(grpc_channel).unwrap();
            }
        }
        "/oak.examples.hello_world.HelloWorld/LotsOfGreetings" => {
            let mut reqs = vec![];
            loop {
                match protobuf::parse_from_reader(grpc_channel) {
                    Err(_) => break,
                    Ok(req) => reqs.push(req),
                }
            }
            let rsp = node.lots_of_greetings(reqs);
            rsp.write_to_writer(grpc_channel).unwrap();
        }
        "/oak.examples.hello_world.HelloWorld/BidiHello" => {
            let mut reqs = vec![];
            loop {
                match protobuf::parse_from_reader(grpc_channel) {
                    Err(_) => break,
                    Ok(req) => reqs.push(req),
                }
            }
            let rsps = node.bidi_hello(reqs);
            for rsp in rsps {
                rsp.write_to_writer(grpc_channel).unwrap();
            }
        }
        _ => {
            writeln!(oak::logging_channel(), "unknown method name: {}", grpc_method_name).unwrap();
            panic!("unknown method name");
        }
    };
}
