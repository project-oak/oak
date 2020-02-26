#[derive(Clone, PartialEq, ::prost::Message)]
pub struct HelloRequest {
    #[prost(string, tag = "1")]
    pub greeting: std::string::String,
}
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct HelloResponse {
    #[prost(string, tag = "1")]
    pub reply: std::string::String,
}
/// Generated server implementations.
pub mod hello_world_server {
    #![allow(unused_variables, dead_code, missing_docs)]
    use tonic::codegen::*;
    ///Generated trait containing gRPC methods that should be implemented for use with
    /// HelloWorldServer.
    #[async_trait]
    pub trait HelloWorld: Send + Sync + 'static {
        async fn say_hello(
            &self,
            request: tonic::Request<super::HelloRequest>,
        ) -> Result<tonic::Response<super::HelloResponse>, tonic::Status>;
        ///Server streaming response type for the LotsOfReplies method.
        type LotsOfRepliesStream: Stream<Item = Result<super::HelloResponse, tonic::Status>>
            + Send
            + Sync
            + 'static;
        async fn lots_of_replies(
            &self,
            request: tonic::Request<super::HelloRequest>,
        ) -> Result<tonic::Response<Self::LotsOfRepliesStream>, tonic::Status>;
        async fn lots_of_greetings(
            &self,
            request: tonic::Request<tonic::Streaming<super::HelloRequest>>,
        ) -> Result<tonic::Response<super::HelloResponse>, tonic::Status>;
        ///Server streaming response type for the BidiHello method.
        type BidiHelloStream: Stream<Item = Result<super::HelloResponse, tonic::Status>>
            + Send
            + Sync
            + 'static;
        async fn bidi_hello(
            &self,
            request: tonic::Request<tonic::Streaming<super::HelloRequest>>,
        ) -> Result<tonic::Response<Self::BidiHelloStream>, tonic::Status>;
    }
    /// As seen in https://grpc.io/docs/guides/concepts/.
    #[derive(Debug)]
    #[doc(hidden)]
    pub struct HelloWorldServer<T: HelloWorld> {
        inner: _Inner<T>,
    }
    struct _Inner<T>(Arc<T>, Option<tonic::Interceptor>);
    impl<T: HelloWorld> HelloWorldServer<T> {
        pub fn new(inner: T) -> Self {
            let inner = Arc::new(inner);
            let inner = _Inner(inner, None);
            Self { inner }
        }
        pub fn with_interceptor(inner: T, interceptor: impl Into<tonic::Interceptor>) -> Self {
            let inner = Arc::new(inner);
            let inner = _Inner(inner, Some(interceptor.into()));
            Self { inner }
        }
    }
    impl<T: HelloWorld> Service<http::Request<HyperBody>> for HelloWorldServer<T> {
        type Response = http::Response<tonic::body::BoxBody>;
        type Error = Never;
        type Future = BoxFuture<Self::Response, Self::Error>;
        fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
            Poll::Ready(Ok(()))
        }
        fn call(&mut self, req: http::Request<HyperBody>) -> Self::Future {
            let inner = self.inner.clone();
            match req.uri().path() {
                "/oak.examples.hello_world.HelloWorld/SayHello" => {
                    struct SayHelloSvc<T: HelloWorld>(pub Arc<T>);
                    impl<T: HelloWorld> tonic::server::UnaryService<super::HelloRequest> for SayHelloSvc<T> {
                        type Response = super::HelloResponse;
                        type Future = BoxFuture<tonic::Response<Self::Response>, tonic::Status>;
                        fn call(
                            &mut self,
                            request: tonic::Request<super::HelloRequest>,
                        ) -> Self::Future {
                            let inner = self.0.clone();
                            let fut = async move { inner.say_hello(request).await };
                            Box::pin(fut)
                        }
                    }
                    let inner = self.inner.clone();
                    let fut = async move {
                        let interceptor = inner.1.clone();
                        let inner = inner.0;
                        let method = SayHelloSvc(inner);
                        let codec = tonic::codec::ProstCodec::default();
                        let mut grpc = if let Some(interceptor) = interceptor {
                            tonic::server::Grpc::with_interceptor(codec, interceptor)
                        } else {
                            tonic::server::Grpc::new(codec)
                        };
                        let res = grpc.unary(method, req).await;
                        Ok(res)
                    };
                    Box::pin(fut)
                }
                "/oak.examples.hello_world.HelloWorld/LotsOfReplies" => {
                    struct LotsOfRepliesSvc<T: HelloWorld>(pub Arc<T>);
                    impl<T: HelloWorld> tonic::server::ServerStreamingService<super::HelloRequest>
                        for LotsOfRepliesSvc<T>
                    {
                        type Response = super::HelloResponse;
                        type ResponseStream = T::LotsOfRepliesStream;
                        type Future =
                            BoxFuture<tonic::Response<Self::ResponseStream>, tonic::Status>;
                        fn call(
                            &mut self,
                            request: tonic::Request<super::HelloRequest>,
                        ) -> Self::Future {
                            let inner = self.0.clone();
                            let fut = async move { inner.lots_of_replies(request).await };
                            Box::pin(fut)
                        }
                    }
                    let inner = self.inner.clone();
                    let fut = async move {
                        let interceptor = inner.1;
                        let inner = inner.0;
                        let method = LotsOfRepliesSvc(inner);
                        let codec = tonic::codec::ProstCodec::default();
                        let mut grpc = if let Some(interceptor) = interceptor {
                            tonic::server::Grpc::with_interceptor(codec, interceptor)
                        } else {
                            tonic::server::Grpc::new(codec)
                        };
                        let res = grpc.server_streaming(method, req).await;
                        Ok(res)
                    };
                    Box::pin(fut)
                }
                "/oak.examples.hello_world.HelloWorld/LotsOfGreetings" => {
                    struct LotsOfGreetingsSvc<T: HelloWorld>(pub Arc<T>);
                    impl<T: HelloWorld> tonic::server::ClientStreamingService<super::HelloRequest>
                        for LotsOfGreetingsSvc<T>
                    {
                        type Response = super::HelloResponse;
                        type Future = BoxFuture<tonic::Response<Self::Response>, tonic::Status>;
                        fn call(
                            &mut self,
                            request: tonic::Request<tonic::Streaming<super::HelloRequest>>,
                        ) -> Self::Future {
                            let inner = self.0.clone();
                            let fut = async move { inner.lots_of_greetings(request).await };
                            Box::pin(fut)
                        }
                    }
                    let inner = self.inner.clone();
                    let fut = async move {
                        let interceptor = inner.1;
                        let inner = inner.0;
                        let method = LotsOfGreetingsSvc(inner);
                        let codec = tonic::codec::ProstCodec::default();
                        let mut grpc = if let Some(interceptor) = interceptor {
                            tonic::server::Grpc::with_interceptor(codec, interceptor)
                        } else {
                            tonic::server::Grpc::new(codec)
                        };
                        let res = grpc.client_streaming(method, req).await;
                        Ok(res)
                    };
                    Box::pin(fut)
                }
                "/oak.examples.hello_world.HelloWorld/BidiHello" => {
                    struct BidiHelloSvc<T: HelloWorld>(pub Arc<T>);
                    impl<T: HelloWorld> tonic::server::StreamingService<super::HelloRequest> for BidiHelloSvc<T> {
                        type Response = super::HelloResponse;
                        type ResponseStream = T::BidiHelloStream;
                        type Future =
                            BoxFuture<tonic::Response<Self::ResponseStream>, tonic::Status>;
                        fn call(
                            &mut self,
                            request: tonic::Request<tonic::Streaming<super::HelloRequest>>,
                        ) -> Self::Future {
                            let inner = self.0.clone();
                            let fut = async move { inner.bidi_hello(request).await };
                            Box::pin(fut)
                        }
                    }
                    let inner = self.inner.clone();
                    let fut = async move {
                        let interceptor = inner.1;
                        let inner = inner.0;
                        let method = BidiHelloSvc(inner);
                        let codec = tonic::codec::ProstCodec::default();
                        let mut grpc = if let Some(interceptor) = interceptor {
                            tonic::server::Grpc::with_interceptor(codec, interceptor)
                        } else {
                            tonic::server::Grpc::new(codec)
                        };
                        let res = grpc.streaming(method, req).await;
                        Ok(res)
                    };
                    Box::pin(fut)
                }
                _ => Box::pin(async move {
                    Ok(http::Response::builder()
                        .status(200)
                        .header("grpc-status", "12")
                        .body(tonic::body::BoxBody::empty())
                        .unwrap())
                }),
            }
        }
    }
    impl<T: HelloWorld> Clone for HelloWorldServer<T> {
        fn clone(&self) -> Self {
            let inner = self.inner.clone();
            Self { inner }
        }
    }
    impl<T: HelloWorld> Clone for _Inner<T> {
        fn clone(&self) -> Self {
            Self(self.0.clone(), self.1.clone())
        }
    }
    impl<T: std::fmt::Debug> std::fmt::Debug for _Inner<T> {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{:?}", self.0)
        }
    }
    impl<T: HelloWorld> tonic::transport::NamedService for HelloWorldServer<T> {
        const NAME: &'static str = "oak.examples.hello_world.HelloWorld";
    }
}
