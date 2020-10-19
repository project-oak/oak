var searchIndex = JSON.parse('{\
"oak_loader":{"doc":"A utility binary to run Oak Runtime.","i":[[5,"main","oak_loader","Main execution point for the Oak loader.",null,[[],["result",6]]],[0,"options","","Helper functions to parse input arguments and create an…",null,null],[3,"Opt","oak_loader::options","Command line options for the Oak loader.",null,null],[12,"application","","",0,null],[12,"grpc_tls_private_key","","",0,null],[12,"grpc_tls_certificate","","",0,null],[12,"root_tls_certificate","","",0,null],[12,"signatures_manifest","","",0,null],[12,"oidc_client","","",0,null],[12,"http_tls_private_key","","",0,null],[12,"http_tls_certificate","","",0,null],[12,"metrics_port","","",0,null],[12,"no_metrics","","",0,null],[12,"introspect_port","","",0,null],[12,"no_introspect","","",0,null],[12,"config_files","","",0,null],[3,"SignatureManifest","","",null,null],[12,"signatures","","",1,null],[3,"ConfigEntry","","A specification of a configuration entry as human readable…",null,null],[12,"key","","",2,null],[12,"filename","","",2,null],[4,"SignatureLocation","","",null,null],[13,"Path","","",3,null],[13,"Url","","",3,null],[5,"create_runtime_config","","Parse input options and create a `RuntimeConfiguration`.",null,[[],[["result",6],["runtimeconfiguration",3]]]],[5,"parse_config_map","","Parse a collection of configuration entries and return the…",null,[[],[["result",6],["configmap",3]]]],[5,"create_secure_server_config","","Create [`oak_runtime::SecureServerConfiguration`]…",null,[[["opt",3]],[["result",6],["secureserverconfiguration",3]]]],[5,"create_grpc_config","","Create the overall [`oak_runtime::GrpcConfiguration`] from…",null,[[["opt",3]],[["result",6],["grpcconfiguration",3]]]],[5,"create_sign_table","","Create a signature table for Oak runtime. Returns an…",null,[[["opt",3]],[["signaturetable",3],["result",6]]]],[5,"create_http_config","","Create the overall [`oak_runtime::HttpConfiguration`] from…",null,[[["opt",3]],[["httpconfiguration",3],["result",6]]]],[5,"get_root_tls_certificate_or_default","","If `oak_debug` is enabled, read root TLS certificate from…",null,[[["opt",3]],[["result",6],["string",3]]]],[5,"get_oidc_client_info","","Parse OpenID Connect client configuration file into a…",null,[[["opt",3]],[["result",6],["option",4]]]],[5,"get_default_root_tls_certs","","Gets the default root TLS certificates from the embedded…",null,[[],[["result",6],["string",3]]]],[5,"create_app_config","","Parse application configuration into an instance of…",null,[[["opt",3]],[["result",6],["applicationconfiguration",3]]]],[11,"from","","",0,[[]]],[11,"into","","",0,[[]]],[11,"to_owned","","",0,[[]]],[11,"clone_into","","",0,[[]]],[11,"borrow","","",0,[[]]],[11,"borrow_mut","","",0,[[]]],[11,"try_from","","",0,[[],["result",4]]],[11,"try_into","","",0,[[],["result",4]]],[11,"type_id","","",0,[[],["typeid",3]]],[11,"vzip","","",0,[[]]],[11,"into_request","","",0,[[],["request",3]]],[11,"from","","",1,[[]]],[11,"into","","",1,[[]]],[11,"borrow","","",1,[[]]],[11,"borrow_mut","","",1,[[]]],[11,"try_from","","",1,[[],["result",4]]],[11,"try_into","","",1,[[],["result",4]]],[11,"type_id","","",1,[[],["typeid",3]]],[11,"vzip","","",1,[[]]],[11,"into_request","","",1,[[],["request",3]]],[11,"from","","",2,[[]]],[11,"into","","",2,[[]]],[11,"to_owned","","",2,[[]]],[11,"clone_into","","",2,[[]]],[11,"borrow","","",2,[[]]],[11,"borrow_mut","","",2,[[]]],[11,"try_from","","",2,[[],["result",4]]],[11,"try_into","","",2,[[],["result",4]]],[11,"type_id","","",2,[[],["typeid",3]]],[11,"vzip","","",2,[[]]],[11,"into_request","","",2,[[],["request",3]]],[11,"equivalent","","",2,[[]]],[11,"from","","",3,[[]]],[11,"into","","",3,[[]]],[11,"borrow","","",3,[[]]],[11,"borrow_mut","","",3,[[]]],[11,"try_from","","",3,[[],["result",4]]],[11,"try_into","","",3,[[],["result",4]]],[11,"type_id","","",3,[[],["typeid",3]]],[11,"vzip","","",3,[[]]],[11,"into_request","","",3,[[],["request",3]]],[11,"clone","","",0,[[],["opt",3]]],[11,"clone","","",2,[[],["configentry",3]]],[11,"eq","","",2,[[["configentry",3]]]],[11,"ne","","",2,[[["configentry",3]]]],[11,"fmt","","",0,[[["formatter",3]],["result",6]]],[11,"fmt","","",1,[[["formatter",3]],["result",6]]],[11,"fmt","","",3,[[["formatter",3]],["result",6]]],[11,"fmt","","",2,[[["formatter",3]],["result",6]]],[11,"from_str","","",2,[[],["result",4]]],[11,"deserialize","","",1,[[],["result",4]]],[11,"deserialize","","",3,[[],["result",4]]],[11,"clap","","",0,[[],["app",3]]],[11,"from_clap","","",0,[[["argmatches",3]]]],[11,"augment_clap","","",0,[[["app",3]],["app",3]]],[11,"is_subcommand","","",0,[[]]]],"p":[[3,"Opt"],[3,"SignatureManifest"],[3,"ConfigEntry"],[4,"SignatureLocation"]]}\
}');
addSearchOptions(searchIndex);initSearch(searchIndex);