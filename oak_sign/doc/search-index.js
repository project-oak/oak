var searchIndex = JSON.parse('{\
"oak_sign":{"doc":"","t":[17,3,17,17,17,3,11,11,11,11,11,11,11,11,11,5,11,5,11,11,11,11,11,11,11,11,11,5,5,12,11,11,11,11,11,12,5,11,12,11,11,11,11,11,11,11,11,11,11,5],"n":["HASH_TAG","KeyPair","PRIVATE_KEY_TAG","PUBLIC_KEY_TAG","SIGNATURE_TAG","SignatureBundle","borrow","borrow","borrow_mut","borrow_mut","clone","clone","clone_into","clone_into","create","decode_public_key_der","default","encode_public_key_der","eq","fmt","fmt","from","from","from","from_pem","from_pem_file","generate","get_sha256","get_sha256_hex","hash","into","into","key_pair_pkcs_8","parse","public_key_der","public_key_der","read_pem_file","sign","signed_hash","to_owned","to_owned","to_pem_file","try_from","try_from","try_into","try_into","type_id","type_id","verify","write_pem_file"],"q":["oak_sign","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","",""],"d":["","Convenience struct that encapsulates …","","","","","","","","","","","","","Signs a SHA-256 hash of the <code>input</code> using <code>private_key</code>.","Decodes the public key as a binary DER-encoded …","","Encodes the public key as a binary DER-encoded …","","","","","","","Parses public key, signature and SHA-256 hash encoded …","Parses public key, signature and SHA-256 hash encoded …","Generates a Ed25519 key pair.","Computes a SHA-256 digest of <code>input</code> and returns it in a …","Computes a SHA-256 digest of <code>bytes</code> and returns it in a …","","","","Returns a PKCS#8 v2 encoded key pair.","Parses a Ed25519 key pair from a PKCS#8 v2 encoded …","Returns the public key as a binary DER-encoded …","Public key as a binary DER-encoded <code>SubjectPublicKeyInfo</code> …","","","","","","","","","","","","","Verifies the signature validity.",""],"i":[0,0,0,0,0,0,1,2,1,2,1,2,1,2,2,0,2,0,1,1,2,1,2,2,2,2,1,0,0,2,1,2,1,1,1,2,0,1,2,1,2,2,1,2,1,2,1,2,2,0],"f":[null,null,null,null,null,null,[[]],[[]],[[]],[[]],[[]],[[],["signaturebundle",3]],[[]],[[]],[[["keypair",3]],[["signaturebundle",3],["result",6,["signaturebundle"]]]],[[],[["result",6,["vec"]],["vec",3,["u8"]]]],[[],["signaturebundle",3]],[[],[["result",6,["vec"]],["vec",3,["u8"]]]],[[],["bool",15]],[[["formatter",3]],["result",6]],[[["formatter",3]],["result",6]],[[]],[[]],[[["modulesignature",3]]],[[],[["signaturebundle",3],["result",6,["signaturebundle"]]]],[[["str",15]],[["signaturebundle",3],["result",6,["signaturebundle"]]]],[[],[["keypair",3],["result",6,["keypair"]]]],[[],[["vec",3,["u8"]],["u8",15]]],[[],["string",3]],null,[[]],[[]],[[],[["vec",3,["u8"]],["u8",15]]],[[],[["keypair",3],["result",6,["keypair"]]]],[[],[["result",6,["vec"]],["vec",3,["u8"]]]],null,[[["str",15]],[["result",6,["vec"]],["vec",3,["u8"]]]],[[],[["vec",3,["u8"]],["u8",15]]],null,[[]],[[]],[[["str",15]],["result",6]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["typeid",3]],[[],["typeid",3]],[[],["result",6]],[[["str",15]],["result",6]]],"p":[[3,"KeyPair"],[3,"SignatureBundle"]]},\
"oak_sign_bin":{"doc":"An utility binary to sign files using Ed25519. …","t":[4,3,13,3,3,13,3,13,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,12,11,11,11,11,11,11,11,11,11,11,12,12,11,11,11,11,11,5,12,12,12,12,12,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,11,12,12,12],"n":["Command","Generate","Generate","Opt","Sign","Sign","Verify","Verify","borrow","borrow","borrow","borrow","borrow","borrow_mut","borrow_mut","borrow_mut","borrow_mut","borrow_mut","clap","clap","clap","clap","clap","clone","clone","clone","clone","clone","clone_into","clone_into","clone_into","clone_into","clone_into","cmd","from","from","from","from","from","from_clap","from_clap","from_clap","from_clap","from_clap","input_file","input_string","into","into","into","into","into","main","private_key","private_key","public_key","signature_file","signature_file","to_owned","to_owned","to_owned","to_owned","to_owned","try_from","try_from","try_from","try_from","try_from","try_into","try_into","try_into","try_into","try_into","type_id","type_id","type_id","type_id","type_id","0","0","0"],"q":["oak_sign_bin","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","oak_sign_bin::Command","",""],"d":["Available commands for <code>oak_sign</code>.","","","Command line options for <code>oak_sign</code>.","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","","Main execution point for <code>oak_sign</code>.","","","","","","","","","","","","","","","","","","","","","","","","","","","",""],"i":[0,0,1,0,0,1,0,1,2,1,3,4,5,2,1,3,4,5,2,1,3,4,5,2,1,3,4,5,2,1,3,4,5,2,2,1,3,4,5,2,1,3,4,5,4,4,2,1,3,4,5,0,3,4,3,4,5,2,1,3,4,5,2,1,3,4,5,2,1,3,4,5,2,1,3,4,5,6,7,8],"f":[null,null,null,null,null,null,null,null,[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[]],[[],["app",3]],[[],["app",3]],[[],["app",3]],[[],["app",3]],[[],["app",3]],[[],["opt",3]],[[],["command",4]],[[],["generate",3]],[[],["sign",3]],[[],["verify",3]],[[]],[[]],[[]],[[]],[[]],null,[[]],[[]],[[]],[[]],[[]],[[["argmatches",3]]],[[["argmatches",3]]],[[["argmatches",3]]],[[["argmatches",3]]],[[["argmatches",3]]],null,null,[[]],[[]],[[]],[[]],[[]],[[],["result",6]],null,null,null,null,null,[[]],[[]],[[]],[[]],[[]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["result",4]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],[[],["typeid",3]],null,null,null],"p":[[4,"Command"],[3,"Opt"],[3,"Generate"],[3,"Sign"],[3,"Verify"],[13,"Generate"],[13,"Sign"],[13,"Verify"]]}\
}');
if (window.initSearch) {window.initSearch(searchIndex)};