initSidebarItems({"constant":[["MAXIMUM_MESSAGE_SIZE","Maximum handshake message size is set to be equal to 1KiB."],["PROTOCOL_VERSION","Remote attestation protocol version."],["REPLAY_PROTECTION_ARRAY_LENGTH","Length (in bytes) of the random vector sent in messages for preventing replay attacks."]],"enum":[["MessageWrapper","Convenience struct that wraps attestation messages."]],"fn":[["deserialize_message","Deserializes an attestation message from a serialized `input` and wraps in a [`MessageWrapper`]."]],"struct":[["ClientHello","Initial message that starts remote attestation handshake."],["ClientIdentity","Client identity message containing remote attestation information and a public key for Diffie-Hellman key negotiation."],["EncryptedData","Message containing data encrypted using a session key."],["ServerIdentity","Server identity message containing remote attestation information and a public key for Diffie-Hellman key negotiation."]],"trait":[["Deserializable",""],["Serializable",""]]});