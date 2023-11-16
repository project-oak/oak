# Verification API

Verification produces a go/no-go decision based on three (complex) arguments:

1. **Evidence** is everything that is derived from the enclave, which is a
   a concrete instance of specific software running on specific hardware.
1. **Endorsements** are known good values and assertions coming from developers
   or manufacturers. Endorsements are not directly related to a particular
   enclave. They are kept with the server.
1. **Reference Values** are passed by the client and pass in remaining
   parameters such as public signing keys.
