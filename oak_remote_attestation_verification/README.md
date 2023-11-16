# Verification API

Verification produces a go/no-go decision based on three (complex) arguments:

1. **Evidence** is everything that is derived from the enclave, which is a
   concrete instance of specific software running on specific hardware.
1. **Endorsements** are assertions coming from developers and manufacturers
   relating to parts of the soft- or hardware. Endorsements originate
   outside the enclave. They are kept with the server.
1. **Reference Values** are passed by the client and provide the remaining
   parameters such as public signing keys. They are known good values that
   are relied upon without proof during the verification.
