# Verification API

Verification produces a go/no-go decision based on three (complex) arguments:

1. **Evidence** is everything that is derived from the constellation, where a
constellation is a concrete instance of specific software running on specific
hardware. 
1. **Endorsements** are the assertions made by developers or manufacturers.
Any data that is unrelated to a particular constellation and is kept with
the server. 
1. **Reference Values** are passed by the client and pass in remaining
parameters such as public signing keys.
