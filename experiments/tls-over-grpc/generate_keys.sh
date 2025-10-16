#!/bin/bash
OUTPUT_DIR=$1
openssl genpkey -algorithm RSA -out "$OUTPUT_DIR/server.key"
openssl req -new -x509 -key "$OUTPUT_DIR/server.key" -out "$OUTPUT_DIR/server.pem" -days 365 -subj "/CN=localhost"