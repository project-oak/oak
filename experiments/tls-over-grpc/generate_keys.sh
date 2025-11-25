#!/bin/bash
OUTPUT_DIR=$1
openssl genpkey -algorithm RSA -out "$OUTPUT_DIR/server.key"
openssl req -new -x509 -key "$OUTPUT_DIR/server.key" -out "$OUTPUT_DIR/server.pem" -days 365 -subj "/CN=localhost"

openssl genpkey -algorithm RSA -out "$OUTPUT_DIR/client.key"
openssl req -new -x509 -key "$OUTPUT_DIR/client.key" -out "$OUTPUT_DIR/client.pem" -days 365 -subj "/CN=localhost"
