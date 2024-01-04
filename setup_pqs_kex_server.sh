#!/bin/bash

# Navigate to the QuantumTimeSandwich directory
cd "$(dirname "$0")/QuantumTimeSandwich"

# Create directories for the oqs_kex_rpc server
mkdir -p src/grpc/oqs_kex_rpc
mkdir -p src/grpc/oqs_kex_rpc/utils

# Create initial Rust files for the oqs_kex_rpc server module
touch src/grpc/oqs_kex_rpc/mod.rs
touch src/grpc/oqs_kex_rpc/server.rs
touch src/grpc/oqs_kex_rpc/utils/mod.rs

echo "oqs-kex-rpc server module structure created successfully in QuantumTimeSandwich."

