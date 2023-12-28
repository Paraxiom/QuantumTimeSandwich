# QuantumTimeSandwich gRPC Server

## Description
The QuantumTimeSandwich gRPC Server is a cutting-edge server implementation designed for secure quantum-resistant cryptographic operations. Utilizing the Open Quantum Safe (OQS) library, it provides a robust platform for secure communications, leveraging post-quantum cryptographic algorithms.

## Features
- Quantum-resistant cryptographic protocols.
- Implementation of key quantum encryption and decryption services.
- Secure session management for quantum key distribution.
- Integration with Open Quantum Safe (OQS) for post-quantum security.

## Prerequisites
- Rust programming environment.
- Open Quantum Safe (OQS) library.
- Tonic gRPC framework for Rust.

## Installation
1. Clone the repository:

git clone https://github.com/Paraxiom/QuantumTimeSandwich
cd QuantumTimeSandwich



2. Install the required dependencies:
```
cargo build
```


## Usage
To start the QuantumTimeSandwich gRPC Server, run the following command:
```
cargo run --bin quantum_time_sandwich_server
```


This will start the server on the default configured port (e.g., `0.0.0.0:50051`).

## Configuration
- Edit the `config.toml` file to adjust server configurations such as port, logging, and specific quantum-safe settings.

## API Reference
- `EncryptMessage`: API for encrypting messages using quantum-safe algorithms.
- `DecryptMessage`: API for decrypting messages.
- `GenerateKey`: API for generating a secure quantum-resistant key.
- Additional APIs for managing quantum states and sessions.

## Contributing
Contributions to the QuantumTimeSandwich gRPC Server are welcome. Please ensure to follow the project's coding standards and submit pull requests for any new features or bug fixes.

## License
Specify the license under which the project is released (e.g., MIT, GPL-3.0).

## Contact
- Lead Developer: Sylvain Cormier   
- Email: sylvain@paraxiom.org
