// build.rs
fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_build::configure()
        .build_server(true) // Set to true to generate server code
        .build_client(true) // Set to true to generate client code
        .compile(
            &["proto/quantum_encryption_service.proto"], // Path to your .proto file
            &["proto"], // Directory where your .proto file is located
        )?;
    Ok(())
}
