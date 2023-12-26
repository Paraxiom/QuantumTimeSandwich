fn main() -> Result<(), Box<dyn std::error::Error>> {
    tonic_build::configure()
        .build_server(true) // Set to false if you don't need server code
        .build_client(true) // Set to false if you don't need client code
        .compile(&["proto/quantum_encryption_service.proto"], &["proto"])
        ?;
    Ok(())
}