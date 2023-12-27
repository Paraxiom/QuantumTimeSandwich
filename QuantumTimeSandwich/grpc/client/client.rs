use log::{error, info};
use quantumtimesandwich::quantum_encryption_service_client::QuantumEncryptionServiceClient;
use quantumtimesandwich::{DecryptionRequest, EncryptionRequest};
pub mod quantumtimesandwich {
    tonic::include_proto!("quantumtimesandwich");
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut client = QuantumEncryptionServiceClient::connect("http://127.0.0.1:50051").await?;

    // Encrypt a message
    let request = tonic::Request::new(EncryptionRequest {
        message: "Hello, QuantumTimeSandwich!".into(),
    });
    let response = client.encrypt_message(request).await?;
    println!(
        "Encrypted Message: {:?}",
        response.into_inner().encrypted_message
    );

    // Decrypt a message
    let request = tonic::Request::new(DecryptionRequest {
        encrypted_message: "encrypted_data".into(), // Replace with actual encrypted data.
    });
    let response = client.decrypt_message(request).await?;
    println!("Decrypted Message: {:?}", response.into_inner().message);

    Ok(())
}
