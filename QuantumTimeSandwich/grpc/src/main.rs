use tonic::{transport::Server, Request, Response, Status};
use oqs::kem::{Algorithm, Kem};

pub mod quantumtimesandwich {
    tonic::include_proto!("quantumtimesandwich");
}

use quantumtimesandwich::quantum_encryption_service_server::{QuantumEncryptionService, QuantumEncryptionServiceServer};
use quantumtimesandwich::{EncryptionRequest, EncryptionResponse, DecryptionRequest, DecryptionResponse, GenerateKeyRequest, GenerateKeyResponse};

#[derive(Default)]
pub struct MyQuantumEncryptionService {}

#[tonic::async_trait]
impl QuantumEncryptionService for MyQuantumEncryptionService {
    async fn encrypt_message(&self, request: Request<EncryptionRequest>) -> Result<Response<EncryptionResponse>, Status> {
        let message = request.into_inner().message;
        // Implement encryption logic here
        // Placeholder logic:
        let encrypted_message = format!("encrypted_{}", message);
        Ok(Response::new(EncryptionResponse { encrypted_message }))
    }

    async fn decrypt_message(&self, request: Request<DecryptionRequest>) -> Result<Response<DecryptionResponse>, Status> {
        let encrypted_message = request.into_inner().encrypted_message;
        // Implement decryption logic here
        // Placeholder logic:
        let message = format!("decrypted_{}", encrypted_message);
        Ok(Response::new(DecryptionResponse { message }))
    }

    async fn generate_key(&self, _request: Request<GenerateKeyRequest>) -> Result<Response<GenerateKeyResponse>, Status> {
        oqs::init(); // Initialize liboqs
    
        // Choose a KEM algorithm
        let kem = match Kem::new(Algorithm::Kyber512) {
            Ok(kem) => kem,
            Err(e) => return Err(Status::internal(format!("KEM initialization failed: {}", e))),
        };
    
        // Generate keypair
        let (public_key, _secret_key) = match kem.keypair() {
            Ok(keys) => keys,
            Err(e) => return Err(Status::internal(format!("Keypair generation failed: {}", e))),
        };
    
        // Convert public_key to a string representation
        let key = hex::encode(public_key);
    
        Ok(Response::new(GenerateKeyResponse { key }))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let addr = "0.0.0.0:50051".parse()?;
    let service = MyQuantumEncryptionService::default();

    println!("Starting gRPC server on {}", addr);
    Server::builder()
        .add_service(QuantumEncryptionServiceServer::new(service))
        .serve(addr)
        .await?;

    Ok(())
}
