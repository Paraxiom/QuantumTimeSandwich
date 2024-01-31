use crate::quantumtimesandwich::MeasureStateRequest;
use crate::quantumtimesandwich::MeasureStateResponse;
use crate::quantumtimesandwich::PrepareStateRequest;
use crate::quantumtimesandwich::PrepareStateResponse;
use crate::quantumtimesandwich::GetKeyResponse;
use crate::quantumtimesandwich::GetKeyRequest;

use bb84::bb84_states::random_bit;
use bb84::bb84_states::BB84State;
use bb84::bb84_states::MeasurementBasis;
use log::{debug, error, info, warn};
use oqs::kem::{Algorithm, Kem};
use quantumtimesandwich::quantum_encryption_service_server::{
    QuantumEncryptionService, QuantumEncryptionServiceServer,
};
use quantumtimesandwich::{
    DecryptionRequest, DecryptionResponse, EncryptionRequest, EncryptionResponse,
    GenerateKeyRequest, GenerateKeyResponse,
};
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::RwLock;
use tokio::sync::Mutex;
use tonic::Code;
use tonic::transport::{Server, Identity, ServerTlsConfig};
use tonic::{Request, Response, Status};


pub mod quantumtimesandwich {
    tonic::include_proto!("quantumtimesandwich");
}

// Assuming you have a struct to hold the sequence of qubits
#[derive(Debug, Clone)]
struct QuantumStates {
    states: Vec<BB84State>,
}

impl Default for QuantumStates {
    fn default() -> Self {
        QuantumStates::new(0) // Default to an empty state, or choose a suitable default size
    }
}

struct SessionData {
    alice_ready: bool,
    bob_ready: bool,
    key: Option<String>,
}
impl Default for SessionData {
    fn default() -> Self {
        SessionData {
            alice_ready: false,
            bob_ready: false,
            key: None,
        }
    }
}

#[derive(Default)]
pub struct MyQuantumEncryptionService {
    sessions: Arc<RwLock<HashMap<String, SessionData>>>,
    quantum_states: Arc<Mutex<QuantumStates>>,
}

impl QuantumStates {
    fn new(size: usize) -> Self {
        QuantumStates {
            states: vec![BB84State::default(); size],
        }
    }
}

impl MyQuantumEncryptionService {
    async fn generate_key_for_session(&self, session_id: String) -> Result<(), Status> {
        debug!("Generating key for session: {}", session_id);
        let mut sessions = self.sessions.write().unwrap();
        if let Some(session) = sessions.get_mut(&session_id) {
            if session.alice_ready && session.bob_ready {
                debug!("Both Alice and Bob are ready. Generating key.");
                let key = "example_generated_key".to_string();
                session.key = Some(key);
                Ok(())
            } else {
                error!("Session not found for measuring quantum state: {}", session_id);
                Err(Status::new(Code::Unavailable, "Both parties are not ready"))
            }
        } else {
            error!("Session not found: {}", session_id);
            Err(Status::new(Code::NotFound, "Session not found"))
        }
    }

    async fn get_key(&self, session_id: String) -> Result<String, Status> {
        let sessions = self.sessions.read().unwrap();
        if let Some(session) = sessions.get(&session_id) {
            if let Some(key) = &session.key {
                Ok(key.clone())
            } else {
                Err(Status::new(Code::Unavailable, "Key not ready"))
            }
        } else {
            Err(Status::new(Code::NotFound, "Session not found"))
        }
    }
}

#[tonic::async_trait]
impl QuantumEncryptionService for MyQuantumEncryptionService {
    async fn encrypt_message(
        &self,
        request: Request<EncryptionRequest>,
    ) -> Result<Response<EncryptionResponse>, Status> {
        let message = request.into_inner().message;
        println!("Encrypting message: {}", message);
        info!("Received encryption request: {}", message);
        println!("Received encryption request");
        // Implement encryption logic here
        let encrypted_message = format!("encrypted_{}", message);
        debug!("Encrypted message: {}", encrypted_message);
        Ok(Response::new(EncryptionResponse { encrypted_message }))
    }

    async fn decrypt_message(
        &self,
        request: Request<DecryptionRequest>,
    ) -> Result<Response<DecryptionResponse>, Status> {
        let encrypted_message = request.into_inner().encrypted_message;
        info!("Received decryption request: {}", encrypted_message);
        // Implement decryption logic here
        let message = format!("decrypted_{}", encrypted_message);
        debug!("Decrypted message: {}", message);
        Ok(Response::new(DecryptionResponse { message }))
    }

    async fn generate_key(
        &self,
        request: Request<GenerateKeyRequest>,
    ) -> Result<Response<GenerateKeyResponse>, Status> {
        let session_id = request.into_inner().session_id;
        debug!("Generating key for session: {}", session_id);
        let (alice_ready, bob_ready) = {
            let sessions = self.sessions.read().unwrap();
            if let Some(session) = sessions.get(&session_id) {
                (session.alice_ready, session.bob_ready)
            } else {
                return Err(Status::new(Code::NotFound, "Session not found"));
            }
        }; // Lock is dropped here

        if alice_ready && bob_ready {
            self.generate_key_for_session(session_id).await?;
            let key = "example_generated_key".to_string();
            Ok(Response::new(GenerateKeyResponse { key }))
        } else {
            Err(Status::internal(
                "Both parties are not ready for key generation",
            ))
        }
    }

    async fn prepare_quantum_state(
        &self,
        request: Request<PrepareStateRequest>,
    ) -> Result<Response<PrepareStateResponse>, Status> {
        // Extract both session_id and num_qubits in one operation
        let req_inner = request.into_inner();
        let session_id = req_inner.session_id;
        let num_qubits = req_inner.num_qubits;

        let bob_ready = {
            let mut sessions = self.sessions.write().unwrap();
            let session = sessions.entry(session_id.clone()).or_default();
            session.alice_ready = true;
            session.bob_ready
        }; // Lock is dropped here

        if bob_ready {
            self.generate_key_for_session(session_id).await?;
        }

        Ok(Response::new(PrepareStateResponse {
            message: "Quantum states prepared".to_string(),
        }))
    }

    async fn measure_quantum_state(
        &self,
        request: Request<MeasureStateRequest>,
    ) -> Result<Response<MeasureStateResponse>, Status> {
        let session_id = request.into_inner().session_id;
        debug!("Measuring quantum state for session: {}", session_id);
        let alice_ready = {
            let mut sessions = self.sessions.write().unwrap();
            if let Some(session) = sessions.get_mut(&session_id) {
                session.bob_ready = true;
                session.alice_ready
            } else {
                error!("Session not found for measuring quantum state: {}", session_id);
                return Err(Status::new(Code::NotFound, "Session not found"));
            }
        }; // Lock is dropped here

        if alice_ready {
            debug!("Alice is ready for session: {}", session_id);
            self.generate_key_for_session(session_id.clone()).await?;
            info!("Key generation initiated for measuring quantum state in session: {}", session_id);
        }

        Ok(Response::new(MeasureStateResponse {
            message: "Quantum states measured".to_string(),
        }))
    }
    
    
        async fn get_key(
            &self,
            request: tonic::Request<GetKeyRequest>,
        ) -> Result<tonic::Response<GetKeyResponse>, tonic::Status> {
            let session_id = request.into_inner().session_id;
    
            let sessions = self.sessions.read().unwrap();
            if let Some(session) = sessions.get(&session_id) {
                if let Some(key) = &session.key {
                    Ok(tonic::Response::new(GetKeyResponse { key: key.clone() }))
                } else {
                    Err(tonic::Status::new(tonic::Code::NotFound, "Key not found for session"))
                }
            } else {
                Err(tonic::Status::new(tonic::Code::NotFound, "Session not found"))
            }
        }
    
    
}


#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("Initializing the server...");
    
    env_logger::init(); // Initialize the logger
    let cert = tokio::fs::read("newserver.pem").await?;
    let key = tokio::fs::read("newserver.key").await?;
    println!("Certificates read successfully");

    
    let server_identity = tonic::transport::Identity::from_pem(&cert, &key);
    let tls_config = tonic::transport::ServerTlsConfig::new().identity(server_identity);
    println!("TLS configuration set");
    let service = MyQuantumEncryptionService::default();
let addr = "127.0.0.1:50052".parse()?;

println!("Starting gRPC server with TLS on {}", addr);

Server::builder()
    .tls_config(tls_config)?
    .add_service(QuantumEncryptionServiceServer::new(service))
    .serve(addr)
    .await?;
println!("Server shut down");
    Ok(())


}
