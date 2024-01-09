use crate::quantumtimesandwich::GetKeyRequest;
use crate::quantumtimesandwich::GetKeyResponse;
use crate::quantumtimesandwich::MeasureStateRequest;
use crate::quantumtimesandwich::MeasureStateResponse;
use crate::quantumtimesandwich::PrepareStateRequest;
use crate::quantumtimesandwich::PrepareStateResponse;
use tokio::sync::oneshot;

use rand::Rng;

use tracing::{debug, error, info, warn};
use tracing_subscriber::fmt;
use tracing_subscriber::fmt::format::FmtSpan;

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
use tokio::sync::mpsc;
use tokio::sync::Mutex;
use tonic::Code;
use tonic::{transport::Server, Request, Response, Status};

use console_subscriber;
pub mod quantumtimesandwich {
    tonic::include_proto!("quantumtimesandwich");
}
pub fn measure_bb84_state(state: BB84State, basis: MeasurementBasis) -> bool {
    match (state, basis.clone()) {
        (BB84State::QubitZero, MeasurementBasis::Rectilinear) => false,
        (BB84State::QubitOne, MeasurementBasis::Rectilinear) => true,
        (BB84State::QubitZero, MeasurementBasis::Diagonal) => rand::random(),
        (BB84State::QubitOne, MeasurementBasis::Diagonal) => rand::random(),
        (BB84State::QubitPlus, MeasurementBasis::Rectilinear) => rand::random(),
        (BB84State::QubitMinus, MeasurementBasis::Rectilinear) => rand::random(),
        (BB84State::QubitPlus, MeasurementBasis::Diagonal) => true,
        (BB84State::QubitMinus, MeasurementBasis::Diagonal) => false,
        
        _ => panic!("Unexpected state and basis combination: {:?}, {:?}", state, basis.clone()),
    }
}


// Define the DeferredWriteOperation struct
struct DeferredWriteOperation {
    session_id: String,
    action: DeferredAction,
}

// Define the DeferredAction enum
enum DeferredAction {
    MarkBobReady,
    // Other actions as needed
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BB84State {
    QubitZero,
    QubitOne,
    QubitPlus,  // Represents the |+> state
    QubitMinus, // Represents the |-> state
}
impl Default for BB84State {
    fn default() -> Self {
        BB84State::QubitZero
    }
}

pub fn random_bit() -> bool {
    let mut rng = rand::thread_rng();
    rng.gen()
}

// Assuming you have a struct to hold the sequence of qubits
#[derive(Debug, Clone)]
struct QuantumStates {
    alice_states: Vec<BB84State>,
    bob_bases: Vec<MeasurementBasis>,
}

impl Default for QuantumStates {
    fn default() -> Self {
        QuantumStates::new(0) // Default to an empty state, or choose a suitable default size
    }
}
#[derive(Debug)]
struct SessionData {
    alice_ready: bool,
    bob_ready: bool,
    key: Option<String>,
    alice_bases: Vec<MeasurementBasis>, // Alice's chosen bases
    bob_bases: Vec<MeasurementBasis>,   // Bob's chosen bases
    alice_bits: Vec<u8>,
    bob_bits: Vec<u8>,                // Alice's encoded bits
    sifted_key: Vec<u8>,
    alice_states: Vec<BB84State>, 
}
impl Default for SessionData {
    fn default() -> Self {
        SessionData {
            alice_ready: false,
            bob_ready: false,
            key: None,
            alice_bases: Vec::new(),
            bob_bases: Vec::new(),
            alice_bits: Vec::new(),
            bob_bits: Vec::new(),
            sifted_key: Vec::new(),
            alice_states: Vec::new(),  // Initialize Alice's states as an empty vector
        }
    }
}

#[derive(Clone)]
pub struct MyQuantumEncryptionService {
    sender: mpsc::Sender<Command>,
}

#[tonic::async_trait]
impl quantumtimesandwich::quantum_encryption_service_server::QuantumEncryptionService
    for MyQuantumEncryptionService
{
    async fn generate_key(
        &self,
        request: Request<GenerateKeyRequest>,
    ) -> Result<Response<GenerateKeyResponse>, Status> {
        let session_id = request.into_inner().session_id;

        // Example: Send a command to the state manager to generate a key
        // and wait for the response
        // (In a real application, you would implement the actual logic here)

        let key = "example_generated_key".to_string(); // This should come from the state manager
        Ok(Response::new(GenerateKeyResponse { key }))
    }
    
    async fn encrypt_message(
        &self,
        request: Request<EncryptionRequest>,
    ) -> Result<Response<EncryptionResponse>, Status> {
        let message = request.into_inner().message;

        // Example: Simple "encryption" (prepend a string)
        let encrypted_message = format!("encrypted_{}", message);

        // Construct the response
        let response = EncryptionResponse { encrypted_message };

        // Return the response wrapped in a tonic::Response
        Ok(Response::new(response))
    }

    async fn decrypt_message(
        &self,
        request: Request<DecryptionRequest>,
    ) -> Result<Response<DecryptionResponse>, Status> {
        let encrypted_message = request.into_inner().encrypted_message;

        // Example: Simple "decryption" (remove a prefixed string)
        // In a real application, replace this with actual decryption logic.
        let decrypted_message = if encrypted_message.starts_with("encrypted_") {
            encrypted_message
                .trim_start_matches("encrypted_")
                .to_string()
        } else {
            return Err(Status::invalid_argument("Invalid encrypted message format"));
        };

        // Construct the response
        let response = DecryptionResponse {
            message: decrypted_message,
        };

        // Return the response wrapped in a tonic::Response
        Ok(Response::new(response))
    }
    async fn prepare_quantum_state(
        &self,
        request: Request<PrepareStateRequest>,
    ) -> Result<Response<PrepareStateResponse>, Status> {
        let req_inner = request.into_inner();
        let session_id = req_inner.session_id;
        let num_qubits = req_inner.num_qubits as usize; // Convert i32 to usize

        // Generate Alice's random qubits and bases
        let alice_qubits: Vec<u8> = (0..num_qubits).map(|_| random_bit() as u8).collect();
        let alice_bases: Vec<u8> = (0..num_qubits).map(|_| random_bit() as u8).collect();

        // Store the qubits and bases in the session state
        // Note: You'll need to implement the logic to access and modify the session state.
        self.store_alice_states(&session_id, &alice_qubits, &alice_bases)
            .await?;

        debug!(
            "Quantum state prepared for session {} with {} qubits",
            session_id, num_qubits
        );

        // Construct the response
        let response = PrepareStateResponse {
            message: format!("Quantum state prepared for session {}", session_id),
        };

        // Return the response wrapped in a tonic::Response
        Ok(Response::new(response))
    }
    // Helper function to store Alice's states in the session
    
    async fn measure_quantum_state(
        &self,
        request: Request<MeasureStateRequest>,
    ) -> Result<Response<MeasureStateResponse>, Status> {
        let session_id = request.into_inner().session_id;

        // Placeholder logic for measuring quantum state
        // In a real application, replace this with actual measurement logic
        debug!("Measuring quantum state for session {}", session_id);

        // Construct the response
        let response = MeasureStateResponse {
            message: format!("Quantum state measured for session {}", session_id),
        };

        // Return the response wrapped in a tonic::Response
        Ok(Response::new(response))
    }

    async fn get_key(
        &self,
        request: Request<GetKeyRequest>,
    ) -> Result<Response<GetKeyResponse>, Status> {
        let session_id = request.into_inner().session_id;

        // Placeholder logic for getting the key
        // In a real application, this should retrieve the key from your state manager or database
        debug!("Retrieving key for session {}", session_id);

        // Example: Let's assume we have a placeholder key for demonstration
        let key = "example_retrieved_key".to_string(); // This should be replaced with the actual key retrieval logic

        // Construct the response
        let response = GetKeyResponse { key };

        // Return the response wrapped in a tonic::Response
        Ok(Response::new(response))
    }
}

impl QuantumStates {
    fn new(size: usize) -> Self {
        QuantumStates {
            alice_states: vec![BB84State::default(); size], // Now this line will work
            bob_bases: vec![MeasurementBasis::default(); size], // Assuming MeasurementBasis also has Default implemented
        }
    }
}

enum Command {
    PrepareQuantumState {
        session_id: String,
        num_qubits: usize,
    },
    GenerateKey {
        session_id: String,
    },
    GetKey {
        session_id: String,
        response: oneshot::Sender<Option<String>>,
    },
    StoreAliceStates {
        session_id: String,
        qubits: Vec<u8>,
        bases: Vec<u8>,
    },
    StoreBobBases {
        session_id: String,
        bases: Vec<MeasurementBasis>,
    },
    SiftKey {
        session_id: String,
    },
    StoreAliceBases {
        session_id: String,
        bases: Vec<MeasurementBasis>,
    },
}

impl MyQuantumEncryptionService {
    // Function for Alice to send her bases to Bob
// Function for Alice to send her bases to Bob
async fn send_bases_to_bob(&self, session_id: &str, alice_bases: &[MeasurementBasis]) -> Result<(), Status> {
    // Simulate storing Alice's bases in a shared medium
    let command = Command::StoreAliceBases {
        session_id: session_id.to_string(),
        bases: alice_bases.to_vec(),
    };

    self.sender.send(command).await.map_err(|_| {
        Status::internal("Failed to send Alice's bases to Bob")
    })?;

    Ok(())
}
// Function for Bob to send his bases to Alice
async fn send_bases_to_alice(&self, session_id: &str, bob_bases: &[MeasurementBasis]) -> Result<(), Status> {
    // Simulate storing Bob's bases in a shared medium
    let command = Command::StoreBobBases {
        session_id: session_id.to_string(),
        bases: bob_bases.to_vec(),
    };

    self.sender.send(command).await.map_err(|_| {
        Status::internal("Failed to send Bob's bases to Alice")
    })?;

    Ok(())
}



async fn measure_and_choose_bases(&self, session_id: &str, alice_states: &[BB84State]) -> Result<(), Status> {
    let bob_bases: Vec<MeasurementBasis> = (0..alice_states.len())
        .map(|_| random_bit())
        .map(MeasurementBasis::from)
        .collect();

    let bob_measurements: Vec<u8> = alice_states
        .iter()
        .zip(&bob_bases)
        .map(|(state, basis)| measure_bb84_state(*state, *basis) as u8)
        .collect();

   Ok(())
}

    async fn receive_bob_bases(&self, session_id: &str, bob_bases: &[u8]) -> Result<(), Status> {
        // Convert bob_bases from &[u8] to Vec<MeasurementBasis>
        let bob_bases_vec: Vec<MeasurementBasis> = bob_bases.iter()
                                                           .map(|&b| b != 0)
                                                           .map(MeasurementBasis::from)
                                                           .collect();

        // Construct the command to store Bob's bases
        let command = Command::StoreBobBases {
            session_id: session_id.to_string(),
            bases: bob_bases_vec,
        };

        // Send the command to the state manager
        self.sender.send(command).await.map_err(|_| {
            Status::internal("Failed to send store Bob bases command to state manager")
        })?;

        Ok(())
    }

    async fn sift_key_for_session(&self, session_id: &str) -> Result<(), Status> {
        let mut session = self.get_session_data(session_id).await
            .ok_or_else(|| Status::not_found("Session data not found"))?;

        if session.alice_bases.is_empty() || session.bob_bases.is_empty() {
            return Err(Status::internal("Alice's or Bob's bases are missing"));
        }

        let sifted_key: Vec<u8> = session.alice_bits
            .iter()
            .zip(&session.bob_bases)
            .enumerate()
            .filter_map(|(index, (&alice_bit, bob_basis))| {
                if session.alice_bases[index] == *bob_basis {
                    Some(alice_bit)
                } else {
                    None
                }
            })
            .collect();

        // Update session data with the sifted key
        session.sifted_key = sifted_key;

        // Update session state
        self.update_session_state(session_id, session).await?;

        Ok(())
    }

    // ... other methods ...

    async fn get_session_data(&self, session_id: &str) -> Option<SessionData> {
        // Implementation to retrieve session data
        // ...
        Some(SessionData::default()) // Replace with your actual logic
    }

    // Helper method to update session state
    async fn update_session_state(&self, session_id: &str, updated_state: SessionData) -> Result<(), Status> {
        // Implementation to update session state
        // ...
        Ok(()) // Replace with your actual logic
    }
    
    async fn exchange_keys(&self, session_id: &str) -> Result<(), Status> {
        let session = self.get_session_data(session_id).await
            .ok_or_else(|| Status::not_found("Session data not found"))?;

        // Check if the key is ready for exchange
        if session.key.is_some() && !session.sifted_key.is_empty() {
            
            send_key_to_alice_and_bob(&session.sifted_key);

            // Update the session state to indicate that the key has been exchanged
            let updated_state = SessionData {
                alice_ready: true,  // Assuming Alice is now ready
                bob_ready: true,    // Assuming Bob is now ready
                key: session.key.clone(),
                alice_bases: session.alice_bases.clone(),
                bob_bases: session.bob_bases.clone(),
                alice_bits: session.alice_bits.clone(),
                bob_bits: session.bob_bits.clone(),
                sifted_key: session.sifted_key.clone(),
                alice_states: session.alice_states.clone(),
            };

            // Update the state manager with the new session data
            self.update_session_state(session_id, updated_state).await?;

            Ok(())
        } else {
            Err(Status::internal("Key not ready for exchange"))
        }
    }

    
  
    
    
   
    async fn generate_key_for_session(&self, session_id: String) -> Result<(), Status> {
        debug!("Attempting to generate key for session: {}", session_id);

        Ok(())
    }
    async fn store_alice_states(
        &self,
        session_id: &str,
        qubits: &[u8],
        bases: &[u8],
    ) -> Result<(), Status> {
        // Construct the command to be sent to the state manager
        let command = Command::StoreAliceStates {
            session_id: session_id.to_string(),
            qubits: qubits.to_vec(),
            bases: bases.to_vec(),
        };

        // Send the command
        self.sender.send(command).await.map_err(|_| {
            Status::internal("Failed to send store Alice states command to state manager")
        })?;

        Ok(())
    }
    // async fn get_key(&self, session_id: String) -> Result<String, Status> {

    // }
}






// You might also need to implement the actual key exchange logic.
// This is a placeholder function.
// Adjust send_key_to_alice_and_bob to accept Vec<u8> or convert Vec<u8> to a string
fn send_key_to_alice_and_bob(key: &[u8]) {
    // Convert Vec<u8> to a string or handle it as a byte array
    // Implement the logic here
}

// Enhance the sifting process
pub fn enhanced_sift_key(
    alice_bits: &[u8], 
    alice_bases: &[MeasurementBasis], 
    bob_bases: &[MeasurementBasis], 
    bob_bits: &[u8]
) -> Vec<u8> {
    alice_bits.iter()
        .zip(alice_bases.iter().zip(bob_bases.iter().zip(bob_bits)))
        .filter_map(|(&alice_bit, (alice_basis, (bob_basis, &bob_bit)))| {
            if alice_basis == bob_basis && alice_bit == bob_bit {
                Some(alice_bit)
            } else {
                None
            }
        })
        .collect()
}
async fn state_manager(mut receiver: mpsc::Receiver<Command>) {
    let mut state = HashMap::<String, SessionData>::new();

    while let Some(command) = receiver.recv().await {
        match command {
            // Modify the SiftKey command to use the enhanced sifting function
            Command::SiftKey { session_id } => {
                if let Some(session) = state.get_mut(&session_id) {
                    session.sifted_key = enhanced_sift_key(
                        &session.alice_bits, 
                        &session.alice_bases, 
                        &session.bob_bases, 
                        &session.bob_bits // Assuming bob_bits is defined and contains Bob's measured bits
                    );
                }
            },
            Command::PrepareQuantumState { session_id, num_qubits } => {
                // Prepare quantum states for Alice
                let quantum_states = QuantumStates::new(num_qubits);
                let mut session = state.entry(session_id.clone()).or_insert_with(SessionData::default);

                // Simulate the preparation of quantum states for Alice
                session.alice_states = quantum_states.alice_states;

                // Simulate the preparation of bases and bits for Alice
                session.alice_bases = (0..num_qubits)
                    .map(|_| random_bit())
                    .map(MeasurementBasis::from)
                    .collect();
                session.alice_bits = (0..num_qubits)
                    .map(|_| random_bit() as u8)
                    .collect();

                // Log the preparation
                debug!("Prepared quantum states for session {}: {:?}", session_id, session);

                // Additional logic for preparing the state (if necessary)
                // ...
            },
            Command::GenerateKey { session_id } => {
                // Logic for generating key
                let key = generate_random_key(); // Placeholder for key generation logic
                if let Some(session) = state.get_mut(&session_id) {
                    session.key = Some(key);
                }
            },
            Command::GetKey { session_id, response } => {
                let key = state.get(&session_id).and_then(|session| session.key.clone());
                let _ = response.send(key); // Send the response back
            },
            Command::StoreAliceStates { session_id, qubits, bases } => {
                if let Some(session) = state.get_mut(&session_id) {
                    session.alice_bits = qubits;
                    session.alice_bases = bases.iter()
                                               .map(|&b| b != 0) // Convert u8 to bool
                                               .map(MeasurementBasis::from)
                                               .collect();
                }
            },
            Command::StoreBobBases { session_id, bases } => {
                if let Some(session) = state.get_mut(&session_id) {
                    session.bob_bases = bases;
                }
            },
            Command::StoreAliceBases { session_id, bases } => {
                if let Some(session) = state.get_mut(&session_id) {
                    session.alice_bases = bases;
                }
            },
            Command::SiftKey { session_id } => {
                if let Some(session) = state.get_mut(&session_id) {
                    // Sifting logic here
                    session.sifted_key = sift_key(
                        &session.alice_bits, 
                        &session.alice_bases, 
                        &session.bob_bases,
                        &session.bob_bits // Add this line to supply the missing argument
                    );
                }
            },
            Command::SiftKey { session_id } => {
                if let Some(session) = state.get_mut(&session_id) {
                    // Enhance the sifting process to consider Bob's measurements
                    let sifted_key = sift_key(&session.alice_bits, &session.alice_bases, &session.bob_bases, &session.bob_bits);
                    session.sifted_key = sifted_key;
                }
            },
            
        }
    }
}

// Placeholder function for generating a random key
fn generate_random_key() -> String {
    // Implement key generation logic
    "random_key".to_string() // Replace with actual key generation
}

fn sift_key(alice_bits: &[u8], alice_bases: &[MeasurementBasis], bob_bases: &[MeasurementBasis], bob_bits: &[u8]) -> Vec<u8> {
    alice_bits.iter()
              .zip(alice_bases.iter().zip(bob_bases.iter().zip(bob_bits)))
              .filter_map(|(&alice_bit, (alice_basis, (bob_basis, &bob_bit)))| {
                  if alice_basis == bob_basis && alice_bit == bob_bit {
                      Some(alice_bit)
                  } else {
                      None
                  }
              })
              .collect()
}



#[derive(Debug, Clone, PartialEq, Copy)]
enum MeasurementBasis {
    Rectilinear, // often represented as |0⟩ and |1⟩
    Diagonal,    // often represented as |+⟩ and |−⟩
}

impl Default for MeasurementBasis {
    fn default() -> Self {
        MeasurementBasis::Rectilinear
    }
}

impl From<bool> for MeasurementBasis {
    fn from(bit: bool) -> Self {
        if bit {
            MeasurementBasis::Rectilinear // Replace with actual basis
        } else {
            MeasurementBasis::Diagonal // Replace with actual basis
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    fmt().with_span_events(FmtSpan::CLOSE).init();

    // Define the address for the gRPC server
    let addr = "0.0.0.0:50051".parse()?;

    let (sender, receiver) = mpsc::channel(32);
    let service = MyQuantumEncryptionService { sender };

    // Spawn the state manager task
    tokio::spawn(async move {
        state_manager(receiver).await;
    });

    println!("Starting gRPC server on {}", addr);
    info!("gRPC server starting on {}", addr);

    Server::builder()
        .add_service(QuantumEncryptionServiceServer::new(service))
        .serve(addr)
        .await?;

    Ok(())
}
