use aes::Aes256;
use aes_gcm::aead::Aead;
use aes_gcm::KeyInit;
use aes_gcm::{Aes256Gcm, Key, Nonce};
use rand::RngCore;
use rand::{rngs::OsRng, Rng};
use sha2::{Digest, Sha256};
use QuantumTimeSandwich::prelude::*; // Import the hash function

fn main() -> Result<(), CircuitError> {
    let mut rng = OsRng;
    let mut b = LocalBuilder::<f64>::default();
    let num_bits = 16; // Use 16 qubits for the quantum key

    let mut key_measurements = Vec::with_capacity(num_bits);

    // Generate the quantum key
    for _ in 0..num_bits {
        let qubit = b.qubit(); // Create a qubit in |0> state
        let qubit = if rng.gen() {
            b.h(qubit) // Apply Hadamard to get |+> state
        } else {
            qubit
        };
        let (_, m) = b.measure(qubit); // Measure the qubit
        key_measurements.push(m);
    }

    // Run the circuit and get the measurement results
    let (_, measured) = b.calculate_state();
    let key_bits: Vec<bool> = key_measurements
        .into_iter()
        .map(|m| measured.get_measurement(m).0 == 1)
        .collect();

    // Convert the bits to bytes for the AES key
    let quantum_key_bytes = bits_to_bytes(&key_bits);

    // Use a hash function for key stretching to get a 256-bit key
    let mut hasher = Sha256::new();
    hasher.update(&quantum_key_bytes);
    let stretched_key_bytes = hasher.finalize().to_vec();

    // Use the stretched key for AES-GCM
    let aes_key = Key::<Aes256>::from_slice(&stretched_key_bytes);

    // Setup nonce for AES-GCM
    let mut nonce = [0u8; 12];
    rng.fill_bytes(&mut nonce);
    let nonce = Nonce::from_slice(&nonce);

    // Initialize AES-GCM cipher
    let cipher = Aes256Gcm::new(aes_key);

    // Encrypt a message
    let message = b"Your secret message";
    let encrypted_message = cipher
        .encrypt(nonce, message.as_ref())
        .expect("encryption failure");

    // Decrypt the message
    let decrypted_message = cipher
        .decrypt(nonce, encrypted_message.as_ref())
        .expect("decryption failure");

    // Compare and validate the original and decrypted message
    assert_eq!(message, &decrypted_message[..]);
    println!("Success! The message was correctly encrypted and decrypted using a quantum key.");

    Ok(())
}

fn bits_to_bytes(bits: &[bool]) -> Vec<u8> {
    let mut bytes = vec![0u8; (bits.len() + 7) / 8]; // Ensure rounding up if not a multiple of 8
    for (index, bit) in bits.iter().enumerate() {
        if *bit {
            bytes[index / 8] |= 1 << (7 - index % 8);
        }
    }
    bytes
}
