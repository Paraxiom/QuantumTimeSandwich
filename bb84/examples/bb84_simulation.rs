use bb84::error_correction;
use bb84::privacy_amplification;
use rand::{thread_rng, Rng};
use QuantumTimeSandwich::prelude::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut rng = thread_rng();
    let n = 5; // Adjusted number of qubits

    // Initialize the circuit builder
    let mut b = LocalBuilder::<f64>::default();

    // Generate random bits and bases for Alice and Bob
    let alice_bits: Vec<bool> = (0..n).map(|_| rng.gen()).collect();
    let alice_bases: Vec<bool> = (0..n).map(|_| rng.gen()).collect();
    let bob_bases: Vec<bool> = (0..n).map(|_| rng.gen()).collect();

    // Prepare vectors to store qubit states and measurement handles
    let mut alice_qubits = Vec::new();
    let mut bob_qubits = Vec::new();

    // Apply operations and measure for each qubit
    for i in 0..n {
        // Alice's operations
        let alice_qubit = b.qubit();
        let alice_qubit = if alice_bases[i] {
            b.h(alice_qubit)
        } else {
            alice_qubit
        };
        let (alice_qubit, alice_m) = b.measure(alice_qubit);
        alice_qubits.push((alice_qubit, alice_m));

        // Bob's operations
        let bob_qubit = b.qubit();
        let bob_qubit = if bob_bases[i] {
            b.h(bob_qubit)
        } else {
            bob_qubit
        };
        let (bob_qubit, bob_m) = b.measure(bob_qubit);
        bob_qubits.push((bob_qubit, bob_m));
    }

    // Run the circuit
    let (_, measured) = b.calculate_state();

    // Process results
    let alice_results: Vec<bool> = alice_qubits
        .iter()
        .map(|(_, m)| measured.get_measurement(*m).0 == 1)
        .collect();
    let bob_results: Vec<bool> = bob_qubits
        .iter()
        .map(|(_, m)| measured.get_measurement(*m).0 == 1)
        .collect();

    // Print initial results
    println!("Alice's Bits: {:?}", alice_bits);
    println!("Alice's Bases: {:?}", alice_bases);
    println!("Bob's Bases: {:?}", bob_bases);
    println!("Alice's Measurements: {:?}", alice_results);
    println!("Bob's Measurements: {:?}", bob_results);

    // Sifting the Key
    let (sifted_alice_bits, sifted_bob_bits) =
        sift_keys(&alice_bases, &bob_bases, &alice_results, &bob_results);

    // Error Correction (Pseudo-code)
    let corrected_bob_bits = error_correction(sifted_alice_bits.clone(), sifted_bob_bits.clone());

    // Privacy Amplification (Pseudo-code)
    let final_alice_key = apply_privacy_amplification(sifted_alice_bits.clone());
    let final_bob_key = apply_privacy_amplification(corrected_bob_bits);

    // Print final results
    println!("Final Alice's Key: {:?}", final_alice_key);
    println!("Final Bob's Key: {:?}", final_bob_key);

    // Test the sifting process
    test_sifting_key(&alice_bases, &bob_bases, &alice_results, &bob_results);

    // Test error correction
    test_error_correction(&sifted_alice_bits, &sifted_bob_bits);

    // Test privacy amplification
    test_privacy_amplification(&final_alice_key, &final_bob_key);

    Ok(())
}

fn sift_keys(
    alice_bases: &[bool],
    bob_bases: &[bool],
    alice_results: &[bool],
    bob_results: &[bool],
) -> (Vec<bool>, Vec<bool>) {
    let mut sifted_alice_bits = Vec::new();
    let mut sifted_bob_bits = Vec::new();
    for i in 0..alice_bases.len() {
        if alice_bases[i] == bob_bases[i] {
            sifted_alice_bits.push(alice_results[i]);
            sifted_bob_bits.push(bob_results[i]);
        }
    }
    (sifted_alice_bits, sifted_bob_bits)
}

fn error_correction(alice_bits: Vec<bool>, bob_bits: Vec<bool>) -> Vec<bool> {
    bb84::error_correction::cascade_correction(alice_bits, bob_bits)
}

// Implement the apply_privacy_amplification function
fn apply_privacy_amplification(key: Vec<bool>) -> Vec<bool> {
    bb84::privacy_amplification::apply_privacy_amplification(key)
}

fn test_sifting_key(
    alice_bases: &[bool],
    bob_bases: &[bool],
    alice_bits: &[bool],
    bob_results: &[bool],
) {
    let mut sifted_alice_bits = Vec::new();
    let mut sifted_bob_bits = Vec::new();
    for i in 0..alice_bases.len() {
        if alice_bases[i] == bob_bases[i] {
            sifted_alice_bits.push(alice_bits[i]);
            sifted_bob_bits.push(bob_results[i]);
            println!(
                "Sifted Pair - Alice: {}, Bob: {}",
                alice_bits[i], bob_results[i]
            ); // Debug output
        }
    }
    println!("Sifted Alice Bits: {:?}", sifted_alice_bits); // Debug output
    println!("Sifted Bob Bits: {:?}", sifted_bob_bits); // Debug output
    assert_eq!(
        sifted_alice_bits, sifted_bob_bits,
        "Sifted keys do not match"
    );
}

fn test_error_correction(sifted_alice_bits: &[bool], sifted_bob_bits: &[bool]) {
    let corrected_bob_bits = error_correction(sifted_alice_bits.to_vec(), sifted_bob_bits.to_vec());
    assert_eq!(
        sifted_alice_bits,
        corrected_bob_bits.as_slice(),
        "Error correction failed"
    );
}

fn test_privacy_amplification(alice_key: &[bool], bob_key: &[bool]) {
    let amplified_alice_key = apply_privacy_amplification(alice_key.to_vec());
    let amplified_bob_key = apply_privacy_amplification(bob_key.to_vec());
    assert_eq!(
        amplified_alice_key, amplified_bob_key,
        "Keys do not match after privacy amplification"
    );
}
