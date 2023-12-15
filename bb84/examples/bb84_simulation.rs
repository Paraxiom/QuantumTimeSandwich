use rand::{thread_rng, Rng};
use QuantumTimeSandwich::prelude::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut rng = thread_rng();
    let n = 10; // Number of qubits

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

    // Print results
    println!("Alice's Bits: {:?}", alice_bits);
    println!("Alice's Bases: {:?}", alice_bases);
    println!("Bob's Bases: {:?}", bob_bases);
    println!("Alice's Measurements: {:?}", alice_results);
    println!("Bob's Measurements: {:?}", bob_results);

    Ok(())
}
