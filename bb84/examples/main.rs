use bb84::bb84::{generate_bb84_state, measure_bb84_state};
use bb84::bb84_states::{random_bit, BB84State, MeasurementBasis};

fn main() {
    println!("--- BB84 Protocol Full Demonstration ---");

    // 1. Alice's Preparation
    let alice_bit = random_bit();
    let alice_basis = MeasurementBasis::random();

    println!("Alice's Secret Bit: {}", alice_bit);
    println!("Alice's Chosen Basis: {:?}", alice_basis);

    // 2. State Generation (Preparation of the Qubit)
    let alice_state = generate_bb84_state(alice_bit, alice_basis);

    // 3. Transmission (The "Sandwich" moment)
    // In a real scenario, noise or Eve would be here.
    let transmitted_state = alice_state;

    // 4. Bob's Measurement
    // Bob must choose his own basis randomly without knowing Alice's
    let bob_basis = MeasurementBasis::random();
    println!("Bob's Chosen Basis: {:?}", bob_basis);

    let bob_bit = measure_bb84_state(transmitted_state, bob_basis);
    println!("Bob's Measured Bit: {}", bob_bit);

    // 5. Sifting (Public Basis Comparison)
    println!("\n--- Sifting Process ---");
    if alice_basis == bob_basis {
        println!("Bases Match! Shared Key Bit: {}", alice_bit);
        if alice_bit == bob_bit {
            println!("✅ Successful key exchange!");
        } else {
            println!("❌ Key exchange failed due to noise.");
        }
    } else {
        println!("⚠️ Bases Mismatch. This bit is discarded.");
    }
}
