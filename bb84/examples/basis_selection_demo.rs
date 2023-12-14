use bb84::bb84::{alice_step, bob_step, generate_bb84_state, measure_bb84_state};
use bb84::bb84_states::{random_bit, BB84State, MeasurementBasis};

fn basis_selection_demo() {
    println!("BB84 Basis Selection Demonstration");

    // Simulate Alice choosing a basis for a number of qubits
    let alice_bases: Vec<MeasurementBasis> = (0..10)
        .map(|_| {
            if random_bit() {
                MeasurementBasis::Basis1
            } else {
                MeasurementBasis::Basis2
            }
        })
        .collect();
    println!("Alice's bases: {:?}", alice_bases);

    // Simulate Bob choosing a basis for a number of qubits
    let bob_bases: Vec<MeasurementBasis> = (0..10)
        .map(|_| {
            if random_bit() {
                MeasurementBasis::Basis1
            } else {
                MeasurementBasis::Basis2
            }
        })
        .collect();
    println!("Bob's bases: {:?}", bob_bases);

    // Compare Alice's and Bob's bases
    let matching_bases_count = alice_bases
        .iter()
        .zip(bob_bases.iter())
        .filter(|&(a, b)| a == b)
        .count();

    println!("Number of matching bases: {}", matching_bases_count);
}

fn main() {
    basis_selection_demo();
}
