use bb84::bb84::{alice_step, bob_step, generate_bb84_state, measure_bb84_state};
use bb84::bb84_states::{random_bit, BB84State, MeasurementBasis};
use rand::Rng;

fn main() {
    println!("BB84 Protocol Full Demonstration");

    // Alice generates a quantum state and chooses a basis
    let alice_state = generate_bb84_state();
    let alice_basis = MeasurementBasis::random();

    // Alice performs her step of the protocol
    let (alice_bit, alice_chosen_basis) = match alice_step() {
        Ok(result) => result,
        Err(e) => {
            println!("Error in Alice's step: {:?}", e);
            return;
        }
    };

    // Simulate the transmission of the state to Bob
    // In a real scenario, this state might be affected by noise or eavesdropping
    let transmitted_state = alice_state;

    // Bob performs his step of the protocol
    let bob_bit = bob_step(transmitted_state, (alice_bit, alice_chosen_basis));

    // Compare the results
    if alice_chosen_basis == alice_basis && alice_bit == bob_bit {
        println!("Successful key exchange!");
    } else {
        println!("Key exchange failed.");
    }
}
