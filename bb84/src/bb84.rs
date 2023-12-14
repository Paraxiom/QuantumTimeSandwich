use crate::bb84::prelude::CircuitError;
use crate::bb84_states::{random_bit, BB84State, Basis, MeasurementBasis};
use QuantumTimeSandwich::builder_traits::CircuitBuilder;
use QuantumTimeSandwich::builder_traits::CliffordTBuilder;
use QuantumTimeSandwich::builder_traits::MeasurementBuilder;
use QuantumTimeSandwich::prelude::LocalBuilder;
use QuantumTimeSandwich::*;
use rand::Rng;

pub fn generate_bb84_state() -> BB84State {
    let _basis = Basis::random(); // Assuming Basis::random() is still relevant
    let value = random_bit(); // Assuming this returns a boolean

    // Decide which state to return based on the value of 'value'
    match value {
        false => BB84State::QubitZero,
        true => BB84State::QubitOne,
    }
}

pub fn measure_bb84_state(state: BB84State, basis: MeasurementBasis) -> bool {
    println!("Before measurement: State: {:?}, Basis: {:?}", state, basis);

    match basis {
        MeasurementBasis::Basis1 => {
            // In Basis1, we assume deterministic outcomes based on the state
            match state {
                BB84State::QubitZero => true,
                BB84State::QubitOne => false,
            }
        }
        MeasurementBasis::Basis2 => {
            // In Basis2, outcomes are probabilistic
            // Simulate this by randomly choosing a measurement outcome
            let mut rng = rand::thread_rng();
            rng.gen() // Randomly returns true or false
        }
    }
}

// This function simulates the effect of noise flipping the state.
pub fn flip_state(state: BB84State) -> BB84State {
    // Logic to flip the state. Assuming a simple binary flip for demonstration.
    match state {
        BB84State::QubitZero => BB84State::QubitOne,
        BB84State::QubitOne => BB84State::QubitZero,
    }
}

// Modify the alice_step to return both the bit and the basis.
pub fn alice_step() -> Result<(bool, MeasurementBasis), CircuitError> {
    let mut b = LocalBuilder::<f64>::default();
    let ra = b.qubit(); // Create a single qubit

    // Alice randomly chooses a basis and prepares her qubit accordingly
    let (ra, basis) = if random_bit() {
        // Apply Hadamard gate for Basis2
        (b.h(ra), MeasurementBasis::Basis2)
    } else {
        // No operation for Basis1
        (ra, MeasurementBasis::Basis1)
    };

    // Measurement
    let (_, handle) = b.measure(ra);

    // Run the circuit and get measurement results
    let (_, measures) = b.calculate_state();
    Ok((measures.get_measurement(handle).0 == 1, basis))
}

// Modify bob_step to take into account Alice's basis
pub fn bob_step(state: BB84State, alice_message: (bool, MeasurementBasis)) -> bool {
    let basis = alice_message.1; // Use the basis that Alice used

    // Bob measures his state in the chosen basis.
    let bit = measure_bb84_state(state, basis);

    // Bob returns the bit that he measured.
    return bit;
}

pub fn main() -> Result<(), CircuitError> {
    let alice_state = generate_bb84_state();
    let bob_state = generate_bb84_state();

    let alice_message = alice_step()?;
    let bob_message = bob_step(bob_state, alice_message);

    // Compare the messages to see if they match.
    if alice_message.0 == bob_message {
        println!("The BB84 protocol was successful!");
    } else {
        println!("The BB84 protocol failed!");
    }
    Ok(())
}
