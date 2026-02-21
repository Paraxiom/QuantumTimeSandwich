use crate::bb84::prelude::CircuitError;
use crate::bb84_states::{random_bit, BB84State, MeasurementBasis};
use QuantumTimeSandwich::builder_traits::CircuitBuilder;
use QuantumTimeSandwich::builder_traits::CliffordTBuilder;
use QuantumTimeSandwich::builder_traits::MeasurementBuilder;
use QuantumTimeSandwich::prelude::LocalBuilder;
use QuantumTimeSandwich::*;

pub fn generate_bb84_state(bit: bool, basis: MeasurementBasis) -> BB84State {
    match basis {
        MeasurementBasis::Basis1 => {
            // Rectilinear basis (|0> and |1>)
            if bit {
                BB84State::QubitOne // Represents the |1> state
            } else {
                BB84State::QubitZero // Represents the |0> state
            }
        }
        MeasurementBasis::Basis2 => {
            // Diagonal basis (|+> and |->)
            if bit {
                BB84State::QubitPlus // Represents the |+> state
            } else {
                BB84State::QubitMinus // Represents the |-> state
            }
        }
    }
}

pub fn generate_bb84_state_with_basis(bit: bool, basis: MeasurementBasis) -> BB84State {
    match (bit, basis) {
        (false, MeasurementBasis::Basis1) => BB84State::QubitZero,
        (true, MeasurementBasis::Basis1) => BB84State::QubitOne,
        // Add specific logic for Basis2 or other bases if necessary
        (false, MeasurementBasis::Basis2) => BB84State::QubitZero, // Example logic
        (true, MeasurementBasis::Basis2) => BB84State::QubitOne,   // Example logic
                                                                    // You can add more cases or a default case here
    }
}

pub fn measure_bb84_state(state: BB84State, basis: MeasurementBasis) -> bool {
    match (state, basis) {
        (BB84State::QubitZero, MeasurementBasis::Basis1) => false,
        (BB84State::QubitOne, MeasurementBasis::Basis1) => true,
        (BB84State::QubitZero, MeasurementBasis::Basis2) => {
            // Probabilistic outcome for rectilinear basis states measured in diagonal basis
            rand::random()
        }
        (BB84State::QubitOne, MeasurementBasis::Basis2) => {
            // Probabilistic outcome for rectilinear basis states measured in diagonal basis
            rand::random()
        }
        (BB84State::QubitPlus, MeasurementBasis::Basis1) => {
            // Probabilistic outcome for diagonal basis states measured in rectilinear basis
            rand::random()
        }
        (BB84State::QubitMinus, MeasurementBasis::Basis1) => {
            // Probabilistic outcome for diagonal basis states measured in rectilinear basis
            rand::random()
        }
        (BB84State::QubitPlus, MeasurementBasis::Basis2) => true,
        (BB84State::QubitMinus, MeasurementBasis::Basis2) => false,
    }
}

pub fn flip_state(state: BB84State) -> BB84State {
    match state {
        BB84State::QubitZero => BB84State::QubitOne,
        BB84State::QubitOne => BB84State::QubitZero,
        BB84State::QubitPlus => BB84State::QubitMinus,
        BB84State::QubitMinus => BB84State::QubitPlus,
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
    let _alice_state = generate_bb84_state(random_bit(), MeasurementBasis::random());
    let bob_state = generate_bb84_state(random_bit(), MeasurementBasis::random());

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
