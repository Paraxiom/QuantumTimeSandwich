use bb84::bb84::{alice_step, bob_step, generate_bb84_state, measure_bb84_state};
use bb84::bb84_states::{random_bit, BB84State, MeasurementBasis};

fn simulate_eavesdropping() {
    println!("BB84 Eavesdropping Simulation");

    // Alice generates a quantum state and chooses a basis to send to Bob
    let alice_state = generate_bb84_state(random_bit(), MeasurementBasis::random());
    let alice_basis = MeasurementBasis::random();

    // Eavesdropper (Eve) intercepts and measures the quantum state
    let eve_basis = MeasurementBasis::random(); // Eve randomly chooses a basis
    let eve_measurement = measure_bb84_state(alice_state, eve_basis);
    println!(
        "Eve intercepts and measures the qubit in {:?} basis. Measurement: {}",
        eve_basis, eve_measurement
    );

    // Eve sends the measured state to Bob
    let eve_state = match eve_measurement {
        true => BB84State::QubitOne, // Assuming Eve sends QubitOne for measurement true
        false => BB84State::QubitZero, // Assuming Eve sends QubitZero for measurement false
    };

    // Bob measures the state sent by Eve
    let bob_measurement = measure_bb84_state(eve_state, alice_basis);
    println!(
        "Bob measures the qubit in {:?} basis. Measurement: {}",
        alice_basis, bob_measurement
    );

    // Determine if eavesdropping is detected
    let eavesdropping_detected = alice_basis == eve_basis && eve_measurement != bob_measurement;
    println!("Eavesdropping detected: {}", eavesdropping_detected);
}

fn main() {
    simulate_eavesdropping();
}
