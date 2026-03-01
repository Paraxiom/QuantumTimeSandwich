use crate::bb84_states::{random_bit, BB84State, MeasurementBasis};

pub fn generate_bb84_state(bit: bool, basis: MeasurementBasis) -> BB84State {
    match (bit, basis) {
        (false, MeasurementBasis::Basis1) => BB84State::QubitZero,
        (true, MeasurementBasis::Basis1) => BB84State::QubitOne,
        (false, MeasurementBasis::Basis2) => BB84State::QubitMinus,
        (true, MeasurementBasis::Basis2) => BB84State::QubitPlus,
    }
}

pub fn measure_bb84_state(state: BB84State, basis: MeasurementBasis) -> bool {
    match (state, basis) {
        (BB84State::QubitZero, MeasurementBasis::Basis1) => false,
        (BB84State::QubitOne, MeasurementBasis::Basis1) => true,
        (BB84State::QubitMinus, MeasurementBasis::Basis2) => false,
        (BB84State::QubitPlus, MeasurementBasis::Basis2) => true,
        _ => rand::random(),
    }
}

pub fn simulate_eve_attack(state: BB84State) -> BB84State {
    let eve_basis = MeasurementBasis::random();
    let intercepted_bit = measure_bb84_state(state, eve_basis);
    generate_bb84_state(intercepted_bit, eve_basis)
}

pub fn run_intercept_resend_round() {
    println!("--- BB84 Intercept-Resend Simulation ---");

    let alice_bit = random_bit();
    let alice_basis = MeasurementBasis::random();
    let alice_state = generate_bb84_state(alice_bit, alice_basis);
    println!("Alice bit: {alice_bit}, basis: {alice_basis:?}");

    let state_after_eve = simulate_eve_attack(alice_state);

    let bob_basis = MeasurementBasis::random();
    let bob_bit = measure_bb84_state(state_after_eve, bob_basis);
    println!("Bob basis: {bob_basis:?}, measured bit: {bob_bit}");

    if alice_basis == bob_basis {
        if alice_bit == bob_bit {
            println!("Sifting result: bases matched and bit matched.");
        } else {
            println!("Sifting result: bases matched but bit mismatched (possible Eve/noise).");
        }
    } else {
        println!("Sifting result: bases mismatched, bit discarded.");
    }
}
