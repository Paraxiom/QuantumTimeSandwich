use bb84::bb84::flip_state;
use bb84::bb84::{alice_step, bob_step, generate_bb84_state, measure_bb84_state};
use bb84::bb84_states::{random_bit, BB84State, MeasurementBasis};
use rand::Rng;

fn simulate_noise_effect() {
    println!("BB84 Protocol with Noise Simulation");

    // Alice generates a quantum state and chooses a basis to send to Bob
    let alice_state = generate_bb84_state(random_bit(), MeasurementBasis::random());
    let alice_basis = MeasurementBasis::random();

    // Simulate noise affecting the state during transmission
    let mut rng = rand::thread_rng();
    let noise_probability = 0.2; // Assume 20% chance of noise
    let transmitted_state = if rng.gen::<f64>() < noise_probability {
        println!("Noise affected the state during transmission.");
        flip_state(alice_state) // Flip the state to simulate noise
    } else {
        alice_state
    };

    // Bob receives the state and measures it in the same basis as Alice
    let bob_measurement = measure_bb84_state(transmitted_state, alice_basis);
    println!(
        "Bob measures the qubit in {:?} basis. Measurement: {}",
        alice_basis, bob_measurement
    );

    // Determine if the measurement is successful (only when no noise affected the state)
    let successful_measurement = alice_state == transmitted_state && bob_measurement;

    println!("Successful measurement: {}", successful_measurement);
}

fn main() {
    simulate_noise_effect();
}
