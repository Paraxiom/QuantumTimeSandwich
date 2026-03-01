use bb84::bb84::{generate_bb84_state, measure_bb84_state, simulate_eve_attack};
use bb84::bb84_states::{random_bit, MeasurementBasis};

fn main() {
    println!("--- BB84 Statistical Attack Analysis ---");

    let total_iterations = 1000;
    let mut matched_bases_count = 0;
    let mut error_count = 0;

    for _ in 0..total_iterations {
        let alice_bit = random_bit();
        let alice_basis = MeasurementBasis::random();
        let alice_state = generate_bb84_state(alice_bit, alice_basis);

        let state_after_eve = simulate_eve_attack(alice_state);

        let bob_basis = MeasurementBasis::random();
        let bob_bit = measure_bb84_state(state_after_eve, bob_basis);

        if alice_basis == bob_basis {
            matched_bases_count += 1;
            if alice_bit != bob_bit {
                error_count += 1;
            }
        }
    }

    let qber = (error_count as f64 / matched_bases_count as f64) * 100.0;
    println!("Total Trials: {}", total_iterations);
    println!("Bits where Bases Matched: {}", matched_bases_count);
    println!("Detected Bit Errors: {}", error_count);
    println!("Calculated QBER: {:.2}%", qber);

    if qber > 20.0 {
        println!("CONCLUSION: Heavy Eavesdropping Detected. Key discarded.");
    } else {
        println!("CONCLUSION: Secure Channel. Proceeding to Privacy Amplification.");
    }
}
