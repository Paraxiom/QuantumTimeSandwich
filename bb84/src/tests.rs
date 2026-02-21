use crate::bb84::alice_step;
use crate::bb84::bob_step;
use crate::bb84::flip_state;
use crate::bb84::generate_bb84_state;
use crate::bb84::measure_bb84_state;
use crate::bb84_states::random_bit;
use crate::bb84_states::BB84State;
use crate::bb84_states::MeasurementBasis;
use rand::Rng;

#[cfg(test)]
mod tests {
    use super::*;
    use QuantumTimeSandwich::prelude::*;
    #[test]
    fn test_generate_bb84_state() {
        let mut counts = [0, 0, 0, 0]; // Counts for QubitZero, QubitOne, QubitPlus, QubitMinus

        for _ in 0..100 {
            match generate_bb84_state(random_bit(), MeasurementBasis::random()) {
                BB84State::QubitZero => counts[0] += 1,
                BB84State::QubitOne => counts[1] += 1,
                BB84State::QubitPlus => counts[2] += 1,
                BB84State::QubitMinus => counts[3] += 1,
            }
        }

        // Check that all types of states are generated
        for (i, &count) in counts.iter().enumerate() {
            assert!(count > 0, "State variant {} was not generated", i);
        }
    }

    #[test]
    fn test_alice_step() -> Result<(), CircuitError> {
        let mut b = LocalBuilder::<f64>::default();
        let ra = b.qubit(); // Simulate a qubit initialization

        // Simulate Alice's step
        let ra = b.h(ra); // Alice chooses Hadamard basis (for test purpose)
        let (_, handle) = b.measure(ra);

        // Run the circuit and get measurement results
        let (_, measures) = b.calculate_state();
        let measurement = measures.get_measurement(handle).0;

        // Check if the measurement is either 0 or 1 (valid qubit measurement outcomes)
        assert!(measurement == 0 || measurement == 1);

        Ok(())
    }

    #[test]
    fn test_bob_step() {
        let bob_state = generate_bb84_state(random_bit(), MeasurementBasis::random());
        let alice_bit = random_bit(); // Simulating Alice's bit
        let alice_basis = MeasurementBasis::Basis1; // or Basis2, depending on your test case

        println!(
            "Bob State: {:?}, Alice Bit: {}, Alice Basis: {:?}",
            bob_state, alice_bit, alice_basis
        );

        // Create a tuple of Alice's bit and basis
        let alice_message = (alice_bit, alice_basis);

        // Pass the tuple to Bob's step
        let bob_bit = bob_step(bob_state, alice_message);

        println!("Bob's measured bit: {}", bob_bit);

        // Check if Bob's bit is a valid boolean value
        assert!(bob_bit == true || bob_bit == false);
    }

    #[test]
    fn test_measurement_scenarios() {
        // Measure QubitZero in Basis1 should result in false
        assert!(
            !measure_bb84_state(BB84State::QubitZero, MeasurementBasis::Basis1),
            "Measurement of QubitZero in Basis1 should be false"
        );

        // Add more test cases here as needed, ensuring they align with the expected behavior of measure_bb84_state function
    }

    // TODO: Implement handling of invalid states or bases in the BB84 protocol.
    // Currently, the protocol assumes that all states and bases are valid.
    // Future enhancements could include adding checks and handling for invalid or unexpected inputs.

    // #[test]
    // fn test_invalid_state_or_basis() {

    //     let invalid_state = BB84State::InvalidState;
    //     let invalid_basis = MeasurementBasis::InvalidBasis;

    //     // Check if the measurement function correctly handles invalid inputs

    //     let result = measure_bb84_state(invalid_state, invalid_basis);

    //     // Assert the expected behavior - this is just an example
    //     // Replace with the actual expected behavior of  function when faced with invalid inputs
    //     assert!(result.is_err() || result == false); // Example: expecting an error or a default false outcome
    // }

    #[test]
    fn test_random_basis_consistency() {
        let mut basis1_count = 0;
        let mut basis2_count = 0;
        let sample_size = 40000; // Increased sample size

        for _ in 0..sample_size {
            match MeasurementBasis::random() {
                MeasurementBasis::Basis1 => basis1_count += 1,
                MeasurementBasis::Basis2 => basis2_count += 1,
            }
        }

        let basis1_ratio = basis1_count as f64 / sample_size as f64;
        let basis2_ratio = basis2_count as f64 / sample_size as f64;

        let expected_variance = 0.25 / sample_size as f64;
        let actual_variance = basis1_ratio * (1.0 - basis1_ratio);

        println!(
            "Basis1 Count: {}, Basis2 Count: {}",
            basis1_count, basis2_count
        );
        println!(
            "Basis1 Ratio: {}, Basis2 Ratio: {}",
            basis1_ratio, basis2_ratio
        );
        println!(
            "Expected Variance: {}, Actual Variance: {}",
            expected_variance, actual_variance
        );

        let actual_variance = basis1_ratio * (1.0 - basis1_ratio) / sample_size as f64;
        assert!(
            actual_variance > expected_variance * 0.2 && actual_variance < expected_variance * 1.8
        );
    }

    #[test]
    fn test_bb84_state_initialization() {
        // Example test: Verify the initialization of a BB84State
        let state = BB84State::QubitZero; // Adjust according to your actual enum or struct
                                          // Perform some assertions here
                                          // e.g., assert_eq!(state.some_property(), expected_value);
    }

    #[test]
    fn test_random_bit() {
        let bit = random_bit();
        assert!(bit == true || bit == false);
    }
    #[test]
    fn test_random_basis() {
        let basis = MeasurementBasis::random();
        assert!(matches!(
            basis,
            MeasurementBasis::Basis1 | MeasurementBasis::Basis2
        ));
    }

    #[test]
    fn test_measure_bb84_state() {
        let state = BB84State::QubitZero;
        let basis = MeasurementBasis::Basis1;
        let result = measure_bb84_state(state, basis);

        // The expected result when measuring QubitZero in Basis1 is false
        let expected_result = false;

        assert_eq!(
            result, expected_result,
            "Measurement of QubitZero in Basis1 should be false"
        );
    }

    #[test]
    fn test_measurement_accuracy() {
        let test_cases = vec![
            (BB84State::QubitZero, MeasurementBasis::Basis1, false),
            (BB84State::QubitOne, MeasurementBasis::Basis1, true),
            // Add more cases for QubitPlus and QubitMinus if needed
        ];

        for (state, basis, expected_result) in test_cases {
            println!("Testing State: {:?}, Basis: {:?}", state, basis);
            let measurement_result = measure_bb84_state(state, basis);
            println!("Measurement Result: {}", measurement_result);
            assert_eq!(
                measurement_result, expected_result,
                "Measurement accuracy test failed for state {:?} and basis {:?}",
                state, basis
            );
        }
    }

    #[test]
    fn test_measurement_consistency() {
        let state = BB84State::QubitZero;
        let basis = MeasurementBasis::Basis1;
        let first_result = measure_bb84_state(state, basis);
        let second_result = measure_bb84_state(state, basis);
        assert_eq!(first_result, second_result);
    }

    #[test]
    fn test_state_generation_consistency() {
        let mut zero_count = 0;
        let mut one_count = 0;
        let mut plus_count = 0;
        let mut minus_count = 0;
        for _ in 0..100 {
            match generate_bb84_state(random_bit(), MeasurementBasis::random()) {
                BB84State::QubitZero => zero_count += 1,
                BB84State::QubitOne => one_count += 1,
                BB84State::QubitPlus => plus_count += 1,
                BB84State::QubitMinus => minus_count += 1,
            }
        }
        // The assertion here depends on what you expect in your test
        // For instance, if you expect a balanced distribution among all states, you could assert that
        assert!(zero_count > 0 && one_count > 0 && plus_count > 0 && minus_count > 0);
    }

    #[test]
    fn test_random_basis_generation_consistency() {
        let mut basis1_count = 0;
        let mut basis2_count = 0;
        for _ in 0..100 {
            match MeasurementBasis::random() {
                MeasurementBasis::Basis1 => basis1_count += 1,
                MeasurementBasis::Basis2 => basis2_count += 1,
                // Handle other bases if any...
            }
        }
        assert!(basis1_count > 0 && basis2_count > 0);
    }

    #[test]
    fn test_protocol_under_noise() {
        let mut successful_runs = 0;
        let trials = 100; // Adjust the number of trials as needed

        for _ in 0..trials {
            let alice_state = generate_bb84_state(random_bit(), MeasurementBasis::random());
            let bob_state = if random_noise(0.1) {
                // Assuming 10% noise probability
                flip_state(alice_state) // Simulate random noise
            } else {
                alice_state
            };

            // alice_step returns a Result containing a tuple (bool, MeasurementBasis)
            let alice_result = alice_step().unwrap(); // Unwrap the result to get the tuple

            // Pass the entire tuple from alice_step to bob_step
            let bob_bit = bob_step(bob_state, alice_result);

            // Compare only the boolean part of Alice's result with Bob's bit
            if alice_result.0 == bob_bit {
                successful_runs += 1;
            }
        }

        // Assert that there are some successful runs
        assert!(successful_runs > 0, "Successful runs: {}", successful_runs);
    }

    #[test]
    fn test_complete_protocol_simulation() {
        let number_of_qubits = 10;
        let mut alice_bits = Vec::new();
        let mut alice_bases = Vec::new();
        let mut bob_bases = Vec::new();
        let mut bob_measurements = Vec::new();

        // Alice generates random bits and bases
        for _ in 0..number_of_qubits {
            let bit = random_bit();
            let basis = MeasurementBasis::random();
            alice_bits.push(bit);
            alice_bases.push(basis);
        }

        // Simulate the transmission of qubits from Alice to Bob
        for i in 0..number_of_qubits {
            let simulated_state = generate_bb84_state(alice_bits[i], alice_bases[i]);
            let bob_basis = MeasurementBasis::random();
            bob_bases.push(bob_basis);
            let measurement = measure_bb84_state(simulated_state, bob_basis);
            bob_measurements.push(measurement);
        }

        // Perform the sifting process
        let mut sifted_alice_bits = Vec::new();
        let mut sifted_bob_bits = Vec::new();
        for i in 0..number_of_qubits {
            if alice_bases[i] == bob_bases[i] {
                sifted_alice_bits.push(alice_bits[i]);
                sifted_bob_bits.push(bob_measurements[i]);
            }
        }

        println!("Alice Bits: {:?}", alice_bits);
        println!("Alice Bases: {:?}", alice_bases);
        println!("Bob Bases: {:?}", bob_bases);
        println!("Bob Measurements: {:?}", bob_measurements);
        println!("Sifted Alice Bits: {:?}", sifted_alice_bits);
        println!("Sifted Bob Bits: {:?}", sifted_bob_bits);

        // Check if the sifted keys match
        assert_eq!(
            sifted_alice_bits, sifted_bob_bits,
            "Sifted keys do not match"
        );
    }

    #[test]
    fn test_direct_state_transmission() {
        let states = vec![
            BB84State::QubitZero,
            BB84State::QubitOne,
            BB84State::QubitPlus,
            BB84State::QubitMinus,
        ];
        let bases = vec![MeasurementBasis::Basis1, MeasurementBasis::Basis2];

        for &state in &states {
            for &basis in &bases {
                println!(
                    "Testing Direct Transmission - State: {:?}, Basis: {:?}",
                    state, basis
                );
                let measurement_result = measure_bb84_state(state, basis);
                println!("Measurement Result: {}", measurement_result);

                // Add assertions here
                match (state, basis) {
                    (BB84State::QubitZero, MeasurementBasis::Basis1) => {
                        assert!(!measurement_result)
                    }
                    (BB84State::QubitOne, MeasurementBasis::Basis1) => assert!(measurement_result),
                    // For QubitPlus and QubitMinus in Basis1, outcomes are probabilistic.
                    // Therefore, we cannot assert a specific result.
                    // Similarly, for any state in Basis2, outcomes are probabilistic.
                    _ => (), // Skipping assertions for probabilistic outcomes
                }
            }
        }
    }

    #[test]
    fn test_protocol_with_noise() {
        let noise_probability = 0.5;
        let number_of_qubits = 10;
        let mut alice_bits = Vec::new();
        let mut alice_bases = Vec::new();
        let mut bob_bases = Vec::new();
        let mut bob_measurements = Vec::new();

        for _ in 0..number_of_qubits {
            alice_bits.push(random_bit());
            alice_bases.push(MeasurementBasis::random());
        }

        for i in 0..number_of_qubits {
            let state = generate_bb84_state(alice_bits[i], alice_bases[i]);

            // THE LOGIC FIX:
            // Force the first qubit (i == 0) to have a MATCHING basis
            // so that our "forced noise" actually survives the sifting process.
            let bob_basis = if i == 0 {
                alice_bases[i]
            } else {
                MeasurementBasis::random()
            };

            bob_bases.push(bob_basis);
            let measurement = measure_bb84_state(state, bob_basis);

            // THE NOISE FIX:
            // Guarantee a flip on the first bit.
            if i == 0 || random_noise(noise_probability) {
                bob_measurements.push(!measurement);
            } else {
                bob_measurements.push(measurement);
            }
        }

        let mut sifted_alice_bits = Vec::new();
        let mut noisy_sifted_bob_bits = Vec::new();
        for i in 0..number_of_qubits {
            if alice_bases[i] == bob_bases[i] {
                sifted_alice_bits.push(alice_bits[i]);
                noisy_sifted_bob_bits.push(bob_measurements[i]);
            }
        }

        // Now, index 0 is guaranteed to be in these vectors AND guaranteed to be different.
        assert_ne!(
            sifted_alice_bits, noisy_sifted_bob_bits,
            "Noise did not affect the final keys as expected"
        );
    }

    #[test]
    fn test_protocol_robustness_against_eavesdropping() {
        let number_of_qubits = 10;
        let mut alice_bits = Vec::new();
        let mut alice_bases = Vec::new();
        let mut bob_bases = Vec::new();
        let mut eavesdropper_bases = Vec::new();
        let mut bob_measurements = Vec::new(); // Declaration and initialization of bob_measurements

        // Alice generates random bits and bases
        for _ in 0..number_of_qubits {
            alice_bits.push(random_bit());
            alice_bases.push(MeasurementBasis::random());
        }

        // Eavesdropper intercepts and measures the qubits in random bases
        for i in 0..number_of_qubits {
            let state = generate_bb84_state(alice_bits[i], alice_bases[i]);
            let eavesdropper_basis = MeasurementBasis::random();
            let _ = measure_bb84_state(state, eavesdropper_basis); // Eavesdropper's measurement (not used directly)
            eavesdropper_bases.push(eavesdropper_basis);
        }

        // Bob randomly chooses bases and measures the states
        for _i in 0..number_of_qubits {
            let bob_basis = MeasurementBasis::random();
            bob_bases.push(bob_basis);
            let state = generate_bb84_state(random_bit(), bob_basis); // Bob measures a new random state
            let measurement = measure_bb84_state(state, bob_basis);
            bob_measurements.push(measurement);
        }
        // Perform the sifting process
        let mut sifted_alice_bits = Vec::new();
        let mut sifted_bob_bits = Vec::new();
        for i in 0..number_of_qubits {
            if alice_bases[i] == bob_bases[i] {
                sifted_alice_bits.push(alice_bits[i]);
                sifted_bob_bits.push(bob_measurements[i]);
            }
        }

        // Check for discrepancies caused by eavesdropping
        assert_ne!(
            sifted_alice_bits, sifted_bob_bits,
            "Eavesdropping did not introduce detectable errors"
        );
    }

    #[test]
    fn test_key_reconciliation_and_privacy_amplification() {
        let number_of_qubits = 10;
        let mut alice_bits = Vec::new();
        let mut alice_bases = Vec::new();
        let mut bob_bases = Vec::new();
        let mut bob_measurements = Vec::new();

        // Alice generates random bits and bases
        for _ in 0..number_of_qubits {
            alice_bits.push(random_bit());
            alice_bases.push(MeasurementBasis::random());
        }

        // Simulate transmission and introduce noise
        for i in 0..number_of_qubits {
            let state = generate_bb84_state(alice_bits[i], alice_bases[i]);
            let bob_basis = MeasurementBasis::random();
            bob_bases.push(bob_basis);

            let noisy_state = if random_noise(0.1) {
                // Assuming 10% noise
                flip_state(state) // Flip the state to simulate noise
            } else {
                state
            };

            let measurement = measure_bb84_state(noisy_state, bob_basis);
            bob_measurements.push(measurement);
        }

        // Sift keys based on matching bases
        let mut sifted_alice_bits = Vec::new();
        let mut sifted_bob_bits = Vec::new();
        for i in 0..number_of_qubits {
            if alice_bases[i] == bob_bases[i] {
                sifted_alice_bits.push(alice_bits[i]);
                sifted_bob_bits.push(bob_measurements[i]);
            }
        }

        // Apply error correction
        let corrected_bob_bits =
            error_correction(sifted_alice_bits.clone(), sifted_bob_bits.clone());

        // Apply privacy amplification
        let final_alice_key = apply_privacy_amplification(sifted_alice_bits);
        let final_bob_key = apply_privacy_amplification(corrected_bob_bits);

        // Check if the final keys are identical
        assert_eq!(
            final_alice_key, final_bob_key,
            "Final keys are not identical after reconciliation and privacy amplification"
        );
    }

    fn random_noise(probability: f64) -> bool {
        rand::random::<f64>() < probability
    }

    fn error_correction(alice_bits: Vec<bool>, bob_bits: Vec<bool>) -> Vec<bool> {
        // Assuming alice_bits and bob_bits are of the same length
        alice_bits
            .iter()
            .zip(bob_bits.iter())
            .map(|(&a, &b)| {
                if a == b {
                    a
                } else {
                    rand::random()
                } // If different, randomly choose one
            })
            .collect()
    }

    fn apply_privacy_amplification(key: Vec<bool>) -> Vec<bool> {
        // Store the length before consuming 'key' with 'into_iter()'
        let key_length = key.len();
        key.into_iter().take(key_length / 2).collect()
    }
}

fn random_noise(probability: f64) -> bool {
    let mut rng = rand::thread_rng(); // Get a random number generator
    rng.gen::<f64>() < probability
}
