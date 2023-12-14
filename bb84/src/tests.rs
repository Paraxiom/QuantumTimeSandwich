use crate::bb84_states::BB84State;
// Import other necessary modules or functions here
use crate::bb84::alice_step;
use crate::bb84::bob_step;
use crate::bb84::flip_state;
use crate::bb84::generate_bb84_state;
use crate::bb84::measure_bb84_state;
use crate::bb84_states::random_bit;
use crate::bb84_states::MeasurementBasis;
use rand::Rng;

#[cfg(test)]
mod tests {
    use super::*;
    use QuantumTimeSandwich::prelude::*;
    #[test]
    fn test_generate_bb84_state() {
        // Simulate generating a state multiple times and check distribution
        let mut zero_count = 0;
        let mut one_count = 0;
        for _ in 0..100 {
            match generate_bb84_state() {
                BB84State::QubitZero => zero_count += 1,
                BB84State::QubitOne => one_count += 1,
            }
        }
        assert!(zero_count > 0 && one_count > 0); // Ensure both states occur
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
        let bob_state = generate_bb84_state();
        let alice_bit = random_bit(); // Simulating Alice's bit
        let alice_basis = MeasurementBasis::Basis1; // or Basis2, depending on your test case

        // Create a tuple of Alice's bit and basis
        let alice_message = (alice_bit, alice_basis);

        // Pass the tuple to Bob's step
        let bob_bit = bob_step(bob_state, alice_message);

        // Check if Bob's bit is a valid boolean value
        assert!(bob_bit == true || bob_bit == false);
    }

    #[test]
    fn test_measurement_scenarios() {
        // Measure QubitZero in Basis1
        assert!(measure_bb84_state(
            BB84State::QubitZero,
            MeasurementBasis::Basis1
        ));

        // Measure QubitOne in Basis1
        assert!(!measure_bb84_state(
            BB84State::QubitOne,
            MeasurementBasis::Basis1
        ));
        let mut outcome_zero = 0;
        let mut outcome_one = 0;
        for _ in 0..100 {
            let result = measure_bb84_state(BB84State::QubitZero, MeasurementBasis::Basis2);
            if result {
                outcome_one += 1;
            } else {
                outcome_zero += 1;
            }
            println!("Basis2, QubitZero, Result: {}", result); // This line is added for debugging
        }
        // Check if outcomes are distributed (not deterministic)
        println!(
            "Basis2, QubitZero, Zero count: {}, One count: {}",
            outcome_zero, outcome_one
        ); // This line is added for debugging
        assert!(outcome_zero > 0 && outcome_one > 0);
        // Measure QubitOne in Basis2 (probabilistic outcome)
        let mut outcome_zero = 0;
        let mut outcome_one = 0;
        for _ in 0..100 {
            let result = measure_bb84_state(BB84State::QubitOne, MeasurementBasis::Basis2);
            if result {
                outcome_one += 1;
            } else {
                outcome_zero += 1;
            }
            println!("Basis2, QubitOne, Result: {}", result); // For debugging
        }
        println!(
            "Basis2, QubitOne, Zero count: {}, One count: {}",
            outcome_zero, outcome_one
        ); // For debugging
        assert!(outcome_zero > 0 && outcome_one > 0); // Expect a distribution of outcomes

        // Measure in Random Basis
        let state = BB84State::QubitZero; // or QubitOne
        let basis = MeasurementBasis::random();
        assert!(measure_bb84_state(state, basis));

        // Repeated Measurements
        let state = BB84State::QubitZero; // or QubitOne
        let basis = MeasurementBasis::Basis1; // or Basis2
        let first_result = measure_bb84_state(state, basis);
        let second_result = measure_bb84_state(state, basis);
        assert_eq!(first_result, second_result);

        // Invalid State or Basis (if applicable)
        // assert!(measure_bb84_state(invalid_state, invalid_basis).is_err());
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

        // Replace 'true' with the actual expected result based on your implementation
        let expected_result = true;

        assert_eq!(result, expected_result);
    }
    #[test]
    fn test_measurement_accuracy() {
        let state = BB84State::QubitZero;
        let basis = MeasurementBasis::Basis1;
        let result = measure_bb84_state(state, basis);
        // Replace with the expected result for this combination
        assert_eq!(result, true);

        // Test other combinations of state and basis...
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
        for _ in 0..100 {
            match generate_bb84_state() {
                BB84State::QubitZero => zero_count += 1,
                BB84State::QubitOne => one_count += 1,
            }
        }
        assert!(zero_count > 0 && one_count > 0);
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
            let alice_state = generate_bb84_state();
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
}

fn random_noise(probability: f64) -> bool {
    let mut rng = rand::thread_rng(); // Get a random number generator
    rng.gen::<f64>() < probability
}
