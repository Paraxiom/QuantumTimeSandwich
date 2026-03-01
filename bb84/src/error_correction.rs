pub fn cascade_correction(alice_bits: Vec<bool>, bob_bits: Vec<bool>) -> Vec<bool> {
    if alice_bits.len() != bob_bits.len() {
        panic!("Alice's and Bob's bit strings must be of the same length");
    }

    let mut corrected_bits = bob_bits.clone();
    let mut block_size = determine_optimal_block_size(alice_bits.len());

    while block_size > 0 {
        for i in (0..alice_bits.len()).step_by(block_size) {
            let end = std::cmp::min(i + block_size, alice_bits.len());
            let alice_block = &alice_bits[i..end];
            let bob_block = corrected_bits[i..end].to_vec(); // Clone the necessary slice

            if calculate_parity(alice_block) != calculate_parity(&bob_block) {
                correct_block_mismatch(alice_block, &bob_block, &mut corrected_bits, i);
            }
        }
        block_size /= 2; // Reduce block size for the next pass
    }

    corrected_bits
}

// Rest of the functions (determine_optimal_block_size, calculate_parity, correct_block_mismatch) remain unchanged

fn correct_block_mismatch(
    alice_block: &[bool],
    bob_block: &[bool],
    corrected_bits: &mut Vec<bool>,
    start_index: usize,
) {
    for (i, (&alice_bit, &bob_bit)) in alice_block.iter().zip(bob_block.iter()).enumerate() {
        if alice_bit != bob_bit {
            corrected_bits[start_index + i] = alice_bit; // Correct the bit based on Alice's bit string
        }
    }
}

fn determine_optimal_block_size(length: usize) -> usize {
    // Example logic for determining block size based on length
    // Start with larger blocks and decrease size in each iteration
    std::cmp::max(4, length / 8)
}

fn calculate_parity(bits: &[bool]) -> bool {
    bits.iter().filter(|&&bit| bit).count() % 2 == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cascade_correction() {
        let alice_bits = vec![true, false, true, false, true, false, true, false];
        let bob_bits = vec![true, true, true, false, true, false, true, false];
        let corrected_bits = cascade_correction(alice_bits, bob_bits);
        assert_eq!(
            corrected_bits,
            vec![true, false, true, false, true, false, true, false]
        );
    }
    #[test]
    fn test_no_error() {
        let alice_bits = vec![false, true, false, true];
        let bob_bits = alice_bits.clone();
        let corrected_bits = cascade_correction(alice_bits, bob_bits);
        assert_eq!(corrected_bits, vec![false, true, false, true]);
    }

    #[test]
    fn test_single_error() {
        let alice_bits = vec![true, false, false, true];
        let mut bob_bits = alice_bits.clone();
        bob_bits[1] = !bob_bits[1]; // Introduce a single error
        let corrected_bits = cascade_correction(alice_bits, bob_bits);
        assert_eq!(corrected_bits, vec![true, false, false, true]);
    }

    #[test]
    fn test_multiple_errors() {
        let alice_bits = vec![true, true, false, false];
        let mut bob_bits = alice_bits.clone();
        bob_bits[0] = !bob_bits[0]; // Introduce first error
        bob_bits[3] = !bob_bits[3]; // Introduce second error
        let corrected_bits = cascade_correction(alice_bits, bob_bits);
        assert_eq!(corrected_bits, vec![true, true, false, false]);
    }

    #[test]
    fn test_all_bits_flipped() {
        let alice_bits = vec![true, true, true, true];
        let bob_bits = vec![false, false, false, false];
        let corrected_bits = cascade_correction(alice_bits, bob_bits);
        assert_eq!(corrected_bits, vec![true, true, true, true]);
    }

    #[test]
    fn test_random_errors() {
        let alice_bits = vec![false, true, true, false, true, false, true, false];
        let mut bob_bits = alice_bits.clone();
        bob_bits[2] = !bob_bits[2];
        bob_bits[5] = !bob_bits[5];
        let corrected_bits = cascade_correction(alice_bits, bob_bits);
        assert_eq!(
            corrected_bits,
            vec![false, true, true, false, true, false, true, false]
        );
    }
    fn test_complex_error_scenario() {
        let alice_bits = vec![true, false, true, false, false, true, true, false];
        let mut bob_bits = alice_bits.clone();
        bob_bits[1] = !bob_bits[1]; // Introduce first error
        bob_bits[4] = !bob_bits[4]; // Introduce second error
        let corrected_bits = cascade_correction(alice_bits, bob_bits);
        assert_eq!(
            corrected_bits,
            vec![true, false, true, false, false, true, true, false]
        );
    }
}
