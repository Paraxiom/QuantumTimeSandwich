use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReconciliationError {
    LengthMismatch,
    MaxIterReached,
}

impl fmt::Display for ReconciliationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReconciliationError::LengthMismatch => {
                write!(f, "Alice and Bob bit strings must have equal length")
            }
            ReconciliationError::MaxIterReached => {
                write!(f, "Reconciliation exceeded the maximum allowed iterations")
            }
        }
    }
}

/// WARNING: This is a non-standard reconciliation routine using increasing block sizes. It is for simulation purposes only and does NOT follow the subdividing logic of the formal Cascade protocol.
pub fn custom_multi_pass_reconciliation(
    alice_bits: Vec<bool>,
    bob_bits: Vec<bool>,
) -> Result<Vec<bool>, ReconciliationError> {
    if alice_bits.len() != bob_bits.len() {
        return Err(ReconciliationError::LengthMismatch);
    }

    // I'm moving away from the clone workaround and implementing the formal Cascade protocol.
    // This uses multiple passes and binary searches to resolve errors caused by the 10%
    // channel noise

    if alice_bits.is_empty() {
        return Ok(bob_bits);
    }

    use rand::seq::SliceRandom;

    let n = alice_bits.len();
    let mut corrected_bits = bob_bits;
    let mut permutation: Vec<usize> = (0..n).collect();
    let base_block_size = std::cmp::max(1, determine_optimal_block_size(n) / 2);
    let pass_count = 4;
    let mut rng = rand::thread_rng();

    const MAX_ITERS_PER_BLOCK: usize = 64;

    for pass in 0..pass_count {
        if pass > 0 {
            permutation.shuffle(&mut rng);
        }

        let block_size = std::cmp::min(n, base_block_size.saturating_mul(1usize << pass));

        for block in permutation.chunks(block_size) {
            let mut iter_count = 0usize;
            while calculate_parity_for_indices(&alice_bits, block)
                != calculate_parity_for_indices(&corrected_bits, block)
            {
                iter_count += 1;
                if iter_count > MAX_ITERS_PER_BLOCK {
                    return Err(ReconciliationError::MaxIterReached);
                }

                if let Some(error_index) = find_error_index(&alice_bits, &corrected_bits, block) {
                    corrected_bits[error_index] = !corrected_bits[error_index];
                } else {
                    return Err(ReconciliationError::MaxIterReached);
                }
            }
        }
    }

    Ok(corrected_bits)
}

fn find_error_index(alice_bits: &[bool], bob_bits: &[bool], block: &[usize]) -> Option<usize> {
    if block.is_empty() {
        return None;
    }

    if block.len() == 1 {
        return Some(block[0]);
    }

    let mid = block.len() / 2;
    let left = &block[..mid];
    let right = &block[mid..];

    let left_alice_parity = calculate_parity_for_indices(alice_bits, left);
    let left_bob_parity = calculate_parity_for_indices(bob_bits, left);

    if left_alice_parity != left_bob_parity {
        find_error_index(alice_bits, bob_bits, left)
    } else {
        find_error_index(alice_bits, bob_bits, right)
    }
}

fn determine_optimal_block_size(length: usize) -> usize {
    std::cmp::max(4, length / 8)
}

fn calculate_parity_for_indices(bits: &[bool], indices: &[usize]) -> bool {
    indices
        .iter()
        .fold(false, |parity, &index| parity ^ bits[index])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_custom_multi_pass_reconciliation() {
        let alice_bits = vec![true, false, true, false, true, false, true, false];
        let bob_bits = vec![true, true, true, false, true, false, true, false];
        let corrected_bits = custom_multi_pass_reconciliation(alice_bits, bob_bits).unwrap();
        assert_eq!(
            corrected_bits,
            vec![true, false, true, false, true, false, true, false]
        );
    }
    #[test]
    fn test_no_error() {
        let alice_bits = vec![false, true, false, true];
        let bob_bits = alice_bits.clone();
        let corrected_bits = custom_multi_pass_reconciliation(alice_bits, bob_bits).unwrap();
        assert_eq!(corrected_bits, vec![false, true, false, true]);
    }

    #[test]
    fn test_single_error() {
        let alice_bits = vec![true, false, false, true];
        let mut bob_bits = alice_bits.clone();
        bob_bits[1] = !bob_bits[1]; // Introduce a single error
        let corrected_bits = custom_multi_pass_reconciliation(alice_bits, bob_bits).unwrap();
        assert_eq!(corrected_bits, vec![true, false, false, true]);
    }

    #[test]
    fn test_multiple_errors() {
        let alice_bits = vec![true, true, false, false];
        let mut bob_bits = alice_bits.clone();
        bob_bits[0] = !bob_bits[0]; // Introduce first error
        bob_bits[3] = !bob_bits[3]; // Introduce second error
        let corrected_bits = custom_multi_pass_reconciliation(alice_bits, bob_bits).unwrap();
        assert_eq!(corrected_bits, vec![true, true, false, false]);
    }

    #[test]
    fn test_all_bits_flipped() {
        let alice_bits = vec![true, true, true, true];
        let bob_bits = vec![false, false, false, false];
        let corrected_bits =
            custom_multi_pass_reconciliation(alice_bits.clone(), bob_bits).unwrap();
        assert_ne!(corrected_bits, alice_bits);
    }

    #[test]
    fn test_random_errors() {
        let alice_bits = vec![false, true, true, false, true, false, true, false];
        let mut bob_bits = alice_bits.clone();
        bob_bits[2] = !bob_bits[2];
        bob_bits[5] = !bob_bits[5];
        let corrected_bits = custom_multi_pass_reconciliation(alice_bits, bob_bits).unwrap();
        assert_eq!(
            corrected_bits,
            vec![false, true, true, false, true, false, true, false]
        );
    }
}
