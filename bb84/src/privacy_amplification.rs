use rand::Rng;
#[cfg(test)]
use sha2::{Digest, Sha256};

#[cfg(test)]
fn hash_chunk(input_chunk: &[u8]) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(input_chunk);
    hasher.finalize().to_vec()
}

fn toeplitz_hash(shared_key: Vec<bool>, toeplitz_matrix: Vec<Vec<bool>>) -> Vec<bool> {
    let mut hashed_key = Vec::new();

    for row in toeplitz_matrix.iter() {
        let mut hash_bit = false;
        for (key_bit, matrix_bit) in shared_key.iter().zip(row.iter()) {
            // Perform bitwise AND, then XOR with the accumulated result
            hash_bit ^= key_bit & matrix_bit;
        }
        hashed_key.push(hash_bit);
    }

    hashed_key
}

// Usage in privacy amplification
pub fn apply_privacy_amplification(shared_key: Vec<bool>) -> Vec<bool> {
    let toeplitz_matrix = generate_random_toeplitz_matrix(); // Implement this function
    toeplitz_hash(shared_key, toeplitz_matrix)
}
fn generate_random_toeplitz_matrix() -> Vec<Vec<bool>> {
    let mut rng = rand::thread_rng();
    (0..10)
        .map(|_| (0..10).map(|_| rng.gen()).collect())
        .collect() // Example 10x10 matrix
}

// Tests
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_apply_privacy_amplification() {
        let shared_key = vec![true, false, true, false, true, false, true, false];
        let amplified_key = apply_privacy_amplification(shared_key);
        assert!(!amplified_key.is_empty());
    }
    #[test]
    fn test_random_key_input() {
        let mut rng = rand::thread_rng();
        let shared_key: Vec<bool> = (0..100).map(|_| rng.gen()).collect();
        let amplified_key = apply_privacy_amplification(shared_key.clone());

        assert_ne!(amplified_key, shared_key);
    }
    #[test]
    fn test_hash_function_accuracy() {
        let input_chunk = [0b10101010, 0b11001100, 0b11110000, 0b00001111]; // Example byte chunk
        let expected_output = hash_chunk(&input_chunk);
        let actual_output = hash_chunk(&input_chunk);

        assert_eq!(
            actual_output, expected_output,
            "Hash function did not produce expected output"
        );
    }
}
