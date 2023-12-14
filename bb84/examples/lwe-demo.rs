use rand::{thread_rng, Rng};
use std::ops::Add;

const LATTICE_DIMENSION: usize = 64;
const MODULUS: i64 = 101; // A small prime number as the modulus
const ERROR_BOUND: i64 = 5; // Bound for the error term

/// Generates a random vector with values in the range [0, MODULUS)
fn generate_random_vector() -> Vec<i64> {
    let mut rng = thread_rng();
    (0..LATTICE_DIMENSION)
        .map(|_| rng.gen_range(0..MODULUS))
        .collect()
}

/// Generates a small error term
fn generate_error() -> i64 {
    let mut rng = thread_rng();
    rng.gen_range(-ERROR_BOUND..=ERROR_BOUND)
}

/// LWE encryption
fn encrypt(secret: &[i64], message: i64) -> (Vec<i64>, i64) {
    let a = generate_random_vector();
    let e = generate_error();
    let b = a
        .iter()
        .zip(secret)
        .fold(0, |acc, (&ai, &si)| acc.add(ai * si))
        % MODULUS
        + e
        + message;
    (a, b)
}

/// LWE decryption (simplified)
fn decrypt(secret: &[i64], ciphertext: &(Vec<i64>, i64)) -> i64 {
    let (a, b) = ciphertext;
    let inner_product = a
        .iter()
        .zip(secret)
        .fold(0, |acc, (&ai, &si)| acc.add(ai * si))
        % MODULUS;
    (b - inner_product) % MODULUS
}

fn main() {
    let secret_key = generate_random_vector(); // Secret key for LWE
    let message = 42; // Example message to encrypt

    // Encrypt the message
    let (a, b) = encrypt(&secret_key, message);
    println!("Encrypted Message: ({:?}, {})", a, b);

    // Decrypt the message
    let decrypted_message = decrypt(&secret_key, &(a, b));
    println!("Decrypted Message: {}", decrypted_message);
}
