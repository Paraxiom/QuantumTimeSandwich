use num_bigint::BigInt;
use num_traits::{One, Zero};
use rand::{thread_rng, Rng};

const POLYNOMIAL_DEGREE: usize = 64;
const MODULUS: i64 = 101; // A small prime number as the modulus

/// Represents a polynomial for Ring-LWE
struct Polynomial {
    coefficients: Vec<i64>,
}

impl Polynomial {
    /// Generates a random polynomial
    fn random() -> Self {
        let mut rng = thread_rng();
        let coeffs = (0..POLYNOMIAL_DEGREE)
            .map(|_| rng.gen_range(0..MODULUS))
            .collect();
        Polynomial {
            coefficients: coeffs,
        }
    }

    /// Adds two polynomials modulo the given modulus
    fn add_mod(&self, other: &Self, modulus: i64) -> Self {
        let mut result_coeffs = vec![0; POLYNOMIAL_DEGREE];
        for i in 0..POLYNOMIAL_DEGREE {
            result_coeffs[i] = (self.coefficients[i] + other.coefficients[i]) % modulus;
        }
        Polynomial {
            coefficients: result_coeffs,
        }
    }

    /// Multiplies two polynomials modulo x^n + 1 and the given modulus
    fn mul_mod(&self, other: &Self, modulus: i64) -> Self {
        let mut result = vec![0; 2 * POLYNOMIAL_DEGREE - 1];
        for (i, &self_coeff) in self.coefficients.iter().enumerate() {
            for (j, &other_coeff) in other.coefficients.iter().enumerate() {
                result[i + j] += self_coeff * other_coeff;
            }
        }
        // Reduce modulo x^n + 1
        for i in POLYNOMIAL_DEGREE..2 * POLYNOMIAL_DEGREE - 1 {
            result[i - POLYNOMIAL_DEGREE] = (result[i - POLYNOMIAL_DEGREE] + result[i]) % modulus;
        }
        result.truncate(POLYNOMIAL_DEGREE);
        Polynomial {
            coefficients: result,
        }
    }
}

fn main() {
    // Generate secret key (random polynomial)
    let secret_key = Polynomial::random();

    // Generate public key (random polynomial)
    let public_key = Polynomial::random();

    // Encrypt a message (simplified for demonstration)
    let message = Polynomial::random(); // Message represented as a polynomial
    let encrypted_message = message.add_mod(&secret_key.mul_mod(&public_key, MODULUS), MODULUS);

    // Decrypt the message (simplified for demonstration)
    let decrypted_message =
        encrypted_message.add_mod(&secret_key.mul_mod(&public_key, MODULUS), MODULUS);

    // Display results
    println!("Secret Key: {:?}", secret_key.coefficients);
    println!("Public Key: {:?}", public_key.coefficients);
    println!("Message: {:?}", message.coefficients);
    println!("Encrypted Message: {:?}", encrypted_message.coefficients);
    println!("Decrypted Message: {:?}", decrypted_message.coefficients);
}
