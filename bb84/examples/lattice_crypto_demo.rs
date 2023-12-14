use rand::Rng;

const LATTICE_SIZE: usize = 128; // Size of the lattice

/// Generates a random lattice vector with small coefficients.
fn generate_small_vector() -> Vec<i32> {
    let mut rng = rand::thread_rng();
    (0..LATTICE_SIZE).map(|_| rng.gen_range(-5..=5)).collect()
}

/// Adds two lattice vectors modulo a large number (for simplicity).
fn add_vectors_modulo(a: &[i32], b: &[i32], modulo: i32) -> Vec<i32> {
    a.iter()
        .zip(b.iter())
        .map(|(x, y)| (x + y) % modulo)
        .collect()
}

fn main() {
    // Generate secret and public vectors
    let secret_vector = generate_small_vector(); // Secret key
    let public_vector = generate_small_vector(); // Public key component

    // Example operation: adding two vectors modulo a large number
    let modulo = 100; // A large number for the modulo operation
    let combined_vector = add_vectors_modulo(&secret_vector, &public_vector, modulo);

    // Output the vectors (in a real implementation, these would be used in cryptographic operations)
    println!("Secret Vector: {:?}", secret_vector);
    println!("Public Vector: {:?}", public_vector);
    println!("Combined Vector (mod {}): {:?}", modulo, combined_vector);
}
