// mod.rs for utils in the oqs_kex_rpc module

// This module contains utility functions and structures used by the oqs_kex_rpc module.

// Example utility function for logging
pub fn log_info(message: &str) {
    // Implement logging functionality
    // This could be as simple as printing to stdout or integrating with a logging framework
    println!("Info: {}", message);
}

// Utility function for error logging
pub fn log_error(message: &str) {
    // Error logging implementation
    println!("Error: {}", message);
}

// You might also have utility functions for common cryptographic operations
// For example, a function to validate key parameters or format keys

pub fn validate_key_parameters(key: &[u8]) -> bool {
    // Implement validation logic
    // Return true if the key parameters meet the required criteria
    key.len() >= 128 // Example condition, adjust according to your needs
}

// Add more utility functions as needed
