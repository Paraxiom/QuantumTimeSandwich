// mod.rs for the oqs_kex_rpc module within the grpc directory

pub mod server;
pub mod utils;

// Here, you can define shared structures, enums, or constants that are used throughout the oqs_kex_rpc module.

// For example, you might define a structure that represents the configuration for the key exchange.
pub struct KeyExchangeConfig {
    // Add configuration parameters here. For instance:
    pub algorithm: String,
    // Add other configuration fields as necessary
}

// If there are common functions or utilities that both the server and possibly other parts of your grpc module need,
// you can define them here or in the utils sub-module.

// Example utility function
pub fn example_util_function() {
    // Implementation of the function
}

// You can also include error handling related to the key exchange process
pub enum KeyExchangeError {
    ConnectionError,
    CryptographicError,
    // Other error types...
}

// Implement any additional shared logic or utilities needed for the key exchange
