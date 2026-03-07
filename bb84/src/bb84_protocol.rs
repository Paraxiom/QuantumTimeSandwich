use crate::error_correction::custom_multi_pass_reconciliation;
use crate::error_correction::ReconciliationError;
use crate::privacy_amplification::apply_privacy_amplification;
use rand::Rng;

/// Represents Alice's role in the BB84 protocol
#[derive(Clone, Debug)]
pub struct Alice {
    num_qubits: usize,
    bits: Vec<bool>,
    bases: Vec<crate::bb84_states::MeasurementBasis>,
}

impl Alice {
    /// Create a new Alice with the specified number of qubits
    pub fn new(num_qubits: usize) -> Self {
        let mut rng = rand::thread_rng();
        let bits: Vec<bool> = (0..num_qubits).map(|_| rng.gen()).collect();
        let bases: Vec<crate::bb84_states::MeasurementBasis> = (0..num_qubits)
            .map(|_| {
                if rng.gen() {
                    crate::bb84_states::MeasurementBasis::Basis1
                } else {
                    crate::bb84_states::MeasurementBasis::Basis2
                }
            })
            .collect();

        Alice {
            num_qubits,
            bits,
            bases,
        }
    }

    pub fn num_qubits(&self) -> usize {
        self.num_qubits
    }

    pub fn bits(&self) -> &[bool] {
        &self.bits
    }

    pub fn bases(&self) -> &[crate::bb84_states::MeasurementBasis] {
        &self.bases
    }
}

/// Represents Bob's role in the BB84 protocol
#[derive(Clone, Debug)]
pub struct Bob {
    bases: Vec<crate::bb84_states::MeasurementBasis>,
    measurements: Vec<bool>,
}

impl Bob {
    /// Create a new Bob
    pub fn new() -> Self {
        Bob {
            bases: Vec::new(),
            measurements: Vec::new(),
        }
    }

    /// Generate random bases for Bob
    pub fn generate_bases(num_qubits: usize) -> Self {
        let mut rng = rand::thread_rng();
        let bases: Vec<crate::bb84_states::MeasurementBasis> = (0..num_qubits)
            .map(|_| {
                if rng.gen() {
                    crate::bb84_states::MeasurementBasis::Basis1
                } else {
                    crate::bb84_states::MeasurementBasis::Basis2
                }
            })
            .collect();

        Bob {
            bases,
            measurements: Vec::new(),
        }
    }

    pub fn bases(&self) -> &[crate::bb84_states::MeasurementBasis] {
        &self.bases
    }

    pub fn measurements(&self) -> &[bool] {
        &self.measurements
    }

    pub fn add_measurement(&mut self, bit: bool) {
        self.measurements.push(bit);
    }
}

// Existing BB84 protocol logic...

// After key exchange process
pub fn finalize_key(raw_key: Vec<bool>) -> Result<Vec<bool>, ReconciliationError> {
    let corrected_key = custom_multi_pass_reconciliation(raw_key.clone(), raw_key)?;
    // or
    // let corrected_key = ldpc_correction(raw_key);

    let seed = rand::random::<u64>();
    Ok(apply_privacy_amplification(corrected_key, seed))
}
