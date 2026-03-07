use crate::bb84::{measure_bb84_state, WeakCoherentSource, WeakPulse};
use crate::bb84_states::{random_bit, BB84State, MeasurementBasis};
use rand::Rng;

// Moving beyond Intercept-Resend to simulate PNS attacks.
// This tooling demonstrates the necessity of Privacy Amplification even when QBER is low.

/// Stores photons Eve splits from multi-photon pulses until basis announcement.
#[derive(Debug, Default, Clone)]
pub struct QuantumMemory {
    stored_states: Vec<BB84State>,
}

impl QuantumMemory {
    /// Create empty memory.
    pub fn new() -> Self {
        Self {
            stored_states: Vec::new(),
        }
    }

    /// Number of stored photons.
    pub fn len(&self) -> usize {
        self.stored_states.len()
    }

    /// True if no stored photons.
    pub fn is_empty(&self) -> bool {
        self.stored_states.is_empty()
    }

    /// Store a split photon state.
    pub fn store(&mut self, state: BB84State) {
        self.stored_states.push(state);
    }

    /// Measure one stored photon after basis announcement.
    ///
    /// When `announced_basis` matches Alice's encoding basis (as in BB84 sifting),
    /// this yields the encoded bit with certainty for that stored photon.
    pub fn measure_with_announced_basis(
        &mut self,
        announced_basis: MeasurementBasis,
    ) -> Option<bool> {
        self.stored_states
            .pop()
            .map(|state| measure_bb84_state(state, announced_basis))
    }
}

/// Photon Number Splitting attacker.
#[derive(Debug, Default, Clone)]
pub struct PNSAttack {
    /// Quantum memory used to defer measurement until basis announcement.
    pub memory: QuantumMemory,
}

impl PNSAttack {
    /// Create a PNS attacker with empty memory.
    pub fn new() -> Self {
        Self {
            memory: QuantumMemory::new(),
        }
    }

    /// Intercept a pulse and split one photon when 2+ photons are present.
    ///
    /// Eve stores exactly one photon and forwards the remaining photons to Bob
    /// without disturbing their quantum state.
    pub fn intercept_and_split(&mut self, pulse: WeakPulse) -> WeakPulse {
        match pulse {
            WeakPulse::Vacuum => WeakPulse::Vacuum,
            WeakPulse::Single(state) => WeakPulse::Single(state),
            WeakPulse::Multi {
                photon_count,
                state,
            } => {
                self.memory.store(state);
                let remaining = photon_count.saturating_sub(1);
                if remaining <= 1 {
                    WeakPulse::Single(state)
                } else {
                    WeakPulse::Multi {
                        photon_count: remaining,
                        state,
                    }
                }
            }
        }
    }

    /// Measure one stored photon after sifting, using publicly announced basis.
    pub fn measure_after_sifting(&mut self, announced_basis: MeasurementBasis) -> Option<bool> {
        self.memory.measure_with_announced_basis(announced_basis)
    }
}

/// Aggregate metrics for PNS simulation runs.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PNSReport {
    pub sifted_bits: usize,
    pub bob_errors: usize,
    pub eve_learned_bits: usize,
    pub qber: f64,
}

/// Simulate PNS against weak coherent BB84 source and report QBER/information gain.
pub fn simulate_pns_attack<R: Rng + ?Sized>(
    source: &WeakCoherentSource,
    rounds: usize,
    rng: &mut R,
) -> PNSReport {
    let mut attack = PNSAttack::new();
    let mut sifted_bits = 0usize;
    let mut bob_errors = 0usize;
    let mut eve_learned_bits = 0usize;

    for _ in 0..rounds {
        let alice_bit = random_bit();
        let alice_basis = MeasurementBasis::random();

        let pulse = source.emit_pulse(alice_bit, alice_basis, rng);
        let forwarded = attack.intercept_and_split(pulse);

        let bob_basis = MeasurementBasis::random();
        if bob_basis != alice_basis {
            continue;
        }

        let bob_state = match forwarded {
            WeakPulse::Vacuum => continue,
            WeakPulse::Single(state) => state,
            WeakPulse::Multi { state, .. } => state,
        };

        sifted_bits += 1;
        let bob_bit = measure_bb84_state(bob_state, bob_basis);
        if bob_bit != alice_bit {
            bob_errors += 1;
        }

        if let Some(eve_bit) = attack.measure_after_sifting(alice_basis) {
            if eve_bit == alice_bit {
                eve_learned_bits += 1;
            }
        }
    }

    let qber = if sifted_bits == 0 {
        0.0
    } else {
        bob_errors as f64 / sifted_bits as f64
    };

    PNSReport {
        sifted_bits,
        bob_errors,
        eve_learned_bits,
        qber,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bb84::generate_bb84_state;
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    #[test]
    fn splits_multi_photon_and_forwards_rest() {
        let mut eve = PNSAttack::new();
        let state = generate_bb84_state(true, MeasurementBasis::Basis1);

        let forwarded = eve.intercept_and_split(WeakPulse::Multi {
            photon_count: 3,
            state,
        });

        assert_eq!(eve.memory.len(), 1);
        assert_eq!(
            forwarded,
            WeakPulse::Multi {
                photon_count: 2,
                state,
            }
        );
    }

    #[test]
    fn eve_gets_full_info_after_basis_announcement() {
        let mut eve = PNSAttack::new();
        let alice_bit = true;
        let alice_basis = MeasurementBasis::Basis2;
        let state = generate_bb84_state(alice_bit, alice_basis);

        eve.intercept_and_split(WeakPulse::Multi {
            photon_count: 2,
            state,
        });

        let eve_bit = eve.measure_after_sifting(alice_basis).unwrap();
        assert_eq!(eve_bit, alice_bit);
    }

    #[test]
    fn pns_adds_no_qber_in_this_model() {
        let source = WeakCoherentSource::new(0.1);
        let mut rng = StdRng::seed_from_u64(7);
        let report = simulate_pns_attack(&source, 5000, &mut rng);

        assert_eq!(report.bob_errors, 0);
        assert_eq!(report.qber, 0.0);
        assert!(report.eve_learned_bits > 0);
    }
}
