use crate::bb84_states::{random_bit, BB84State, MeasurementBasis};
use rand::Rng;

/// Weak coherent pulse output categories used for BB84 source modeling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WeakPulse {
    /// No photon emitted (vacuum pulse).
    Vacuum,
    /// Exactly one photon emitted.
    Single(BB84State),
    /// Two or more photons emitted in the same prepared state.
    Multi { photon_count: u32, state: BB84State },
}

/// Practical weak-coherent BB84 source.
///
/// Instead of always producing exactly one photon, this source samples a photon
/// count from a Poisson distribution with mean `mu` (`mean_photon_number`).
#[derive(Debug, Clone, Copy)]
pub struct WeakCoherentSource {
    mean_photon_number: f64,
}

impl WeakCoherentSource {
    /// Create a weak coherent source with mean photon number `mu`.
    pub fn new(mean_photon_number: f64) -> Self {
        Self { mean_photon_number }
    }

    /// Return configured mean photon number `mu`.
    pub fn mean_photon_number(&self) -> f64 {
        self.mean_photon_number
    }

    /// Sample a Poisson-distributed photon count for one pulse.
    ///
    /// Uses Knuth's method and returns `0`, `1`, `2`, ...
    pub fn sample_photon_count<R: Rng + ?Sized>(&self, rng: &mut R) -> u32 {
        let mu = self.mean_photon_number;
        if !mu.is_finite() || mu <= 0.0 {
            return 0;
        }

        let threshold = (-mu).exp();
        let mut k: u32 = 0;
        let mut product = 1.0_f64;

        loop {
            k += 1;
            product *= rng.gen::<f64>();
            if product <= threshold {
                return k - 1;
            }
        }
    }

    /// Emit one BB84 pulse and classify it as vacuum/single/multi-photon.
    pub fn emit_pulse<R: Rng + ?Sized>(
        &self,
        bit: bool,
        basis: MeasurementBasis,
        rng: &mut R,
    ) -> WeakPulse {
        let photon_count = self.sample_photon_count(rng);
        let state = generate_bb84_state(bit, basis);

        match photon_count {
            0 => WeakPulse::Vacuum,
            1 => WeakPulse::Single(state),
            n => WeakPulse::Multi {
                photon_count: n,
                state,
            },
        }
    }
}

pub fn generate_bb84_state(bit: bool, basis: MeasurementBasis) -> BB84State {
    match (bit, basis) {
        (false, MeasurementBasis::Basis1) => BB84State::QubitZero,
        (true, MeasurementBasis::Basis1) => BB84State::QubitOne,
        (false, MeasurementBasis::Basis2) => BB84State::QubitMinus,
        (true, MeasurementBasis::Basis2) => BB84State::QubitPlus,
    }
}

pub fn measure_bb84_state(state: BB84State, basis: MeasurementBasis) -> bool {
    match (state, basis) {
        (BB84State::QubitZero, MeasurementBasis::Basis1) => false,
        (BB84State::QubitOne, MeasurementBasis::Basis1) => true,
        (BB84State::QubitMinus, MeasurementBasis::Basis2) => false,
        (BB84State::QubitPlus, MeasurementBasis::Basis2) => true,
        _ => rand::random(),
    }
}

pub fn simulate_eve_attack(state: BB84State) -> BB84State {
    let eve_basis = MeasurementBasis::random();
    let intercepted_bit = measure_bb84_state(state, eve_basis);
    generate_bb84_state(intercepted_bit, eve_basis)
}

pub fn flip_state(state: BB84State) -> BB84State {
    match state {
        BB84State::QubitZero => BB84State::QubitOne,
        BB84State::QubitOne => BB84State::QubitZero,
        BB84State::QubitPlus => BB84State::QubitMinus,
        BB84State::QubitMinus => BB84State::QubitPlus,
    }
}

pub fn alice_step() -> Result<(bool, MeasurementBasis), &'static str> {
    Ok((random_bit(), MeasurementBasis::random()))
}

pub fn bob_step(state: BB84State, alice_message: (bool, MeasurementBasis)) -> bool {
    let (_, alice_basis) = alice_message;
    measure_bb84_state(state, alice_basis)
}
