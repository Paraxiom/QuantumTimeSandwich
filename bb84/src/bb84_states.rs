use crate::bb84::measure_bb84_state;
use rand::prelude::*;
use rand::Rng;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BB84State {
    QubitZero,
    QubitOne,
    QubitPlus,  // Represents the |+> state
    QubitMinus, // Represents the |-> state
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MeasurementBasis {
    Basis1,
    Basis2,
    // ... other bases
}

impl MeasurementBasis {
    pub fn random() -> Self {
        let mut rng = thread_rng();
        match rng.gen_range(0..2) {
            // Assuming there are 2 types of bases
            0 => MeasurementBasis::Basis1,
            1 => MeasurementBasis::Basis2,
            // ... handle other cases
            _ => unreachable!(),
        }
    }
}

pub type Basis = MeasurementBasis;

pub fn random_bit() -> bool {
    let mut rng = rand::thread_rng();
    rng.gen()
}

// fn alice_step(state: BB84State) -> bool {
//     // Alice randomly chooses a basis.
//     let basis = MeasurementBasis::random();

//     // Alice measures her state in the chosen basis.
//     let bit = measure_bb84_state(state, basis);

//     // Alice returns the bit that she measured.
//     return bit;
// }

fn bob_step(state: BB84State, _alice_bit: bool) -> bool {
    // Bob randomly chooses a basis.
    let basis = MeasurementBasis::random();

    // Bob measures his state in the chosen basis.
    let bit = measure_bb84_state(state, basis);

    // Bob returns the bit that he measured.
    return bit;
}

fn main() {
    let basis = Basis::random();
    let value = random_bit();

    println!("Basis: {:?}", basis);
    println!("Value: {:?}", value);
}
