// protocol.rs
use crate::unit_circle_states::RotationGate;

pub struct Protocol {
    pub gates: Vec<RotationGate>,
}

impl Protocol {
    pub fn new(gates: Vec<RotationGate>) -> Self {
        Protocol { gates }
    }
    pub fn gates(&self) -> &[RotationGate] {
        &self.gates
    }

    // Other necessary methods...
}
