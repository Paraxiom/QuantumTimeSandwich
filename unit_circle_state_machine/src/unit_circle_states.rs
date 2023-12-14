use num_complex::Complex;

#[derive(Clone, Debug, Copy, PartialEq)]
pub enum GateType {
    PauliX,
    PauliY,
    PauliZ,
    Hadamard,
    CNOT,
    // Add other gate types as needed
}

#[derive(Clone, Debug, PartialEq)]
pub enum UnitCircleState {
    Initial,
    GateOperation {
        gate_type: GateType,
        state: Complex<f64>,
    },
    Measurement { result: Option<bool> },
    Entanglement,
    ErrorCorrection,
    Final,
}

impl Default for UnitCircleState {
    fn default() -> Self {
        UnitCircleState::Initial // Choose the variant that makes sense as a default
    }
}

impl UnitCircleState {
    // Method to transition to a GateOperation state
    pub fn gate_operation(gate_type: GateType, angle: Complex<f64>) -> Self {
        UnitCircleState::GateOperation {
            gate_type,
            state: angle,
        }
    }

    // Other methods for different state transitions
}
#[derive(Clone, Debug, Copy, PartialEq)]
pub struct RotationGate {
    angle: Complex<f64>,
    gate_type: GateType,
}

impl RotationGate {
    // Define the `new` method
    pub fn new(angle: Complex<f64>, gate_type: GateType) -> Self {
        RotationGate { angle, gate_type }
    }

    // Define the `get_gate_type` method
    pub fn get_gate_type(&self) -> GateType {
        self.gate_type
    }
    pub fn apply_to(&self, state: &UnitCircleState) -> UnitCircleState {
        println!("Applying gate: {:?}", self); // Debugging

        if self.angle == Complex::new(0.0, 0.0) {
            println!("Zero rotation applied. State unchanged."); // Debugging
            return state.clone(); // No change for zero rotation
        }

        match state {
            UnitCircleState::Initial => {
                println!("Transition from Initial to GateOperation"); // Debugging
                UnitCircleState::GateOperation { gate_type: self.gate_type, state: self.angle }
            }
            UnitCircleState::GateOperation { gate_type, state: existing_state } => {
                let new_state = self.angle * existing_state;
                println!("Transition in GateOperation. New State: {:?}", new_state); // Debugging
                UnitCircleState::GateOperation { gate_type: *gate_type, state: new_state }
            }
            _ => {
                println!("State unchanged for state: {:?}", state); // Debugging
                state.clone() // For other states, no change
            }
        }
        
    }
}
