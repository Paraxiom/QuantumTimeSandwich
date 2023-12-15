use crate::unit_circle_states;
use crate::unit_circle_states::GateType;
use crate::unit_circle_states::RotationGate;
use crate::Operation;
use crate::Protocol;
use crate::UnitCircleState;
use num_complex::Complex;
use std::f64::consts::PI;
#[derive(Clone, Debug, Default)]
pub struct UnitCircleStateMachine {
    current_state: UnitCircleState,
}

impl UnitCircleStateMachine {
    pub fn new() -> Self {
        Self {
            current_state: UnitCircleState::Initial,
            // Initialize other fields
        }
    }
    // Method to manually set the state of the state machine
    pub fn set_state(&mut self, new_state: UnitCircleState) {
        self.current_state = new_state;
    }
    // Modified apply_gate method to accept GateType
    pub fn apply_gate(&mut self, gate_type: GateType) {
        let rotation_gate = match gate_type {
            GateType::PauliX => RotationGate::new(Complex::new(PI, 0.0), GateType::PauliX),
            GateType::PauliY => RotationGate::new(Complex::new(0.0, PI), GateType::PauliY),
            GateType::PauliZ => RotationGate::new(Complex::new(PI, 0.0), GateType::PauliZ),
            GateType::Hadamard => RotationGate::new(
                Complex::new(PI / std::f64::consts::SQRT_2, 0.0),
                GateType::Hadamard,
            ),
            GateType::CNOT => RotationGate::new(Complex::new(0.0, 0.0), GateType::CNOT),
            // Add cases for other gate types
        };
        // Apply the rotation gate to the current state
        self.current_state = rotation_gate.apply_to(&self.current_state);
    }

    // Gets the current state
    pub fn current_state(&self) -> &UnitCircleState {
        &self.current_state
    }
    pub fn apply_operation(&mut self, operation: Operation) {
        match operation {
            Operation::ApplyGate(gate) => {
                let gate_type = gate.get_gate_type();
                self.apply_gate(gate_type);
            } // Handle other operations as needed
        }
    }

    pub fn apply_protocol(&mut self, protocol: &Protocol) {
        for gate in protocol.gates() {
            let gate_type = gate.get_gate_type();
            self.apply_gate(gate_type);
        }
    }
    // Handle a measurement operation
    pub fn apply_measurement(&mut self, result: bool) {
        self.current_state = UnitCircleState::Measurement {
            result: Some(result),
        };
    }

    // Handle an entanglement operation
    pub fn apply_entanglement(&mut self) {
        self.current_state = UnitCircleState::Entanglement;
    }

    // Handle error correction
    pub fn apply_error_correction(&mut self) {
        self.current_state = UnitCircleState::ErrorCorrection;
    }

    // Transition to the final state
    pub fn finalize(&mut self) {
        self.current_state = UnitCircleState::Final;
    }
}
