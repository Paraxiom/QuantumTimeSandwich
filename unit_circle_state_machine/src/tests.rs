use crate::unit_circle_states::GateType;
use crate::{Protocol, RotationGate, UnitCircleState, UnitCircleStateMachine};
use num_complex::Complex;
use std::f64::consts::PI;

#[cfg(test)]
mod tests {
    use super::*;
    use num_complex::Complex;
    use std::f64::consts::PI;

    #[test]
    fn test_state_initialization() {
        let state_machine = UnitCircleStateMachine::new();
        assert_eq!(
            *state_machine.current_state(),
            UnitCircleState::default(),
            "State machine should be initialized with the default state"
        );
    }
    #[test]
    fn test_apply_gate() {
        let mut state_machine = UnitCircleStateMachine::new();
        // Set initial state to a GateOperation state
        let initial_state =
            UnitCircleState::gate_operation(GateType::PauliX, Complex::new(1.0, 0.0));
        state_machine.set_state(initial_state.clone());
        let gate = RotationGate::new(Complex::new(PI / 2.0, 0.0), GateType::Hadamard); // Replace GateType::Hadamard with the correct gate type
        state_machine.apply_gate(GateType::PauliX);
        assert_ne!(
            state_machine.current_state(),
            &initial_state,
            "State should change after applying the gate"
        );
    }

    #[test]
    fn test_apply_protocol() {
        let mut state_machine = UnitCircleStateMachine::new();
        let initial_state = state_machine.current_state().clone();
        let protocol = Protocol::new(vec![
            RotationGate::new(Complex::new(PI / 2.0, 0.0), GateType::Hadamard), // Replace GateType::Hadamard with the correct gate type
        ]);
        state_machine.apply_protocol(&protocol);
        assert_ne!(
            state_machine.current_state(),
            &initial_state,
            "State should change after applying the protocol"
        );
    }

    #[test]
    fn test_empty_protocol_application() {
        let mut state_machine = UnitCircleStateMachine::new();
        let initial_state = state_machine.current_state().clone();
        let protocol = Protocol::new(vec![]);
        state_machine.apply_protocol(&protocol);
        assert_eq!(
            state_machine.current_state(),
            &initial_state,
            "State should remain unchanged after applying an empty protocol"
        );
    }

    #[test]
    fn test_protocol_with_multiple_gates() {
        let mut state_machine = UnitCircleStateMachine::new();
        let initial_state = state_machine.current_state().clone();
        let protocol = Protocol::new(vec![
            RotationGate::new(Complex::new(PI / 2.0, 0.0), GateType::Hadamard),
            RotationGate::new(Complex::new(PI / 2.0, 0.0), GateType::Hadamard),
        ]);
        state_machine.apply_protocol(&protocol);
        assert_ne!(
            state_machine.current_state(),
            &initial_state,
            "State should change after applying a protocol with multiple gates"
        );
    }

    fn test_state_consistency() {
        let mut state_machine = UnitCircleStateMachine::new();
        println!(
            "Initial state machine state: {:?}",
            state_machine.current_state()
        ); // Debugging

        // Create a RotationGate object with zero rotation.
        // Note: Replace 'GateType::PauliX' with the appropriate gate type if necessary.
        let zero_rotation_gate = RotationGate::new(Complex::new(0.0, 0.0), GateType::PauliX);

        // Extract the GateType from the RotationGate object.
        // This assumes that RotationGate has a method `get_gate_type()`.
        let gate_type = zero_rotation_gate.get_gate_type();

        // Apply the extracted GateType to the state machine.
        state_machine.apply_gate(gate_type);

        println!(
            "State machine state after zero rotation: {:?}",
            state_machine.current_state()
        ); // Debugging

        // Check if the state remains unchanged after applying a zero rotation gate.
        assert_eq!(
            state_machine.current_state(),
            &UnitCircleState::Initial,
            "State should remain unchanged after applying a zero rotation gate"
        );
    }
}
