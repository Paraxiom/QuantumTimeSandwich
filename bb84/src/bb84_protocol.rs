/// Applies the given gates to the given unit circle state and returns the resulting state.
pub fn unit_circle_state_machine_protocol(state: UnitCircleState, gates: Vec<RotationGate>) -> UnitCircleState {
    // Apply the gates to the state.
    for gate in gates {
        state = gate * state;
    }

    // Return the final state.
    return state;
}
