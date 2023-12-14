// benches/ucsm_benchmarks.rs

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use unit_circle_state_machine::UnitCircleStateMachine;
use unit_circle_state_machine::unit_circle_states::GateType;
use unit_circle_state_machine::UnitCircleState;
use num_complex::Complex;
use std::f64::consts::PI;

fn benchmark_ucsm_operations(c: &mut Criterion) {
    c.bench_function("ucsm_gate_application", |b| {
        let mut state_machine = UnitCircleStateMachine::new();

        b.iter(|| {
            // Example: Applying a PauliX gate
            state_machine.apply_gate(GateType::PauliX);
            // Reset state machine to initial state for next iteration
            state_machine.set_state(UnitCircleState::Initial);
        });
    });

    c.bench_function("ucsm_measurement", |b| {
        let mut state_machine = UnitCircleStateMachine::new();

        b.iter(|| {
            // Example: Simulating a measurement operation
            state_machine.apply_measurement(true);
            // Reset state machine to initial state for next iteration
            state_machine.set_state(UnitCircleState::Initial);
        });
    });

    // Additional benchmarks for other UCSM functionalities can be added here
}

criterion_group!(benches, benchmark_ucsm_operations);
criterion_main!(benches);
