#![feature(test)]

extern crate test;
use bb84::bb84::{alice_step, bob_step, flip_state, generate_bb84_state, measure_bb84_state};
use bb84::bb84_states::{random_bit, MeasurementBasis};
use test::Bencher;
#[bench]
fn bench_generate_bb84_state(b: &mut Bencher) {
    b.iter(|| generate_bb84_state(random_bit(), MeasurementBasis::random()));
}

#[bench]
fn bench_measure_bb84_state_basis1(b: &mut Bencher) {
    let state = generate_bb84_state(random_bit(), MeasurementBasis::random());
    b.iter(|| measure_bb84_state(state, MeasurementBasis::Basis1));
}

// Add more benchmarks for other functions...
#[bench]
fn bench_measure_bb84_state_basis2(b: &mut Bencher) {
    let state = generate_bb84_state(random_bit(), MeasurementBasis::random());
    b.iter(|| measure_bb84_state(state, MeasurementBasis::Basis2));
}

#[bench]
fn bench_alice_step(b: &mut Bencher) {
    b.iter(|| alice_step().unwrap());
}

#[bench]
fn bench_bob_step(b: &mut Bencher) {
    let state = generate_bb84_state(random_bit(), MeasurementBasis::random());
    let alice_message = (random_bit(), MeasurementBasis::Basis1); // Example values
    b.iter(|| bob_step(state, alice_message));
}

#[bench]
fn bench_flip_state(b: &mut Bencher) {
    let state = generate_bb84_state(random_bit(), MeasurementBasis::random());
    b.iter(|| flip_state(state));
}

#[bench]
fn bench_random_bit(b: &mut Bencher) {
    b.iter(|| random_bit());
}
