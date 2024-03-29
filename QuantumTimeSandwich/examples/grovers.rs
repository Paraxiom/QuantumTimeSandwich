use std::num::NonZeroUsize;
use QuantumTimeSandwich::builder::Qudit;
use QuantumTimeSandwich::builder_traits::UnitaryBuilder;
use QuantumTimeSandwich::prelude::*;
//-> Result<(), CircuitError>

fn prepare_state<P: Precision>(n: u64) -> Result<(), CircuitError> {
    let mut b = LocalBuilder::<f64>::default();

    let n = NonZeroUsize::new(n as usize).unwrap();
    let r = b.register(n);
    let r = b.h(r);

    let anc = b.qubit();
    let anc = b.not(anc);
    let anc = b.h(anc);

    let r = b.merge_two_registers(r, anc);

    let (_, handle) = b.measure_stochastic(r);

    let (state, measures) = b.calculate_state();
    println!("{:?}", state);
    println!("{:?}", measures.get_stochastic_measurement(handle));
    Ok(())
}
#[cfg(feature = "macros")]
fn apply_us<P: Precision>(
    b: &mut dyn UnitaryBuilder<P>,
    search: Qudit,
    ancillary: Qudit,
    x0: u64,
) -> Result<(Qudit, Qudit), CircuitError> {
    let search = b.h(search);
    let (search, ancillary) = program!(b, search, ancillary, |x| {
        (0, if x == 0 { std::f64::consts::PI } else { 0.0 })
    })?;
    let search = b.h(search);
    Ok((search, ancillary))
}

#[cfg(feature = "macros")]
fn apply_uw(
    b: &mut dyn UnitaryBuilder,
    search: Qudit,
    ancillary: Qudit,
    x0: u64,
) -> Result<(Qudit, Qudit), CircuitError> {
    // Need to move the x0 value into the closure.
    program!(b, search, ancillary, move |x| ((x == x0) as u64, 0.0))
}

#[cfg(feature = "macros")]
fn apply_grover_iteration<P: Precision>(x: u64) -> Result<(), CircuitError> {
    let mut b = LocalBuilder::<f64>::default();

    let n = NonZeroUsize::new(b.n() - 1).unwrap();

    let r = b.register(n);
    let anc = b.qubit();

    let (r, anc) = apply_uw(&mut b, r, anc, x).unwrap();
    let (r, _) = apply_us(&mut b, r, anc).unwrap();

    let (_, measured) = b.calculate_state_with_init([(&r, 0b000), (&anc, 0b001)]);

    Ok(())
}

fn main() {}
