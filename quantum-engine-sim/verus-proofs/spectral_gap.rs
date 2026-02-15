//! Verus formal verification: Spectral gap properties on T².
//!
//! Proves functional correctness of λ₁ = 2 - 2cos(2π/N):
//!   - Positivity for N ≥ 2
//!   - Bounds: 0 < λ₁ ≤ 4
//!   - Monotonicity: λ₁(N+1) < λ₁(N)
//!
//! Uses Verus `real` type for exact mathematical reasoning.
//! Tier 2 verification (Kani → **Verus** → Lean 4).

use vstd::prelude::*;

verus! {

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Axiomatized transcendental: cos on reals
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub uninterp spec fn cos(x: real) -> real;

// Uninterpreted constants with axioms
pub uninterp spec fn TWO_PI() -> real;
pub uninterp spec fn PI_VAL() -> real;

#[verifier::external_body]
pub proof fn two_pi_positive()
    ensures TWO_PI() > 0real,
{}

#[verifier::external_body]
pub proof fn pi_positive()
    ensures PI_VAL() > 0real,
{}

#[verifier::external_body]
pub proof fn two_pi_is_2_pi()
    ensures TWO_PI() == 2real * PI_VAL(),
{}

/// Trusted axiom: cos is bounded in [-1, 1].
#[verifier::external_body]
pub proof fn cos_bounded(x: real)
    ensures -1real <= cos(x), cos(x) <= 1real,
{}

/// Trusted axiom: cos(0) = 1.
#[verifier::external_body]
pub proof fn cos_zero()
    ensures cos(0real) == 1real,
{}

/// Trusted axiom: cos(2π) = 1 (periodicity).
#[verifier::external_body]
pub proof fn cos_two_pi()
    ensures cos(TWO_PI()) == 1real,
{}

/// Trusted axiom: cos < 1 for 0 < x < 2π.
#[verifier::external_body]
pub proof fn cos_strict_less_one(x: real)
    requires 0real < x, x < TWO_PI(),
    ensures cos(x) < 1real,
{}

/// Trusted axiom: cos is decreasing on [0, π].
#[verifier::external_body]
pub proof fn cos_decreasing_0_pi(a: real, b: real)
    requires 0real <= a, a < b, b <= PI_VAL(),
    ensures cos(a) > cos(b),
{}

/// Trusted: for a > 0, b > 0: a/b > 0.
#[verifier::external_body]
pub proof fn div_pos_pos(a: real, b: real)
    requires a > 0real, b > 0real,
    ensures a / b > 0real,
{}

/// Trusted: for a > 0, 0 < b1 < b2: a/b2 < a/b1.
#[verifier::external_body]
pub proof fn div_pos_denom_increasing(a: real, b1: real, b2: real)
    requires a > 0real, 0real < b1, b1 < b2,
    ensures a / b2 < a / b1,
{}

/// Trusted: for a > 0, b >= 2: a/b <= a/2.
#[verifier::external_body]
pub proof fn div_bound_ge_2(a: real, b: real)
    requires a > 0real, b >= 2real,
    ensures a / b <= a / 2real,
{}

/// Trusted: for a > 0, b >= 2: a/b < a.
#[verifier::external_body]
pub proof fn div_shrinks(a: real, b: real)
    requires a > 0real, b >= 2real,
    ensures a / b < a,
{}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Spec: spectral gap
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub open spec fn spectral_gap(n: int) -> real
    recommends n >= 2
{
    2real - 2real * cos(TWO_PI() / (n as real))
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Helper: 2π/N is in (0, π] for N ≥ 2
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

proof fn theta_in_range(n: int)
    requires n >= 2,
    ensures
        TWO_PI() / (n as real) > 0real,
        TWO_PI() / (n as real) <= PI_VAL(),
        TWO_PI() / (n as real) < TWO_PI(),
{
    two_pi_positive();
    two_pi_is_2_pi();
    pi_positive();

    let nr = n as real;
    assert(nr >= 2real);

    // TWO_PI() > 0 and n >= 2 > 0 → TWO_PI()/n > 0
    div_pos_pos(TWO_PI(), nr);

    // TWO_PI()/n ≤ TWO_PI()/2 = PI_VAL()
    div_bound_ge_2(TWO_PI(), nr);
    // TWO_PI()/nr <= TWO_PI()/2 = 2*PI_VAL()/2 = PI_VAL()

    // TWO_PI()/n < TWO_PI() (since n >= 2)
    div_shrinks(TWO_PI(), nr);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 1: spectral_gap > 0 for N ≥ 2
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn spectral_gap_positive(n: int)
    requires n >= 2,
    ensures spectral_gap(n) > 0real,
{
    let theta = TWO_PI() / (n as real);
    theta_in_range(n);
    cos_strict_less_one(theta);
    // cos(theta) < 1 → 2*cos(theta) < 2 → -2*cos(theta) > -2 → 2-2*cos(theta) > 0
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 2: 0 < λ₁ ≤ 4
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn spectral_gap_bounded(n: int)
    requires n >= 2,
    ensures spectral_gap(n) > 0real, spectral_gap(n) <= 4real,
{
    let theta = TWO_PI() / (n as real);
    spectral_gap_positive(n);
    cos_bounded(theta);
    // cos(theta) >= -1 → 2*cos(theta) >= -2 → -2cos(theta) <= 2 → 2-2cos <= 4
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 3: monotonically decreasing in N
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn spectral_gap_monotone(n: int)
    requires n >= 2,
    ensures spectral_gap(n + 1) < spectral_gap(n),
{
    let nr = n as real;
    let nr1 = (n + 1) as real;
    let theta_n = TWO_PI() / nr;
    let theta_n1 = TWO_PI() / nr1;

    two_pi_positive();
    two_pi_is_2_pi();
    pi_positive();

    assert(nr >= 2real);
    assert(nr1 > nr);
    assert(nr1 > 0real);

    // theta_n1 < theta_n: TWO_PI/(n+1) < TWO_PI/n
    div_pos_denom_increasing(TWO_PI(), nr, nr1);

    // theta_n1 > 0
    div_pos_pos(TWO_PI(), nr1);

    // theta_n <= PI (from theta_in_range)
    theta_in_range(n);

    // cos decreasing: cos(theta_n1) > cos(theta_n) since 0 < theta_n1 < theta_n ≤ π
    cos_decreasing_0_pi(theta_n1, theta_n);
    // cos(theta_n1) > cos(theta_n)
    // → 2cos(theta_n1) > 2cos(theta_n)
    // → -2cos(theta_n1) < -2cos(theta_n)
    // → 2-2cos(theta_n1) < 2-2cos(theta_n)
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 4: spectral gap at N=1 is zero
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn spectral_gap_zero_at_one()
    ensures
        2real - 2real * cos(TWO_PI() / (1int as real)) == 0real,
{
    cos_two_pi();
    assert(1int as real == 1real);
    assert(TWO_PI() / 1real == TWO_PI());
}

} // verus!

fn main() {}
