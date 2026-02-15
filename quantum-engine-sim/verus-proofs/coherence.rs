//! Verus formal verification: Coherence time properties.
//!
//! Proves functional correctness of τ = -ln(ε)/λ₁:
//!   - Positivity when λ₁ > 0 and 0 < ε < 1
//!   - Monotonicity: larger spectral gap → shorter coherence time
//!   - Tonnetz enhancement: enhanced_t2 ≥ bare_t2
//!
//! Mirrors: coherence.rs:72, coherence.rs:136
//! Tier 2 verification (Kani → **Verus** → Lean 4).

use vstd::prelude::*;

verus! {

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Axiomatized transcendentals
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub uninterp spec fn ln(x: real) -> real;
pub uninterp spec fn exp(x: real) -> real;
pub uninterp spec fn cos(x: real) -> real;
pub uninterp spec fn TWO_PI() -> real;

#[verifier::external_body]
pub proof fn two_pi_positive()
    ensures TWO_PI() > 0real,
{}

/// ln(x) < 0 for 0 < x < 1.
#[verifier::external_body]
pub proof fn ln_negative_below_one(x: real)
    requires 0real < x, x < 1real,
    ensures ln(x) < 0real,
{}

/// ln is strictly increasing.
#[verifier::external_body]
pub proof fn ln_monotone(a: real, b: real)
    requires 0real < a, a < b,
    ensures ln(a) < ln(b),
{}

/// exp(x) > 0.
#[verifier::external_body]
pub proof fn exp_positive(x: real)
    ensures exp(x) > 0real,
{}

/// cos < 1 for 0 < x < 2π.
#[verifier::external_body]
pub proof fn cos_strict_less_one(x: real)
    requires 0real < x, x < TWO_PI(),
    ensures cos(x) < 1real,
{}

// ── Arithmetic helpers (trusted, Z3 nonlinear workarounds) ──

/// a > 0, b > 0 → a/b > 0
#[verifier::external_body]
pub proof fn div_pos_pos(a: real, b: real)
    requires a > 0real, b > 0real,
    ensures a / b > 0real,
{}

/// a > 0, 0 < b1 < b2 → a/b2 < a/b1
#[verifier::external_body]
pub proof fn div_pos_denom_increasing(a: real, b1: real, b2: real)
    requires a > 0real, 0real < b1, b1 < b2,
    ensures a / b2 < a / b1,
{}

/// a > 0, b >= 2 → a/b < a
#[verifier::external_body]
pub proof fn div_shrinks(a: real, b: real)
    requires a > 0real, b >= 2real,
    ensures a / b < a,
{}

/// a > b, c > 0 → a/c > b/c
#[verifier::external_body]
pub proof fn div_numerator_order(a: real, b: real, c: real)
    requires a > b, c > 0real,
    ensures a / c > b / c,
{}

/// a > 0, b > 0, c > 0 → a*b*c > 0
#[verifier::external_body]
pub proof fn mul_pos_pos_pos(a: real, b: real, c: real)
    requires a > 0real, b > 0real, c > 0real,
    ensures a * b * c > 0real,
{}

/// a > 0, b >= 1 → a*b >= a
#[verifier::external_body]
pub proof fn mul_ge_one(a: real, b: real)
    requires a > 0real, b >= 1real,
    ensures a * b >= a,
{}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Spec functions
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// τ = -ln(ε) / λ₁
pub open spec fn coherence_time(gap: real, threshold: real) -> real {
    -ln(threshold) / gap
}

/// λ₁ = 2 - 2cos(2π/N)
pub open spec fn spectral_gap(n: int) -> real {
    2real - 2real * cos(TWO_PI() / (n as real))
}

/// Enhancement = 1 + 2Q·exp(-1)/λ₁
pub open spec fn enhancement_factor(quality: real, gap: real) -> real {
    1real + 2real * quality * exp(-1real) / gap
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 1: Coherence time is positive
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn coherence_time_positive(gap: real, threshold: real)
    requires gap > 0real, 0real < threshold, threshold < 1real,
    ensures coherence_time(gap, threshold) > 0real,
{
    ln_negative_below_one(threshold);
    // -ln(threshold) > 0
    div_pos_pos(-ln(threshold), gap);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 2: Larger gap → shorter coherence time
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn coherence_time_monotone(gap1: real, gap2: real, threshold: real)
    requires 0real < gap1, gap1 < gap2, 0real < threshold, threshold < 1real,
    ensures coherence_time(gap1, threshold) > coherence_time(gap2, threshold),
{
    ln_negative_below_one(threshold);
    let neg_ln_t = -ln(threshold);
    assert(neg_ln_t > 0real);
    // neg_ln_t > 0, 0 < gap1 < gap2 → neg_ln_t/gap2 < neg_ln_t/gap1
    div_pos_denom_increasing(neg_ln_t, gap1, gap2);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 3: Tighter threshold → longer coherence time
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn coherence_time_threshold_monotone(gap: real, eps1: real, eps2: real)
    requires gap > 0real, 0real < eps1, eps1 < eps2, eps2 < 1real,
    ensures coherence_time(gap, eps1) > coherence_time(gap, eps2),
{
    ln_monotone(eps1, eps2);
    ln_negative_below_one(eps1);
    ln_negative_below_one(eps2);
    // ln(eps1) < ln(eps2) < 0
    // -ln(eps1) > -ln(eps2) > 0
    let a = -ln(eps1);
    let b = -ln(eps2);
    assert(a > 0real);
    assert(b > 0real);
    assert(a > b);
    // a > b > 0, gap > 0 → a/gap > b/gap
    div_numerator_order(a, b, gap);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 4: Tonnetz enhancement ≥ 1
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn tonnetz_enhancement_at_least_one(quality: real, gap: real)
    requires quality > 0real, gap > 0real,
    ensures enhancement_factor(quality, gap) >= 1real,
{
    exp_positive(-1real);
    let e = exp(-1real);
    assert(e > 0real);
    // 2 * quality * e > 0
    mul_pos_pos_pos(2real, quality, e);
    let num = 2real * quality * e;
    assert(num > 0real);
    // num / gap > 0
    div_pos_pos(num, gap);
    // 1 + positive >= 1
}

/// Enhanced T₂ ≥ bare T₂.
pub proof fn tonnetz_enhanced_t2_geq_bare(t2_bare: real, quality: real, gap: real)
    requires t2_bare > 0real, quality > 0real, gap > 0real,
    ensures t2_bare * enhancement_factor(quality, gap) >= t2_bare,
{
    tonnetz_enhancement_at_least_one(quality, gap);
    mul_ge_one(t2_bare, enhancement_factor(quality, gap));
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 5: Coherence time from torus spectral gap
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn torus_coherence_time_positive(n: int, threshold: real)
    requires n >= 2, 0real < threshold, threshold < 1real,
    ensures coherence_time(spectral_gap(n), threshold) > 0real,
{
    two_pi_positive();
    let theta = TWO_PI() / (n as real);
    div_pos_pos(TWO_PI(), n as real);
    div_shrinks(TWO_PI(), n as real);
    cos_strict_less_one(theta);
    // spectral_gap(n) > 0
    coherence_time_positive(spectral_gap(n), threshold);
}

} // verus!

fn main() {}
