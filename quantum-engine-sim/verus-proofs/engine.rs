//! Verus formal verification: Engine cycle thermodynamic bounds.
//!
//! Proves:
//!   - Work of compression ≥ 0
//!   - Protection factor ∈ (0, 1]
//!   - Efficiency ∈ [0, 1] given valid inputs
//!   - Protection monotone in spectral gap
//!   - Work symmetric
//!
//! Mirrors: engine.rs:187 (run_cycle)
//! Tier 2 verification (Kani → **Verus** → Lean 4).

use vstd::prelude::*;

verus! {

pub uninterp spec fn exp(x: real) -> real;

#[verifier::external_body]
pub proof fn exp_positive(x: real)
    ensures exp(x) > 0real,
{}

#[verifier::external_body]
pub proof fn exp_leq_one_nonpositive(x: real)
    requires x <= 0real,
    ensures exp(x) <= 1real,
{}

#[verifier::external_body]
pub proof fn exp_monotone(a: real, b: real)
    requires a < b,
    ensures exp(a) < exp(b),
{}

// ── Arithmetic helpers ──

/// a < 0, b > 0 → a/b < 0
#[verifier::external_body]
pub proof fn div_neg_pos(a: real, b: real)
    requires a < 0real, b > 0real,
    ensures a / b < 0real,
{}

/// a > 0, 0 < b1 < b2 → a/b2 < a/b1
#[verifier::external_body]
pub proof fn div_pos_denom_increasing(a: real, b1: real, b2: real)
    requires a > 0real, 0real < b1, b1 < b2,
    ensures a / b2 < a / b1,
{}

/// 0 <= a <= b, c > 0 → a/c <= b/c
#[verifier::external_body]
pub proof fn div_numerator_le(a: real, b: real, c: real)
    requires 0real <= a, a <= b, c > 0real,
    ensures a / c <= b / c,
{}

/// a >= 0, c > 0 → a/c >= 0
#[verifier::external_body]
pub proof fn div_nonneg_pos(a: real, c: real)
    requires a >= 0real, c > 0real,
    ensures a / c >= 0real,
{}

/// a < b, c > 0 → a/c < b/c
#[verifier::external_body]
pub proof fn div_strict_numerator(a: real, b: real, c: real)
    requires a < b, c > 0real,
    ensures a / c < b / c,
{}

/// a > 0 → a/a == 1
#[verifier::external_body]
pub proof fn div_self(a: real)
    requires a > 0real,
    ensures a / a == 1real,
{}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Spec functions
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub open spec fn work_compression(e_max: real, e_min: real) -> real {
    if e_min - e_max >= 0real { e_min - e_max } else { e_max - e_min }
}

pub open spec fn protection_factor(gap: real, gamma_norm: real) -> real {
    exp(-gap / gamma_norm)
}

pub open spec fn efficiency(net_work: real, work_comp: real) -> real {
    net_work / work_comp
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 1: Work ≥ 0
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn work_non_negative(e_max: real, e_min: real)
    ensures work_compression(e_max, e_min) >= 0real,
{}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 2: Protection ∈ (0, 1]
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn protection_bounded(gap: real, gamma_norm: real)
    requires gap > 0real, gamma_norm > 0real,
    ensures
        protection_factor(gap, gamma_norm) > 0real,
        protection_factor(gap, gamma_norm) <= 1real,
{
    div_neg_pos(-gap, gamma_norm);
    let arg = -gap / gamma_norm;
    assert(arg < 0real);
    exp_positive(arg);
    exp_leq_one_nonpositive(arg);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 3: Larger gap → smaller protection factor
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn protection_monotone(gap1: real, gap2: real, gamma_norm: real)
    requires 0real < gap1, gap1 < gap2, gamma_norm > 0real,
    ensures
        protection_factor(gap2, gamma_norm) < protection_factor(gap1, gamma_norm),
{
    // -gap2 < -gap1 < 0, gamma_norm > 0
    // -gap2/gn < -gap1/gn (both negative, dividing by positive preserves order)
    assert(-gap2 < -gap1);
    div_strict_numerator(-gap2, -gap1, gamma_norm);
    // -gap2/gn < -gap1/gn
    exp_monotone(-gap2 / gamma_norm, -gap1 / gamma_norm);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 4: Efficiency bounded
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn efficiency_bounded(net_work: real, work_comp: real)
    requires work_comp > 0real, 0real <= net_work, net_work <= work_comp,
    ensures
        efficiency(net_work, work_comp) >= 0real,
        efficiency(net_work, work_comp) <= 1real,
{
    // 0 <= net_work → net_work / work_comp >= 0
    div_nonneg_pos(net_work, work_comp);
    // net_work <= work_comp → net_work / work_comp <= work_comp / work_comp
    div_numerator_le(net_work, work_comp, work_comp);
    // work_comp / work_comp = 1
    div_self(work_comp);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 5: Work is symmetric
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn work_symmetric(e1: real, e2: real)
    ensures work_compression(e1, e2) == work_compression(e2, e1),
{}

} // verus!

fn main() {}
