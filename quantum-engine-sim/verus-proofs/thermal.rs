//! Verus formal verification: Bose-Einstein thermal occupation properties.
//!
//! Proves functional correctness of n_th = 1/(exp(x) - 1):
//!   - Non-negativity for x > 0
//!   - Monotonicity: decreasing in x
//!   - Temperature monotonicity: higher T → higher n_th
//!   - Upper bound: n_th ≤ 1/x
//!   - Zero-temperature limit: n_th → 0
//!
//! Mirrors: vacuum.rs:83 (thermal_occupation)
//! Tier 2 verification (Kani → **Verus** → Lean 4).

use vstd::prelude::*;

verus! {

pub uninterp spec fn exp(x: real) -> real;

#[verifier::external_body]
pub proof fn exp_positive(x: real)
    ensures exp(x) > 0real,
{}

#[verifier::external_body]
pub proof fn exp_monotone(a: real, b: real)
    requires a < b,
    ensures exp(a) < exp(b),
{}

#[verifier::external_body]
pub proof fn exp_gt_one_positive(x: real)
    requires x > 0real,
    ensures exp(x) > 1real,
{}

#[verifier::external_body]
pub proof fn exp_lower_bound(x: real)
    requires x > 0real,
    ensures exp(x) >= 1real + x,
{}

// ── Arithmetic helpers (trusted) ──

#[verifier::external_body]
pub proof fn div_pos_pos(a: real, b: real)
    requires a > 0real, b > 0real,
    ensures a / b > 0real,
{}

#[verifier::external_body]
pub proof fn div_pos_denom_increasing(a: real, b1: real, b2: real)
    requires a > 0real, 0real < b1, b1 < b2,
    ensures a / b2 < a / b1,
{}

#[verifier::external_body]
pub proof fn div_pos_le(a: real, b: real, c: real)
    requires a > 0real, c > 0real, b >= c,
    ensures a / b <= a / c,
{}

#[verifier::external_body]
pub proof fn mul_pos_pos(a: real, b: real)
    requires a > 0real, b > 0real,
    ensures a * b > 0real,
{}

#[verifier::external_body]
pub proof fn mul_pos_strict(a: real, b1: real, b2: real)
    requires a > 0real, 0real < b1, b1 < b2,
    ensures a * b1 < a * b2,
{}

/// a > 0, a*b > 1 → 1/a < b
#[verifier::external_body]
pub proof fn recip_lt_from_product(a: real, b: real)
    requires a > 0real, a * b > 1real,
    ensures 1real / a < b,
{}

/// a <= b < c → a < c (transitivity with ≤ and <)
#[verifier::external_body]
pub proof fn le_lt_trans(a: real, b: real, c: real)
    requires a <= b, b < c,
    ensures a < c,
{}

/// n_th = 1/(exp(x) - 1)
pub open spec fn bose_einstein(x: real) -> real {
    1real / (exp(x) - 1real)
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 1: n_th > 0 for x > 0
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn thermal_non_negative(x: real)
    requires x > 0real,
    ensures bose_einstein(x) > 0real,
{
    exp_gt_one_positive(x);
    div_pos_pos(1real, exp(x) - 1real);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 2: n_th decreasing in x
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn thermal_decreasing_in_x(x1: real, x2: real)
    requires 0real < x1, x1 < x2,
    ensures bose_einstein(x1) > bose_einstein(x2),
{
    exp_gt_one_positive(x1);
    exp_gt_one_positive(x2);
    exp_monotone(x1, x2);
    let d1 = exp(x1) - 1real;
    let d2 = exp(x2) - 1real;
    assert(0real < d1);
    assert(d1 < d2);
    div_pos_denom_increasing(1real, d1, d2);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 3: Higher temperature → higher occupation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// For fixed ω,ℏ,k_B: T₁ < T₂ → n_th(T₁) < n_th(T₂).
/// Since direct composition thermal_x → bose_einstein is hard for Z3,
/// we state the result in terms of x values directly.
pub proof fn thermal_monotone_in_x_values(x_cold: real, x_hot: real)
    requires
        0real < x_hot,
        x_hot < x_cold,
    ensures
        bose_einstein(x_cold) < bose_einstein(x_hot),
{
    thermal_decreasing_in_x(x_hot, x_cold);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 4: Upper bound n_th ≤ 1/x
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub proof fn thermal_upper_bound(x: real)
    requires x > 0real,
    ensures bose_einstein(x) <= 1real / x,
{
    exp_lower_bound(x);
    exp_gt_one_positive(x);
    let d = exp(x) - 1real;
    assert(d >= x);
    assert(d > 0real);
    div_pos_le(1real, d, x);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Proof 5: Zero-temperature limit (quantitative)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// For x > 1/ε: n_th(x) ≤ 1/x < ε.
/// Combined with T→0 giving x→∞, this shows n_th vanishes.
pub proof fn thermal_vanishes_bound(x: real, epsilon: real)
    requires
        epsilon > 0real,
        x > 0real,
        x * epsilon > 1real,
    ensures
        bose_einstein(x) < epsilon,
{
    thermal_upper_bound(x);
    // bose_einstein(x) <= 1/x
    recip_lt_from_product(x, epsilon);
    // 1/x < epsilon
    le_lt_trans(bose_einstein(x), 1real / x, epsilon);
}

} // verus!

fn main() {}
