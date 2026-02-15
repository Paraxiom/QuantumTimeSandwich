# Verus formal verification for quantum-engine-sim
#
# Tier 2 of 3-tier verification: Kani (panic-freedom) → Verus (functional correctness) → Lean 4
#
# Prerequisites:
#   1. Download Verus from https://github.com/verus-lang/verus/releases
#   2. Extract to ~/.verus/ (or set VERUS_HOME below)
#   3. Run: make all
#
# Each .rs file is self-contained and compiled independently by Verus.

VERUS_HOME ?= $(HOME)/.verus
VERUS      ?= $(VERUS_HOME)/verus

# All proof files
PROOFS = spectral_gap distance coherence thermal engine

.PHONY: all clean check install-check $(PROOFS)

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# Targets
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

all: install-check $(PROOFS)
	@echo ""
	@echo "═══════════════════════════════════════════════════════════════"
	@echo "  All Verus proofs verified successfully!"
	@echo "  Tier 2 (functional correctness) ✓"
	@echo "═══════════════════════════════════════════════════════════════"

install-check:
	@if [ ! -x "$(VERUS)" ]; then \
		echo "Error: Verus not found at $(VERUS)"; \
		echo "Install: download from https://github.com/verus-lang/verus/releases"; \
		echo "Extract to ~/.verus/ or set VERUS_HOME=<path>"; \
		exit 1; \
	fi

# Individual proof targets
spectral_gap:
	@echo "── Verifying spectral_gap.rs (torus spectral gap properties)..."
	$(VERUS) spectral_gap.rs
	@echo "   ✓ spectral_gap: 5 verified"

distance:
	@echo "── Verifying distance.rs (toroidal distance metric axioms)..."
	$(VERUS) distance.rs
	@echo "   ✓ distance: 8 verified"

coherence:
	@echo "── Verifying coherence.rs (coherence time properties)..."
	$(VERUS) coherence.rs
	@echo "   ✓ coherence: 6 verified"

thermal:
	@echo "── Verifying thermal.rs (Bose-Einstein occupation)..."
	$(VERUS) thermal.rs
	@echo "   ✓ thermal: 5 verified"

engine:
	@echo "── Verifying engine.rs (engine cycle bounds)..."
	$(VERUS) engine.rs
	@echo "   ✓ engine: 5 verified"

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# Utilities
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

clean:
	@echo "Nothing to clean (Verus produces no artifacts)"

# Quick check: just verify the pure-integer distance proofs (no axioms)
check:
	@echo "Quick check: distance.rs (pure integer, no axiom trust)..."
	$(VERUS) distance.rs
	@echo "   ✓ distance proofs verified (zero trusted axioms)"

# Summary of proof counts
summary:
	@echo ""
	@echo "Verus Proof Summary (Tier 2: Functional Correctness)"
	@echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
	@echo "  spectral_gap.rs:  5 verified (theta range, positivity, bounds, monotone, degenerate)"
	@echo "  distance.rs:      8 verified (circ symmetric/bounded/triangle, dist symmetric/identity/bounded/triangle/nondegenerate)"
	@echo "  coherence.rs:     6 verified (positive, monotone-gap, monotone-threshold, enhancement≥1, enhanced-T2, torus-positive)"
	@echo "  thermal.rs:       5 verified (non-negative, decreasing, monotone-T, upper-bound, vanishing)"
	@echo "  engine.rs:        5 verified (work≥0, protection∈(0,1], protection-monotone, efficiency∈[0,1], work-symmetric)"
	@echo "  ─────────────────────────────────────"
	@echo "  Total:           29 verified, 0 errors"
	@echo ""
	@echo "  Trusted axioms:  cos (bounded, cos(0)=1, cos(2π)=1, <1 on (0,2π), decreasing on [0,π])"
	@echo "                   ln (negative below 1, monotone)"
	@echo "                   exp (positive, monotone, exp(0)=1, ≤1 for x≤0, ≥1+x for x>0)"
	@echo "                   arithmetic (div/mul ordering for nonlinear Z3)"
	@echo ""
	@echo "  Axiom-free:      distance.rs (8 verified, pure integer arithmetic)"
