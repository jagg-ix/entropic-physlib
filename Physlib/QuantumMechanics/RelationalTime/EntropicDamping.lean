/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.PageWootters
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Entropic-rate decomposition and imaginary-action damping

Two scalar companions to the dissipative Page–Wootters material in
`Physlib.QuantumMechanics.RelationalTime.PageWootters`:

## §1 — Effective entropic-rate decomposition

In a non-inertial (Fermi) frame the effective entropic rate splits into a
clock-imperfection term, an acceleration (Unruh) term, and a geometric
(rotation/curvature) term:

 `λ_total = (ΔH_C/ℏ)² + κ/(2π) + (geometric)`.

`EntropicRateDecomposition` includes the three physical inputs with their
non-negativity, and the module proves that `λ_total` is non-negative and
dominates each contribution, vanishing exactly when all three vanish.

**Scope.** This formalises *only* the structural fact that `λ_total`
is a sum of three non-negative contributions that dominates each. It does
**not** formalise the source text's claimed `ΔH_C → ∞ ⇒ λ = 0` limit: as
written, the clock term `(ΔH_C/ℏ)²` *grows* with `ΔH_C`, so that limit is in
tension with the decomposition. The intended "sharper clock ⇒ smaller floor"
monotonicity needs the inverse time-resolution identification
`Δt ~ ℏ/ΔH_C` and is deliberately left to consumers rather than asserted here.

## §2 — Imaginary-action amplitude damping

For an open conditional state with imaginary action `S_I ≥ 0`, the
Page–Wootters conditional amplitude has a real damping factor
`exp(−S_I/(2ℏ))`, squaring to the probability damping `exp(−S_I/ℏ)`. This is
the modulus counterpart of the unitary phase `−E_S·t/ℏ`; together they give
the full conditional-state factorisation, and the squared form is the
Cameron–Martin path weight `W = exp(−τ_ent)` with `S_I = τ_ent·ℏ` (cf.
`Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrame`, where
`W = 1 ⟺ λ = 0`).

**Origin.** §2 is a self-contained re-derivation, in physlib idiom and with
no external dependency, of the dissipative-amplitude factor of a Page–Wootters
conditional state under a GKSL/Lindblad generator (Lindblad 1976; Breuer &
Petruccione 2002, §3.2). The unitary base is Page & Wootters 1983; the
`S_I ≥ 0` positivity of the imaginary action is the load-bearing assumption.

## References

- Page & Wootters 1983, *Evolution without evolution*, Phys. Rev. D 27, 2885,
 doi:10.1103/PhysRevD.27.2885.
- Lindblad 1976, *On the generators of quantum dynamical semigroups*,
 Commun. Math. Phys. 48, 119, doi:10.1007/BF01608499 — the dissipative
 (GKSL) generator behind the `exp(−S_I/(2ℏ))` amplitude factor.
- Breuer & Petruccione 2002, *The Theory of Open Quantum Systems*, Oxford
 University Press, doi:10.1093/acprof:oso/9780199213900.001.0001, §3.2 —
 open-system amplitude and probability damping.
- Gambini, Porto & Pullin 2004, *A relational solution to the problem of time*,
 New J. Phys. 6, 45, doi:10.1088/1367-2630/6/1/045 — fundamental decoherence
 from imperfect clocks.
- Unruh 1976, *Notes on black-hole evaporation*, Phys. Rev. D 14, 870,
 doi:10.1103/PhysRevD.14.870 — the `κ/(2π)` acceleration term.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.RelationalTime

/-! ## §1 — Effective entropic-rate decomposition -/

/-- **Additive decomposition of the effective entropic rate** in a non-inertial
(Fermi) frame.  Includes the clock energy spread `ΔH_C ≥ 0`, the acceleration
parameter `κ ≥ 0` (Unruh), and a geometric contribution `≥ 0`, with `ℏ > 0`. -/
structure EntropicRateDecomposition where
  /-- Reduced Planck constant. -/
  ℏ : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ
  /-- Clock energy spread (standard deviation, `≥ 0`). -/
  ΔH_C : ℝ
  /-- `ΔH_C ≥ 0`. -/
  ΔH_C_nonneg : 0 ≤ ΔH_C
  /-- Acceleration / surface-gravity parameter (Unruh, `≥ 0`). -/
  κ : ℝ
  /-- `κ ≥ 0`. -/
  κ_nonneg : 0 ≤ κ
  /-- Geometric (rotation/curvature) contribution. -/
  geometric : ℝ
  /-- `geometric ≥ 0`. -/
  geometric_nonneg : 0 ≤ geometric

namespace EntropicRateDecomposition

variable (D : EntropicRateDecomposition)

/-- Clock-imperfection contribution `(ΔH_C/ℏ)²`. -/
def clockRate : ℝ := (D.ΔH_C / D.ℏ) ^ 2

/-- Acceleration (Unruh) contribution `κ/(2π)`. -/
def unruhRate : ℝ := D.κ / (2 * Real.pi)

/-- Total effective entropic rate `λ_total = clockRate + unruhRate + geometric`. -/
def total : ℝ := D.clockRate + D.unruhRate + D.geometric

theorem clockRate_nonneg : 0 ≤ D.clockRate := by
  unfold clockRate; positivity

theorem unruhRate_nonneg : 0 ≤ D.unruhRate := by
  unfold unruhRate
  exact div_nonneg D.κ_nonneg (by positivity)

theorem total_nonneg : 0 ≤ D.total :=
  add_nonneg (add_nonneg D.clockRate_nonneg D.unruhRate_nonneg) D.geometric_nonneg

theorem clockRate_le_total : D.clockRate ≤ D.total := by
  unfold total; linarith [D.unruhRate_nonneg, D.geometric_nonneg]

theorem unruhRate_le_total : D.unruhRate ≤ D.total := by
  unfold total; linarith [D.clockRate_nonneg, D.geometric_nonneg]

theorem geometric_le_total : D.geometric ≤ D.total := by
  unfold total; linarith [D.clockRate_nonneg, D.unruhRate_nonneg]

/-- **The total rate vanishes iff every contribution vanishes.** -/
theorem total_eq_zero_iff :
    D.total = 0 ↔ D.clockRate = 0 ∧ D.unruhRate = 0 ∧ D.geometric = 0 := by
  have hc := D.clockRate_nonneg
  have hu := D.unruhRate_nonneg
  have hg := D.geometric_nonneg
  simp only [total]
  constructor
  · intro h; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; rw [h1, h2, h3]; ring

end EntropicRateDecomposition

/-! ## §2 — Imaginary-action amplitude damping

Re-derivation, self-contained in physlib, of the dissipative Page–Wootters
amplitude lemmas (see module header for origin). -/

/-- **Imaginary-action damping** of an open conditional state: Planck constant
`ℏ > 0` and imaginary action `S_I ≥ 0`. -/
structure ImaginaryActionDamping where
  /-- Reduced Planck constant. -/
  ℏ : ℝ
  /-- `ℏ > 0`. -/
  ℏ_pos : 0 < ℏ
  /-- Imaginary action accumulated to the clock reading. -/
  S_I : ℝ
  /-- **Load-bearing assumption**: `S_I ≥ 0`. -/
  S_I_nonneg : 0 ≤ S_I

namespace ImaginaryActionDamping

variable (D : ImaginaryActionDamping)

/-- Modulus of the dissipative amplitude factor: `exp(−S_I/(2ℏ))`. -/
def amplitude : ℝ := Real.exp (-(D.S_I / (2 * D.ℏ)))

/-- Squared amplitude (probability damping): `exp(−S_I/ℏ)`. -/
def probability : ℝ := Real.exp (-(D.S_I / D.ℏ))

theorem amplitude_pos : 0 < D.amplitude := Real.exp_pos _

/-- The amplitude is at most `1` under `S_I ≥ 0`. -/
theorem amplitude_le_one : D.amplitude ≤ 1 := by
  rw [amplitude, Real.exp_le_one_iff]
  have hq : 0 ≤ D.S_I / (2 * D.ℏ) :=
    div_nonneg D.S_I_nonneg (by have := D.ℏ_pos; positivity)
  linarith

/-- **Recovery of standard Page–Wootters** at `S_I = 0`: no damping. -/
theorem amplitude_at_S_I_zero (h : D.S_I = 0) : D.amplitude = 1 := by
  rw [amplitude, h]; simp

/-- **Central identity**: the squared amplitude equals the probability damping
`exp(−S_I/ℏ)`. -/
theorem amplitude_sq_eq_probability : D.amplitude ^ 2 = D.probability := by
  rw [amplitude, probability, sq, ← Real.exp_add]
  congr 1
  have : D.ℏ ≠ 0 := ne_of_gt D.ℏ_pos
  field_simp; ring

/-- Logarithmic form: `log(amplitude) = −S_I/(2ℏ)`. -/
theorem log_amplitude : Real.log D.amplitude = -(D.S_I / (2 * D.ℏ)) := by
  rw [amplitude, Real.log_exp]

/-- **Anti-monotonicity in `S_I`** (same `ℏ`): larger imaginary action yields a
smaller amplitude. -/
theorem amplitude_antitone (D' : ImaginaryActionDamping)
    (hℏ : D.ℏ = D'.ℏ) (h : D.S_I ≤ D'.S_I) : D'.amplitude ≤ D.amplitude := by
  rw [amplitude, amplitude, Real.exp_le_exp, hℏ, neg_le_neg_iff]
  have hpos : (0 : ℝ) < 2 * D'.ℏ := by have := D.ℏ_pos; rw [hℏ] at this; linarith
  gcongr

end ImaginaryActionDamping

end QuantumMechanics.RelationalTime

end
