/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Das–Jevicki collective field theory of MQM (Alexandrov §III.3)

The macroscopic / target-space description of 2D string theory is obtained from the **collective field** —
the density of matrix eigenvalues `φ(x,t) = tr δ(x − M(t))` (Alexandrov, hep-th/0311273, Eq. III.45), the
two-dimensional dynamical string field. Its dynamics is the Das–Jevicki collective field theory.

The collective Hamiltonian is the energy of the Fermi sea, `H = ∬_{sea} (dx dp / 2π)(h(x,p) + μ)` with the
inverted-oscillator symbol `h = ½p² − ½x²` (Eqs. III.47–III.48). When the sea is bounded by two momenta
`p_±(x,t)` the momentum integral gives the cubic form (Eq. III.49), and the substitution `p_± = v ± πφ`
(Eq. III.50, with density `φ = (p_+ − p_-)/2π`) produces the Das–Jevicki collective Hamiltonian density
(Eq. III.52).

* `fermiSea_momentum_integral`: the momentum integral `∫_{p_-}^{p_+}(½p² + W) dp = ⅙(p_+³ − p_-³) +
  W(p_+ − p_-)` — Eq. III.47 → III.49.
* `fermiSeaDensity_eq`: `φ = (p_+ − p_-)/2π` reproduces the Fermi-sea width — the eigenvalue density `φ`
  (Eq. III.45) as a phase-space quantity (Eq. III.50).
* `collective_hamiltonian_density`: under `p_± = v ± πφ` the cubic Fermi-sea integrand becomes the Das–Jevicki
  density `½φv² + (π²/6)φ³ + Wφ` (Eq. III.49 → III.52) — the cubic collective-field interaction.

## References

* S. Yu. Alexandrov, *Matrix Quantum Mechanics and Two-dimensional String Theory in Non-trivial
  Backgrounds*, hep-th/0311273, Ch. III §3, Eqs. (III.45)–(III.52). A. Das, A. Jevicki (1990).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.DasJevickiCollectiveField

/-- **[Fermi-sea momentum integral, Eq. III.47 → III.49]** `∫_{p_-}^{p_+}(½p² + W) dp = ⅙(p_+³ − p_-³) +
W(p_+ − p_-)`. Integrating the single-particle energy `h + μ = ½p² + W` (`W = V + μ`) across the Fermi sea
`p ∈ [p_-, p_+]` produces the cubic form of the collective Hamiltonian. -/
theorem fermiSea_momentum_integral (W pm pp : ℝ) :
    (∫ p in pm..pp, ((1 / 2) * p ^ 2 + W)) = (1 / 6) * (pp ^ 3 - pm ^ 3) + W * (pp - pm) := by
  have hf : IntervalIntegrable (fun p : ℝ => (1 / 2) * p ^ 2) MeasureTheory.volume pm pp :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _
  have hg : IntervalIntegrable (fun _ : ℝ => W) MeasureTheory.volume pm pp :=
    continuous_const.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hf hg, intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, smul_eq_mul]
  push_cast
  ring

/-- **The collective field / eigenvalue density** as a phase-space quantity `φ = (p_+ − p_-)/2π`
(Eq. III.45, III.50): the width of the Fermi sea in momentum, divided by `2π`. -/
noncomputable def fermiSeaDensity (pp pm : ℝ) : ℝ := (pp - pm) / (2 * Real.pi)

/-- **[The density is the half-width, Eq. III.50]** `p_+ − p_- = 2π φ`. -/
theorem fermiSeaDensity_eq (pp pm : ℝ) : pp - pm = 2 * Real.pi * fermiSeaDensity pp pm := by
  unfold fermiSeaDensity
  field_simp

/-- **[Das–Jevicki collective Hamiltonian density, Eq. III.49 → III.52]** Under the parametrization
`p_± = v ± πφ` (Eq. III.50, with velocity `v = (p_+ + p_-)/2` and density `φ = (p_+ − p_-)/2π`) the cubic
Fermi-sea integrand becomes
`(1/2π)(⅙(p_+³ − p_-³) + W(p_+ − p_-)) = ½ φ v² + (π²/6) φ³ + W φ` —
the Das–Jevicki collective field Hamiltonian density, exhibiting the **cubic** `φ³` string interaction. -/
theorem collective_hamiltonian_density (W pp pm : ℝ) :
    (1 / (2 * Real.pi)) * ((1 / 6) * (pp ^ 3 - pm ^ 3) + W * (pp - pm))
      = (1 / 2) * ((pp - pm) / (2 * Real.pi)) * ((pp + pm) / 2) ^ 2
        + (Real.pi ^ 2 / 6) * ((pp - pm) / (2 * Real.pi)) ^ 3
        + W * ((pp - pm) / (2 * Real.pi)) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end Physlib.QuantumMechanics.ComplexAction.MatrixQuantumMechanics.DasJevickiCollectiveField

end
