/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzNambu
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-!
# The Lorenz orbit on `Σ₂`: anharmonic-oscillator reduction and the lobe gate (Axenides–Floratos §3.1)

On the non-dissipative Lorenz orbit the generalized Hamiltonian `H₂ = σz − x²/2` is conserved
(`DissipativeNambuLorenz.LorenzNambu`), so the motion lies on the parabolic cylinder `Σ₂ : H₂ = const`
(Axenides, Floratos, JHEP 04 (2010) 036, Eq. 3.23). Reducing the dynamics to `Σ₂` turns the remaining
generalized Hamiltonian `H₁ = ½[y² + (z−r)²]` into an **anharmonic (quartic) oscillator** (Eq. 3.27)

  `H₁ = ½ y² + (x² − a²)² / (8σ²)`,   with   `a² = −2H₂ + 2σr = 2(σr − H₂)`   (Eq. 3.28),

whose effective potential `V(x) = (x² − a²)²/(8σ²)` is a **single well** (`a² ≤ 0`, `H₂ ≥ σr`) or a
**double well** (`a² > 0`, `H₂ < σr`) — the two minima `x = ±√(a²)` being the two lobes of the Lorenz
butterfly, the single well being a one-lobe orbit.

This file works at the algebraic layer (scalars `H₁, H₂` whose gradients are the `lorenzGradH₁/₂` of
`DissipativeNambuLorenz.LorenzNambu`; the canonical/symplectic reduction itself is not formalized):

* **§A — the surface relation** (Eqs. 3.23–3.24, 3.28). `aSq = 2(σr − H₂)`; `surface_z_eq`:
  `(x² − a²)/(2σ) = z − r` on `Σ₂` (for `σ ≠ 0`).
* **§B — the anharmonic reduction** (Eq. 3.27). `lorenzH1_reduced`: `H₁ = ½y² + V(x)` with
  `V(x) = (x² − a²)²/(8σ²)`.
* **§C — the lobe gate** (Eq. 3.28). `aSq_pos_iff`: `a² > 0 ⟺ H₂ < σr`. `effPotential_sub_center`:
  `V(x) − V(0) = x²(x² − 2a²)/(8σ²)`. `effPotential_single_well` (`a² ≤ 0`): `0` is the strict minimum —
  one lobe. `effPotential_double_well` (`a² > 0`): every `A` with `A² = a²` (i.e. `±√(a²)`) is a zero of `V`
  strictly below the central barrier `V(0) > 0`, and `A ≠ 0` — two lobes.

## References

* M. Axenides, E. Floratos, JHEP 04 (2010) 036, §3.1, Eqs. 3.19–3.20, 3.23–3.24, 3.27–3.28. `Physlib`
  (`DissipativeNambuLorenz.LorenzNambu`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzNambu

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzSigma2Reduction

/-- **`H₁ = ½[y² + (z−r)²]`** (Eq. 3.19) — the scalar generalized Hamiltonian whose gradient is
`lorenzGradH₁`. -/
noncomputable def lorenzH1 (r : ℝ) (p : Fin 3 → ℝ) : ℝ := ((p 1) ^ 2 + (p 2 - r) ^ 2) / 2

/-- **`H₂ = σz − x²/2`** (Eq. 3.20) — the conserved generalized Hamiltonian (its level set is `Σ₂`) whose
gradient is `lorenzGradH₂`. -/
noncomputable def lorenzH2 (σ : ℝ) (p : Fin 3 → ℝ) : ℝ := σ * p 2 - (p 0) ^ 2 / 2

/-- **`a² = 2(σr − H₂)`** (Eq. 3.28) — the anharmonic shape parameter; `> 0` is the double well. -/
noncomputable def aSq (σ r : ℝ) (p : Fin 3 → ℝ) : ℝ := 2 * (σ * r - lorenzH2 σ p)

/-- **The effective anharmonic potential** `V(x) = (x² − a²)²/(8σ²)` (the quartic of Eq. 3.27). -/
noncomputable def effPotential (asq σ x : ℝ) : ℝ := (x ^ 2 - asq) ^ 2 / (8 * σ ^ 2)


/-- **[Surface relation]** on `Σ₂`, `(x² − a²)/(2σ) = z − r` (for `σ ≠ 0`): the parabolic-cylinder constraint
`H₂ = const` written through the shape parameter `a² = 2(σr − H₂)`. -/
lemma surface_z_eq (σ r : ℝ) (p : Fin 3 → ℝ) (hσ : σ ≠ 0) :
    (p 0 ^ 2 - aSq σ r p) / (2 * σ) = p 2 - r := by
  rw [div_eq_iff (mul_ne_zero two_ne_zero hσ)]
  unfold aSq lorenzH2
  ring


/-- **[Anharmonic reduction]** on `Σ₂`, `H₁ = ½y² + V(x)` with `V(x) = (x² − a²)²/(8σ²)` (Eq. 3.27): the
non-dissipative Lorenz dynamics reduces to a quartic oscillator in `x` with `y` the conjugate momentum. -/
lemma lorenzH1_reduced (σ r : ℝ) (p : Fin 3 → ℝ) (hσ : σ ≠ 0) :
    lorenzH1 r p = (p 1) ^ 2 / 2 + effPotential (aSq σ r p) σ (p 0) := by
  have hs := surface_z_eq σ r p hσ
  unfold lorenzH1 effPotential
  rw [← hs]
  field_simp
  ring


/-- **[Double-well condition]** `a² > 0 ⟺ H₂ < σr` (Eq. 3.28): the orbit is a two-lobe (butterfly) orbit
exactly when the conserved `H₂` is below `σr`. -/
lemma aSq_pos_iff (σ r : ℝ) (p : Fin 3 → ℝ) :
    0 < aSq σ r p ↔ lorenzH2 σ p < σ * r := by
  unfold aSq
  constructor <;> intro h <;> linarith

/-- **[Potential relative to the centre]** `V(x) − V(0) = x²(x² − 2a²)/(8σ²)` — the algebraic identity
controlling the well shape. -/
lemma effPotential_sub_center (asq σ x : ℝ) :
    effPotential asq σ x - effPotential asq σ 0 = x ^ 2 * (x ^ 2 - 2 * asq) / (8 * σ ^ 2) := by
  unfold effPotential
  rw [← sub_div]
  congr 1
  ring

/-- **[Single well]** for `a² ≤ 0` (i.e. `H₂ ≥ σr`) the centre `x = 0` is the strict minimum of `V`: a
one-lobe orbit. -/
lemma effPotential_single_well (asq σ x : ℝ) (h0 : asq ≤ 0) (hσ : σ ≠ 0) (hx : x ≠ 0) :
    effPotential asq σ 0 < effPotential asq σ x := by
  have hsub := effPotential_sub_center asq σ x
  have hx2 : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hx))
  have hσsq : 0 < σ ^ 2 := lt_of_le_of_ne (sq_nonneg σ) (Ne.symm (pow_ne_zero 2 hσ))
  have hσ2 : 0 < 8 * σ ^ 2 := by linarith
  have hfac : 0 < x ^ 2 - 2 * asq := by linarith
  have hpos : 0 < x ^ 2 * (x ^ 2 - 2 * asq) / (8 * σ ^ 2) := div_pos (mul_pos hx2 hfac) hσ2
  linarith

/-- **[Double well]** for `a² > 0` (i.e. `H₂ < σr`) every `A` with `A² = a²` — the two lobe centres
`x = ±√(a²)` — is a zero of `V`, strictly below the positive central barrier `V(0)`, and is nonzero: a
two-lobe orbit. -/
lemma effPotential_double_well (asq σ A : ℝ) (hA : A ^ 2 = asq) (h0 : 0 < asq) (hσ : σ ≠ 0) :
    effPotential asq σ A = 0 ∧ effPotential asq σ A < effPotential asq σ 0 ∧ A ≠ 0 := by
  have hσsq : 0 < σ ^ 2 := lt_of_le_of_ne (sq_nonneg σ) (Ne.symm (pow_ne_zero 2 hσ))
  have hσ2 : 0 < 8 * σ ^ 2 := by linarith
  have hzero : effPotential asq σ A = 0 := by
    unfold effPotential
    rw [hA, sub_self]
    simp
  have hcenter : 0 < effPotential asq σ 0 := by
    have hrw : effPotential asq σ 0 = asq ^ 2 / (8 * σ ^ 2) := by
      unfold effPotential; rw [show ((0 : ℝ) ^ 2 - asq) ^ 2 = asq ^ 2 from by ring]
    rw [hrw]
    exact div_pos (pow_pos h0 2) hσ2
  have hAne : A ≠ 0 := by
    intro h
    rw [h] at hA
    simp at hA
    linarith [hA.symm.le, h0]
  exact ⟨hzero, by rw [hzero]; exact hcenter, hAne⟩

end Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzSigma2Reduction

end
