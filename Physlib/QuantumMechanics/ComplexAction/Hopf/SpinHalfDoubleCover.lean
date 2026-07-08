/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.PolarizatorBlochSphere

/-!
# Spin-½ as the SU(2) → SO(3) double cover: the 2π/4π periodicity

Formalizes the **spin-½ double cover** — the genuine, exact content behind "spin is topological". A spinor
rotation about a Bloch axis is the half-angle SU(2) element

  `R(θ) = cos(θ/2)·1 − i sin(θ/2)·G`   (`spinRotation`, `G` the su(2) generator with `G² = 1`),

which is **4π-periodic, not 2π-periodic**:

* a `2π` rotation sends the spinor to **minus itself** `R(θ + 2π) = −R(θ)` (`spinRotation_add_two_pi`), so
  `R(2π) = −1` (`spinRotation_two_pi`);
* only a `4π` rotation returns it, `R(4π) = 1` (`spinRotation_four_pi`).

The **double cover** is then exact: the *physical* (SO(3)) rotation — the sign-insensitive conjugation
`R · X · R` — is already `2π`-periodic (`spinRotation_conj_two_pi`), because it is unchanged under
`R ↦ −R` (`neg_conj_invariant`). So `SO(3)` closes at `2π` while its `SU(2)` spinor cover needs `4π`: a
spin-½ object is double-valued over the rotation group.

Grounded in the existing su(2)/Bloch structure: the generator is the **Bloch-sphere Pauli-`Y`**
`σ_y = σ(inr 1)` of `AlgebraicQFTQuasifree.PolarizatorBlochSphere` (`J = iσ_y`, `σ_y² = 1` by `pauliY_sq`), so
`spinHalfRotation θ = R_{σ_y}(θ)` (`spinHalfRotation`) is the spin-½ rotation about the Bloch axis, with the
2π/4π double cover (`spin_half_double_cover`). This is the rigorous, knot-free statement of the spin-½
topology: the SU(2) double cover of the rotation group, on the existing Bloch/Bogoliubov su(2).

* **§A — the spinor rotation and its 2π/4π periodicity** (`spinRotation`, `spinRotation_zero`,
  `spinRotation_add_two_pi`, `spinRotation_two_pi`, `spinRotation_four_pi`).
* **§B — the SU(2) → SO(3) double cover** (`neg_conj_invariant`, `spinRotation_conj_two_pi`).
* **§C — spin-½ on the Bloch su(2)** (`spinHalfRotation`, `spinHalfRotation_two_pi`,
  `spinHalfRotation_four_pi`, `spin_half_double_cover`).

## References

* The SU(2) → SO(3) double cover and spin-½ periodicity (standard). structures:
  `AlgebraicQFTQuasifree.PolarizatorBlochSphere` (`σ`, `pauliY_sq`, `J = iσ_y` Bloch generator),
  `Bogoliubov.SaitoBogoliubovBoseFermiStatistics` / `ThermoFieldDynamics.TFDBogoliubovHopf` (the fermion su(2) Bogoliubov structure).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover

open Matrix PauliMatrix

/-! ## §A — the spinor rotation and its 2π/4π periodicity -/

/-- **The spinor (SU(2)) rotation** `R(θ) = cos(θ/2)·1 − i sin(θ/2)·G` about a Bloch axis with su(2)
generator `G` (`G² = 1`). The half-angle is what makes spin-½ double-valued over the rotation group. -/
noncomputable def spinRotation (G : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos (θ / 2) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
    - (Real.sin (θ / 2) : ℂ) • (Complex.I • G)

/-- **[`R(0) = 1`]** the identity rotation. -/
theorem spinRotation_zero (G : Matrix (Fin 2) (Fin 2) ℂ) : spinRotation G 0 = 1 := by
  rw [spinRotation]; simp

/-- **[The spinor flips sign under a `2π` rotation] `R(θ + 2π) = −R(θ)`.** The defining feature of spin-½:
a full `2π` rotation multiplies the spinor by `−1` (`cos(θ/2 + π) = −cos(θ/2)`, `sin(θ/2 + π) =
−sin(θ/2)`). -/
theorem spinRotation_add_two_pi (G : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    spinRotation G (θ + 2 * Real.pi) = - spinRotation G θ := by
  have hc : Real.cos ((θ + 2 * Real.pi) / 2) = - Real.cos (θ / 2) := by
    rw [show (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi by ring, Real.cos_add, Real.cos_pi, Real.sin_pi]
    ring
  have hs : Real.sin ((θ + 2 * Real.pi) / 2) = - Real.sin (θ / 2) := by
    rw [show (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi by ring, Real.sin_add, Real.cos_pi, Real.sin_pi]
    ring
  rw [spinRotation, spinRotation, hc, hs]
  push_cast
  simp only [neg_smul]
  abel

/-- **[`R(2π) = −1`]** a `2π` rotation is `−1` on spinors. -/
theorem spinRotation_two_pi (G : Matrix (Fin 2) (Fin 2) ℂ) : spinRotation G (2 * Real.pi) = -1 := by
  have h := spinRotation_add_two_pi G 0
  rw [zero_add, spinRotation_zero] at h
  exact h

/-- **[`R(4π) = 1`]** only a `4π` rotation returns the spinor to itself — the `SU(2)` double cover. -/
theorem spinRotation_four_pi (G : Matrix (Fin 2) (Fin 2) ℂ) : spinRotation G (4 * Real.pi) = 1 := by
  have h := spinRotation_add_two_pi G (2 * Real.pi)
  rw [spinRotation_two_pi, show (2 * Real.pi + 2 * Real.pi) = 4 * Real.pi by ring, neg_neg] at h
  exact h

/-! ## §B — the SU(2) → SO(3) double cover -/

/-- **[Conjugation is invariant under `R ↦ −R`] `(−R)·X·(−R) = R·X·R`.** The two sign factors cancel, so the
physical (adjoint / SO(3)) action of a spinor rotation does not see the overall sign. -/
theorem neg_conj_invariant (R X : Matrix (Fin 2) (Fin 2) ℂ) : (-R) * X * (-R) = R * X * R := by
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- **[The SO(3) rotation is `2π`-periodic] `R(θ + 2π)·X·R(θ + 2π) = R(θ)·X·R(θ)`.** Although the spinor
`R` flips sign at `2π` and needs `4π` to return, the physical rotation it generates — the sign-insensitive
conjugation `R · X · R` — is already `2π`-periodic. This is the `SU(2) → SO(3)` double cover: `SO(3)` closes
at `2π`, its spinor cover `SU(2)` at `4π`. -/
theorem spinRotation_conj_two_pi (G X : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    spinRotation G (θ + 2 * Real.pi) * X * spinRotation G (θ + 2 * Real.pi)
      = spinRotation G θ * X * spinRotation G θ := by
  rw [spinRotation_add_two_pi]
  exact neg_conj_invariant (spinRotation G θ) X

/-! ## §C — spin-½ on the Bloch su(2) -/

/-- **The spin-½ rotation** `R_{σ_y}(θ)` about the Bloch axis — the spinor rotation generated by the
Bloch-sphere Pauli-`Y` `σ_y = σ(inr 1)` (`AlgebraicQFTQuasifree.PolarizatorBlochSphere`, `σ_y² = 1` by `pauliY_sq`, the su(2)
generator `J = iσ_y` of the Bloch/Poincaré sphere). -/
noncomputable def spinHalfRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  spinRotation (σ (Sum.inr 1)) θ

/-- **[Spin-½: `R(2π) = −1`]** the electron spinor flips sign under a `2π` rotation about the Bloch axis. -/
theorem spinHalfRotation_two_pi : spinHalfRotation (2 * Real.pi) = -1 :=
  spinRotation_two_pi (σ (Sum.inr 1))

/-- **[Spin-½: `R(4π) = 1`]** only a `4π` rotation returns it — the spin-½ double cover. -/
theorem spinHalfRotation_four_pi : spinHalfRotation (4 * Real.pi) = 1 :=
  spinRotation_four_pi (σ (Sum.inr 1))

/-- **[The spin-½ double cover, assembled].** The spin-½ rotation about the Bloch axis:

* flips sign under `2π`, `R(2π) = −1`;
* returns only under `4π`, `R(4π) = 1`;
* yet generates an SO(3) rotation already `2π`-periodic, `R(θ+2π)·X·R(θ+2π) = R(θ)·X·R(θ)`.

A spin-½ object is double-valued over the rotation group — the `SU(2) → SO(3)` double cover — grounded
in the existing Bloch/Bogoliubov su(2), with no knot or trefoil structure required. -/
theorem spin_half_double_cover (X : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) :
    spinHalfRotation (2 * Real.pi) = -1
      ∧ spinHalfRotation (4 * Real.pi) = 1
      ∧ spinHalfRotation (θ + 2 * Real.pi) * X * spinHalfRotation (θ + 2 * Real.pi)
          = spinHalfRotation θ * X * spinHalfRotation θ :=
  ⟨spinHalfRotation_two_pi, spinHalfRotation_four_pi, spinRotation_conj_two_pi (σ (Sum.inr 1)) X θ⟩

end Physlib.QuantumMechanics.ComplexAction.Hopf.SpinHalfDoubleCover

end
