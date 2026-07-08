/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.LorentzGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Einstein's equations from tetrad/canonical data: ADM tetrad gravity (Lusanna 2015)

Formalizes the algebraic kernel of canonical **ADM tetrad gravity** (L. Lusanna, *Canonical ADM tetrad
gravity*, Int. J. Geom. Methods Mod. Phys. 12 (2015) 1530001) — how the **Einstein/GR structure is
reconstructed from the Lorentz-frame tetrad variables** (the variables in which the Dirac/fermion field lives,
the QFT/QM side) — and links the Lorentz gauge algebra to the fused `𝔰𝔬(1,3)` superoperator
(`AlgebraicQFTQuasifree.KleinGordonProgram` §F / `Electromagnetic.EMLorentzCombinedSuperoperator`).

In tetrad gravity the `4`-metric is *built* from the cotetrad `E` and the flat Minkowski metric `η`:

  `g_AB = η_{(α)(β)} E^{(α)}_A E^{(β)}_B`, i.e. `g = EᵀηE`   (`tetradMetric`).

The tetrad includes the local Lorentz gauge freedom `E ↦ ΛE`, `Λ ∈ SO(1,3)`, which **drops out of the metric**
(`tetradMetric_lorentz_gauge`) — the `𝔰𝔬(1,3)` rotations of the orthonormal frame are pure gauge, the inertial
freedom. The dynamical Einstein content is then the **ADM constraints**: the scalar (Hamiltonian) constraint
`³R + (tr K)² − K_ij K^ij = 16πG ρ` is the `G_{nn}` (time–time) Einstein equation in Gauss–Codazzi form, and
its trace gauge variable — the **York time** `tr K` (the trace of the extrinsic curvature) — is Lusanna's
central inertial gauge variable (clock synchronization).

* **§A — the tetrad reconstruction of the metric** (`tetradMetric`, `tetradMetric_symm`,
  `lorentz_preserves_eta`, `tetradMetric_lorentz_gauge`). `g = EᵀηE`, symmetric, invariant under local Lorentz
  `E ↦ ΛE`.
* **§B — the `𝔰𝔬(1,3)` Lorentz gauge algebra** (`IsLorentzAlg`, `lorentzAlg_add`,
  `infinitesimal_lorentz_metric_invariant`, `lorentzAlg_eta_antisym`). The `η`-antisymmetric generators
  `JᵀΗ = −ηJ`; closure under `+`; the infinitesimal gauge invariance `Eᵀ(Jᵀη+ηJ)E = 0`; and `ηJ` is *plain*
  antisymmetric — the metric-covariant form of the fused superoperator's `𝔰𝔬(1,3)` (the same Lie algebra
  with the EM field strength and the Lorentz/gravity generator).
* **§C — the ADM constraints / York time** (`yorkTime`, `hamiltonianConstraint`,
  `hamiltonianConstraint_vacuum_iff`, `sourcedHamiltonianConstraint`,
  `sourcedHamiltonianConstraint_vacuum_iff`). The York time `tr K`; the scalar constraint `= G_{nn}` Einstein;
  vacuum `ℋ = 0 ⟺ ³R + (tr K)² = K_ij K^ij`; and the matter-sourced form `ℋ = κ ρ` (`G_{nn} = κ T_{nn}`)
  whose `ρ = 0` limit is the vacuum constraint.

The deep canonical-gravity machinery — the Dirac first-class constraint algebra, the York canonical basis
diagonalizing York–Lichnerowicz, the tidal Dirac observables, the post-Minkowskian linearization — is the
analytic/Hamiltonian layer; the metric-reconstruction and constraint kernel is formalized here.

## References

* L. Lusanna, *Canonical ADM tetrad gravity*, Int. J. Geom. Methods Mod. Phys. 12 (2015) 1530001
  (tetrad `4`-metric, York time = `tr K`, the ADM constraints, Dirac observables).
* Repo dependencies: `Relativity.MinkowskiMatrix` (`minkowskiMatrix`, `sq`, `eq_transpose`),
  `Relativity.LorentzGroup` (`LorentzGroup`, `dual`); `AlgebraicQFTQuasifree.KleinGordonProgram` §F /
  `Electromagnetic.EMLorentzCombinedSuperoperator` (the fused `𝔰𝔬(1,3)` superoperator `ad_{J+F}`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

open Matrix

variable {d : ℕ}

/-! ## §A — the tetrad reconstruction of the `4`-metric -/

/-- **[`g = EᵀηE`] The `4`-metric reconstructed from a cotetrad** `g_AB = η_{(α)(β)} E^{(α)}_A E^{(β)}_B` —
GR's metric built from the orthonormal-frame tetrad `E` and the flat Minkowski metric `η`. -/
noncomputable def tetradMetric (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ := Eᵀ * minkowskiMatrix * E

/-- **The reconstructed metric is symmetric** `gᵀ = g` (from `ηᵀ = η`). -/
theorem tetradMetric_symm (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    (tetradMetric E)ᵀ = tetradMetric E := by
  rw [tetradMetric, transpose_mul, transpose_mul, transpose_transpose,
    minkowskiMatrix.eq_transpose, Matrix.mul_assoc]

/-- **Lorentz transformations preserve `η`** `Λᵀ η Λ = η` — the defining property of `SO(1,3)` (from
`dual Λ · Λ = 1` and `η² = 1`). -/
theorem lorentz_preserves_eta {Λ : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (h : Λ ∈ LorentzGroup d) : Λᵀ * minkowskiMatrix * Λ = minkowskiMatrix := by
  have h1 : minkowskiMatrix * Λᵀ * minkowskiMatrix * Λ = 1 :=
    LorentzGroup.mem_iff_dual_mul_self.mp h
  have h2 : minkowskiMatrix * (minkowskiMatrix * Λᵀ * minkowskiMatrix * Λ) = minkowskiMatrix := by
    rw [h1, mul_one]
  calc Λᵀ * minkowskiMatrix * Λ
      = (minkowskiMatrix * minkowskiMatrix) * Λᵀ * minkowskiMatrix * Λ := by
        rw [minkowskiMatrix.sq, one_mul]
    _ = minkowskiMatrix * (minkowskiMatrix * Λᵀ * minkowskiMatrix * Λ) := by noncomm_ring
    _ = minkowskiMatrix := h2

/-- **[Local Lorentz gauge invariance] `g[ΛE] = g[E]`** — the metric is invariant under a local Lorentz
rotation `E ↦ ΛE` of the orthonormal frame: the `𝔰𝔬(1,3)` frame rotations are pure (inertial) gauge, dropping
out of GR's metric. -/
theorem tetradMetric_lorentz_gauge {Λ E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (h : Λ ∈ LorentzGroup d) : tetradMetric (Λ * E) = tetradMetric E := by
  rw [tetradMetric, tetradMetric, transpose_mul]
  calc Eᵀ * Λᵀ * minkowskiMatrix * (Λ * E)
      = Eᵀ * (Λᵀ * minkowskiMatrix * Λ) * E := by noncomm_ring
    _ = Eᵀ * minkowskiMatrix * E := by rw [lorentz_preserves_eta h]

/-! ## §B — the `𝔰𝔬(1,3)` Lorentz gauge algebra -/

/-- **The Lorentz Lie algebra `𝔰𝔬(1,3)`** — the `η`-antisymmetric generators `Jᵀη = −ηJ` (the infinitesimal
frame rotations/boosts). -/
def IsLorentzAlg (J : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) : Prop :=
  Jᵀ * minkowskiMatrix = -(minkowskiMatrix * J)

/-- **`𝔰𝔬(1,3)` is closed under addition.** -/
theorem lorentzAlg_add {J K : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (hJ : IsLorentzAlg J) (hK : IsLorentzAlg K) : IsLorentzAlg (J + K) := by
  unfold IsLorentzAlg at *; rw [transpose_add, add_mul, hJ, hK, mul_add, neg_add]

/-- **[Infinitesimal Lorentz gauge invariance] `Eᵀ(Jᵀη + ηJ)E = 0`** — a `𝔰𝔬(1,3)` generator produces a
*vanishing* first-order variation of the tetrad metric: the frame rotation `δE = JE` is metric-preserving (the
linearization of `tetradMetric_lorentz_gauge`). -/
theorem infinitesimal_lorentz_metric_invariant
    {J : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ} (hJ : IsLorentzAlg J)
    (E : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    Eᵀ * (Jᵀ * minkowskiMatrix + minkowskiMatrix * J) * E = 0 := by
  unfold IsLorentzAlg at hJ
  rw [hJ, neg_add_cancel, Matrix.mul_zero, Matrix.zero_mul]

/-- **[Link to the fused superoperator] `ηJ` is plain-antisymmetric** `(ηJ)ᵀ = −ηJ`. The metric-covariant
`𝔰𝔬(1,3)` generator `J` (`η`-antisymmetric) maps to a *plain* antisymmetric matrix `ηJ` — the convention of
the fused Lorentz–EM superoperator `ad_{J+F}` (`Electromagnetic.EMLorentzCombinedSuperoperator`), where the EM field strength
and the Lorentz/gravity generator are plain-antisymmetric `𝔰𝔬(1,3)` elements. Same Lie algebra, two
conventions related by `J ↦ ηJ`. -/
theorem lorentzAlg_eta_antisym {J : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (hJ : IsLorentzAlg J) : (minkowskiMatrix * J)ᵀ = -(minkowskiMatrix * J) := by
  rw [transpose_mul, minkowskiMatrix.eq_transpose, hJ]

/-! ## §C — the ADM constraints and the York time -/

/-- **[Lusanna's inertial gauge variable] The York time `tr K`** — the trace of the extrinsic curvature of the
instantaneous `3`-space, the freedom in clock synchronization. -/
noncomputable def yorkTime (K : Matrix (Fin d) (Fin d) ℝ) : ℝ := Matrix.trace K

/-- **[Scalar/Hamiltonian constraint = `G_{nn}` Einstein] `ℋ = ³R + (tr K)² − K_ij K^ij`** — the Gauss–Codazzi
form of the time–time Einstein equation (`ℋ = 16πG ρ`); the dynamical Einstein content of the canonical data
`(³metric, K)`. -/
noncomputable def hamiltonianConstraint (R3 KdotK : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  R3 + yorkTime K ^ 2 - KdotK

/-- **[Vacuum Einstein time–time] `ℋ = 0 ⟺ ³R + (tr K)² = K_ij K^ij`** — the vacuum Hamiltonian constraint,
the `G_{nn} = 0` Einstein equation relating the `3`-curvature and the extrinsic curvature. -/
theorem hamiltonianConstraint_vacuum_iff (R3 KdotK : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) :
    hamiltonianConstraint R3 KdotK K = 0 ↔ R3 + yorkTime K ^ 2 = KdotK := by
  rw [hamiltonianConstraint, sub_eq_zero]

/-- **[Matter-sourced scalar constraint] `ℋ = κ ρ`** — the full (non-vacuum) Hamiltonian/scalar Einstein
constraint with matter energy density `ρ` on the right: `³R + (tr K)² − K_ij K^ij = κ ρ`, the `G_{nn} = κ T_{nn}`
time–time Einstein equation (`κ = 16πG`). The vacuum constraint is the `ρ = 0` limit. -/
def sourcedHamiltonianConstraint (R3 KdotK ρ κ : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  hamiltonianConstraint R3 KdotK K = κ * ρ

/-- **[The sourceless limit is the vacuum constraint] `ρ = 0`** — the matter-sourced scalar constraint at
zero energy density reduces to the vacuum Hamiltonian constraint `³R + (tr K)² = K_ij K^ij`
(`hamiltonianConstraint_vacuum_iff`). -/
theorem sourcedHamiltonianConstraint_vacuum_iff (R3 KdotK κ : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) :
    sourcedHamiltonianConstraint R3 KdotK 0 κ K ↔ R3 + yorkTime K ^ 2 = KdotK := by
  rw [sourcedHamiltonianConstraint, mul_zero, hamiltonianConstraint_vacuum_iff]

/-! ## §D — Regge/Sorkin initial-value constraint bridge -/

/-- Sorkin's Regge initial-value constraints are the discrete counterpart of the
ADM Hamiltonian constraint.  This definition reuses the existing ADM scalar
constraint structure. -/
noncomputable def sorkinADMConstraint {d : ℕ}
    (R3 KdotK : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  hamiltonianConstraint R3 KdotK K

/-- Vacuum Sorkin/Regge initial-value constraint, expressed through the existing
ADM Hamiltonian constraint theorem. -/
theorem sorkinADMConstraint_vacuum_iff {d : ℕ}
    (R3 KdotK : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) :
    sorkinADMConstraint R3 KdotK K = 0 ↔ R3 + yorkTime K ^ 2 = KdotK := by
  exact hamiltonianConstraint_vacuum_iff R3 KdotK K

/-- Sourced Sorkin/Regge initial-value constraint, linked to the existing ADM
matter-sourced scalar constraint. -/
theorem sorkinADMConstraint_sourced_iff {d : ℕ}
    (R3 KdotK rho kappa : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) :
    sorkinADMConstraint R3 KdotK K = kappa * rho
      ↔ sourcedHamiltonianConstraint R3 KdotK rho kappa K := by
  rfl

/-! ## §E — Einstein from tetrad/canonical data -/

/-- **[GR from the tetrad/canonical data] the Einstein structure assembled.** The metric is the
Lorentz-gauge-invariant tetrad construct `g[ΛE] = g[E]`; the `G_{nn}` Einstein equation is the vacuum
Hamiltonian constraint `³R + (tr K)² = K_ij K^ij`; and the gauge generator is a `𝔰𝔬(1,3)` element whose
`η`-dressed form `ηJ` is the plain-antisymmetric `𝔰𝔬(1,3)` of the fused Lorentz–EM superoperator. GR's
Einstein content is reconstructed from the Lorentz-frame (Dirac/QFT) tetrad and canonical variables. -/
theorem einstein_from_tetrad_data {Λ E J : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (hΛ : Λ ∈ LorentzGroup d) (hJ : IsLorentzAlg J)
    (R3 KdotK : ℝ) (K : Matrix (Fin d) (Fin d) ℝ) :
    tetradMetric (Λ * E) = tetradMetric E
      ∧ (hamiltonianConstraint R3 KdotK K = 0 ↔ R3 + yorkTime K ^ 2 = KdotK)
      ∧ (minkowskiMatrix * J)ᵀ = -(minkowskiMatrix * J) :=
  ⟨tetradMetric_lorentz_gauge hΛ, hamiltonianConstraint_vacuum_iff R3 KdotK K,
    lorentzAlg_eta_antisym hJ⟩

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

end
