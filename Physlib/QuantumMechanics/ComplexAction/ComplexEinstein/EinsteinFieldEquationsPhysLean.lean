/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
public import Physlib.Relativity.LorentzAlgebra.Basis

/-!
# The Einstein field equations, realized on the original PhysLean relativity infrastructure

Connects the ADM/York/Lusanna gravity arc (built on this branch) to the **original PhysLean relativity
infrastructure** — `Relativity.LorentzAlgebra` (the Lie algebra `𝔰𝔬(1,3)`), `Relativity.minkowskiMatrix` (the
metric `η`), `Relativity.LorentzGroup` — and realizes the **Einstein field equations** and their general-
relativistic consequences on it.

The bridge is the identity of the gauge algebras: the ADM-tetrad Lorentz gauge generators of
`CanonicalTetradGravity.TetradADMGravity` (`IsLorentzAlg J : Jᵀη = −ηJ`) are *exactly* the elements of PhysLean's
`lorentzAlgebra` (`= so'(1,3)`, with `mem_iff : Aᵀη = −ηA`):

  `IsLorentzAlg J ↔ J ∈ lorentzAlgebra`   (`isLorentzAlg_iff_mem_lorentzAlgebra`),

so PhysLean's `boostGenerator`/`rotationGenerator` are the gravity gauge generators of the arc
(`boostGenerator_isLorentzAlg`, `rotationGenerator_isLorentzAlg`), and the tetrad-reconstructed metric is
invariant under PhysLean's `LorentzGroup` (`CanonicalTetradGravity.TetradADMGravity.tetradMetric_lorentz_gauge`).

On this metric we realize the Einstein field equations:

* the **Einstein tensor** `G_μν = R_μν − ½R g_μν` (`einsteinTensor`, trace-reversed Ricci), symmetric
  (`einsteinTensor_symm`);
* the **field equation** `G_μν = κ T_μν` (`einsteinFieldEquation`) and its cosmological form
  `G_μν + Λ g_μν = κ T_μν` (`einsteinFieldEquationCosmological`);
* the **contracted Bianchi identity ⟹ stress-energy conservation** `∇^μ G_μν = 0 ⟹ ∇^μ T_μν = 0`
  (`bianchi_implies_conservation`);
* the **vacuum equation** `G_μν = 0 ⟺ R_μν = ½R g_μν` (`einsteinTensor_vacuum_iff`).

This ties the whole gravity construction — the fused Lorentz–EM superoperator, the ADM constraints, the York
basis, the complex Einstein energy — to the canonical PhysLean Lorentz-algebra / metric machinery.

* **§A — the gauge algebras coincide** (`isLorentzAlg_iff_mem_lorentzAlgebra`, `boostGenerator_isLorentzAlg`,
  `rotationGenerator_isLorentzAlg`).
* **§B — the Einstein field equations** (`einsteinTensor`, `einsteinTensor_symm`,
  `einsteinTensor_vacuum_iff`, `einsteinFieldEquation`, `einsteinFieldEquationCosmological`,
  `bianchi_implies_conservation`).

## References

* C. W. Misner, K. S. Thorne, J. A. Wheeler, *Gravitation* (the Einstein tensor, the field equations, the
  contracted Bianchi identity).
* Repo carriers: `Relativity.LorentzAlgebra` (`lorentzAlgebra`, `boostGenerator`, `rotationGenerator`,
  `mem_iff`), `Relativity.minkowskiMatrix`, `CanonicalTetradGravity.TetradADMGravity` (`IsLorentzAlg`, the tetrad metric).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

open Matrix minkowskiMatrix
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity


/-- **[The gauge algebras coincide] `IsLorentzAlg J ↔ J ∈ lorentzAlgebra`.** The ADM-tetrad Lorentz gauge
generator condition `Jᵀη = −ηJ` (`CanonicalTetradGravity.TetradADMGravity.IsLorentzAlg`) is *exactly* membership in PhysLean's
`Relativity.LorentzAlgebra.lorentzAlgebra` (`= so'(1,3)`, `mem_iff : Aᵀη = −ηA`). The branch's gravity gauge
algebra is the canonical Lorentz Lie algebra. -/
lemma isLorentzAlg_iff_mem_lorentzAlgebra (J : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :
    IsLorentzAlg J ↔ J ∈ lorentzAlgebra := by
  rw [IsLorentzAlg, lorentzAlgebra.mem_iff, neg_mul]

/-- **[PhysLean boosts are gravity gauge generators] `boostGenerator i` satisfies `IsLorentzAlg`.** -/
lemma boostGenerator_isLorentzAlg (i : Fin 3) : IsLorentzAlg (lorentzAlgebra.boostGenerator i) :=
  (isLorentzAlg_iff_mem_lorentzAlgebra _).mpr (lorentzAlgebra.boostGenerator_mem i)

/-- **[PhysLean rotations are gravity gauge generators] `rotationGenerator i` satisfies `IsLorentzAlg`.** -/
lemma rotationGenerator_isLorentzAlg (i : Fin 3) :
    IsLorentzAlg (lorentzAlgebra.rotationGenerator i) :=
  (isLorentzAlg_iff_mem_lorentzAlgebra _).mpr (lorentzAlgebra.rotationGenerator_mem i)


variable {ι : Type*}

/-- **[Trace-reversed Ricci] the Einstein tensor** `G_μν = R_μν − ½R g_μν` — built from the Ricci tensor
`Ric`, the scalar curvature `scalarR`, and the metric `g`. -/
noncomputable def einsteinTensor (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  Ric - (scalarR / 2) • g

/-- **The Einstein tensor is symmetric** when `Ric` and `g` are (`Gᵀ = G`). -/
lemma einsteinTensor_symm (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g : Matrix ι ι ℝ)
    (hRic : Ricᵀ = Ric) (hg : gᵀ = g) :
    (einsteinTensor Ric scalarR g)ᵀ = einsteinTensor Ric scalarR g := by
  rw [einsteinTensor, transpose_sub, transpose_smul, hRic, hg]

/-- **[Vacuum] `G_μν = 0 ⟺ R_μν = ½R g_μν`** — the vacuum Einstein equation (trace-reversed Ricci vanishing). -/
lemma einsteinTensor_vacuum_iff (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g : Matrix ι ι ℝ) :
    einsteinTensor Ric scalarR g = 0 ↔ Ric = (scalarR / 2) • g := by
  rw [einsteinTensor, sub_eq_zero]

/-- **[Einstein field equation] `G_μν = κ T_μν`** — the curvature (Einstein tensor) equals `κ = 8πG/c⁴` times
the stress-energy tensor. -/
def einsteinFieldEquation (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ) (κ : ℝ) : Prop :=
  einsteinTensor Ric scalarR g = κ • T

/-- **[With cosmological constant] `G_μν + Λ g_μν = κ T_μν`** — the Einstein field equation with the
cosmological term `Λ` (the candidate dark-energy term). -/
def einsteinFieldEquationCosmological (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (Λ κ : ℝ) : Prop :=
  einsteinTensor Ric scalarR g + Λ • g = κ • T

/-- **[Contracted Bianchi ⟹ conservation] `∇^μ G_μν = 0 ⟹ ∇^μ T_μν = 0`.** The divergence-free Einstein
tensor (the contracted Bianchi identity `∇^μ G_μν = 0`) forces the stress-energy to be conserved — the
diffeomorphism-invariance / consistency of the field equation `G = κT` (`κ ≠ 0`). -/
lemma bianchi_implies_conservation (Div : Matrix ι ι ℝ →ₗ[ℝ] (ι → ℝ))
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ) (κ : ℝ)
    (hEFE : einsteinFieldEquation Ric scalarR g T κ) (hBianchi : Div (einsteinTensor Ric scalarR g) = 0)
    (hκ : κ ≠ 0) : Div T = 0 := by
  unfold einsteinFieldEquation at hEFE
  rw [hEFE, map_smul] at hBianchi
  exact (smul_eq_zero.mp hBianchi).resolve_left hκ

/-! ## Verifying solutions against the field equation -/

/-- **A metric is a vacuum solution** when its Einstein tensor vanishes, `G_μν = 0` — equivalently
`R_μν = ½R g_μν` (`einsteinTensor_vacuum_iff`). -/
def IsVacuumSolution (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g : Matrix ι ι ℝ) : Prop :=
  einsteinTensor Ric scalarR g = 0

/-- **A vacuum solution satisfies the source-free Einstein field equation** `G_μν = κ·0`, for every
coupling `κ`: the field-equation check passes on a vacuum metric with vanishing stress-energy. -/
theorem IsVacuumSolution.satisfies_einsteinFieldEquation {Ric g : Matrix ι ι ℝ} {scalarR κ : ℝ}
    (h : IsVacuumSolution Ric scalarR g) : einsteinFieldEquation Ric scalarR g 0 κ := by
  rw [einsteinFieldEquation, h, smul_zero]

/-- **A Ricci-flat, scalar-flat metric is a vacuum solution** `R_μν = 0 ∧ R = 0 ⟹ G_μν = 0`. Every
Ricci-flat spacetime is verified against the vacuum field equation through this bridge: Minkowski
(`Curvature.RiemannCurvatureTensor.flat_riemann_curvature_vanishes`), Schwarzschild
(`Curvature.MoulinSchwarzschildVacuum`), Kerr (`KerrSchildVacuum`, Ricci-flat by the exact Kerr–Schild
identity). -/
theorem ricciFlat_isVacuumSolution {Ric g : Matrix ι ι ℝ} {scalarR : ℝ}
    (hRic : Ric = 0) (hR : scalarR = 0) : IsVacuumSolution Ric scalarR g := by
  rw [IsVacuumSolution, einsteinTensor, hRic, hR]; simp

/-- **A Ricci-flat metric solves the vacuum Einstein field equation** `R_μν = 0 ⟹ G_μν = κ·0`. -/
theorem ricciFlat_satisfies_einsteinFieldEquation {Ric g : Matrix ι ι ℝ} {scalarR κ : ℝ}
    (hRic : Ric = 0) (hR : scalarR = 0) : einsteinFieldEquation Ric scalarR g 0 κ :=
  (ricciFlat_isVacuumSolution hRic hR).satisfies_einsteinFieldEquation

/-- **Verifying a sourced solution** `G_μν = κ T_μν ⟹` the field equation holds with source `T`: a
metric whose Einstein tensor equals `κ T` is a solution for the stress-energy `T` (the direct
verification condition, e.g. the electrovacuum and FLRW families). -/
theorem satisfies_einsteinFieldEquation_of_einsteinTensor_eq {Ric g T : Matrix ι ι ℝ} {scalarR κ : ℝ}
    (h : einsteinTensor Ric scalarR g = κ • T) : einsteinFieldEquation Ric scalarR g T κ := h

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean

end
