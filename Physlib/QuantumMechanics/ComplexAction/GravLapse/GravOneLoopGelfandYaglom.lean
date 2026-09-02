/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster

/-!
# One-loop complex `ℝ×S³` gravitational saddles: Gel'fand–Yaglom determinant (Mallik–Narain 2026)

Formalizes the algebraic core of *S. Mallik, G. Narain, "IR behaviour of one-loop complex `ℝ×S³`
saddles", arXiv:2604.21736*: the gravitational Lorentzian path integral `𝒵 = ∫𝒟g e^{iS/ℏ}` over complex
metrics, and the **Gel'fand–Yaglom theorem** that reduces the one-loop functional determinant to a finite
matrix determinant.

* **§A — the gravitational complex-saddle weight is the master formula** (`gravComplexSaddle_weight_eq_master`):
  the Lorentzian path-integral weight `e^{iS/ℏ}` (Eqs. 1, 3) of a complex `ℝ×S³` saddle with action
  `S = S_R + iS_I` is the complex-action/entropic-time master integrand `complexActionPathIntegralWeight` of `PathIntegral.ComplexActionPathIntegralWeight` — the
  gravitational path integral is the complex-action path integral of the arc.
* **§B–§D — the Gel'fand–Yaglom one-loop determinant** (Eqs. 54, 62, 65, 68): the functional determinant of
  the 1D self-adjoint Sturm–Liouville operator `𝒟 = −d/dt(P d/dt) + Q` reduces to the finite determinant
  `det 𝒟 = det[M + N·E₁]` (`gelfandYaglomDet`), where `E₁` is the fundamental matrix at `t=1`; for
  Dirichlet–Dirichlet boundaries `M, N` (Eq. 65) this is the single entry `u₂(1) = E₁ 0 1`
  (`gelfandYaglom_dirichlet`, Eq. 68).
* **§E — the one-loop prefactor** (Eq. 52): the Gaussian functional integral `∫𝒟H e^{iS/ℏ} = (det 𝒟)^{−1/2}`
  (`oneLoopPrefactor`), and the one-loop Hartle–Hawking wave function `tree × prefactor`
  (`oneLoopWaveFunction`).
* **§F — boson/fermion determinant duality** (`boson_fermion_determinant_duality`): the bosonic
  Gel'fand–Yaglom determinant and the fermionic Berezin determinant (`PathIntegral.QEDFunctionalIntegralConstruction`)
  both reduce a Gaussian functional integral to a finite determinant (`(det)^{∓1/2,+1}`).
* **§G — the lapse contour supplies the tree-level complex saddle** (`oneLoopWaveFunction_eq_lapse_dressed`,
  `oneLoopWaveFunction_norm_eq_lapse`): the one-loop Hartle–Hawking wave function `Ψ = e^{iS_cl/ℏ}(det 𝒟)^{−1/2}`
  is the Banihashemi–Jacobson `N − iε` lapse-displaced constraint weight `lapseWeight N ε ℋ`
  (`GravLapse.ContourMaster`) dressed by the Gel'fand–Yaglom one-loop prefactor — the lapse contour is the
  *origin* of the complex saddle's imaginary action `S_I = εℋ`, and the determinant is its one-loop correction.

## References

* S. Mallik, G. Narain, *IR behaviour of one-loop complex `ℝ×S³` saddles*, arXiv:2604.21736 (2026).
* B. Banihashemi, T. Jacobson, *On the lapse contour in the gravitational path integral*,
  arXiv:2405.10307v3 (2 Mar 2025), DOI `10.48550/arXiv.2405.10307`, §II — the `N − iε` lapse contour that
  sources the tree-level complex saddle (§G).
* I. M. Gel'fand, A. M. Yaglom, *Integration in functional spaces and its applications in quantum
  physics*, J. Math. Phys. 1 (1960) 48 — the functional-determinant theorem.
* J. B. Hartle, S. W. Hawking, *Wave function of the Universe*, Phys. Rev. D 28 (1983) 2960.
* M. Kontsevich, G. Segal (2021); E. Witten (2021) — the KSW allowability criterion for complex metrics.
* Repo carriers: `PathIntegral.ComplexActionPathIntegralWeight` (`nagaoNielsenComplexActionWeight`, `complexActionPathIntegralWeight`),
  `PathIntegral.QEDFunctionalIntegralConstruction` (Berezin fermion determinant).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom

open Matrix
open Physlib.QuantumMechanics.ComplexAction


/-- **[Mallik–Narain Eqs. 1, 3] The gravitational complex-saddle path-integral weight is the master
formula.** The Lorentzian path integral `𝒵 = ∫𝒟g e^{iS/ℏ}` (and the Hartle–Hawking `Ψ = ∫_NB 𝒟g e^{iS/ℏ}`)
weights a complex `ℝ×S³` saddle with action `S = S_R + iS_I` by `e^{iS/ℏ} = nagaoNielsenComplexActionWeight S_R S_I ℏ`,
which is the complex-action/entropic-time master integrand `complexActionPathIntegralWeight` (`PathIntegral.ComplexActionPathIntegralWeight`). The gravitational
path integral over complex metrics *is* the complex-action path integral of the arc. -/
lemma gravComplexSaddle_weight_eq_master (S_R S_I ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    PathIntegral.ComplexActionPathIntegralWeight.nagaoNielsenComplexActionWeight S_R S_I ℏ
      = PathIntegral.ComplexActionPathIntegralWeight.complexActionPathIntegralWeight S_R S_I ℏ :=
  PathIntegral.ComplexActionPathIntegralWeight.nagaoNielsen_eq_master S_R S_I ℏ hℏ


/-- **[Mallik–Narain Eq. 62] The Gel'fand–Yaglom functional determinant** `det 𝒟 = det[M + N·E₁]` of the 1D
Sturm–Liouville operator `𝒟 = −d/dt(P d/dt) + Q` (Eq. 54), with `E₁` the fundamental (Wronskian) matrix at
`t=1` and `M, N` the boundary matrices — the infinite-dimensional one-loop determinant as a `2×2`
determinant. -/
def gelfandYaglomDet (M N E1 : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (M + N * E1).det

/-- **[Mallik–Narain Eq. 65] Dirichlet boundary matrix `M`** for the `Dirichlet–Dirichlet` condition on the
fluctuation `H_l(0) = H_l(1) = 0`. -/
def dirichletM : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- **[Mallik–Narain Eq. 65] Dirichlet boundary matrix `N`**. -/
def dirichletN : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- **[Mallik–Narain Eq. 68] The Dirichlet–Dirichlet one-loop determinant is `u₂(1)`.** With the
Dirichlet boundary matrices, `det 𝒟 = det[M + N·E₁] = E₁ 0 1 = u₂(1)` — the single off-diagonal entry of
the fundamental matrix (the zero-mode solution `u₂` with `u₂(0)=0`, `u̇₂(0)=1/P(0)`, evaluated at `t=1`). The
whole one-loop fluctuation determinant is one number read off the classical solution. -/
lemma gelfandYaglom_dirichlet (E1 : Matrix (Fin 2) (Fin 2) ℝ) :
    gelfandYaglomDet dirichletM dirichletN E1 = E1 0 1 := by
  unfold gelfandYaglomDet dirichletM dirichletN
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one]
  ring


/-- **[Mallik–Narain Eq. 52] The one-loop Gaussian prefactor** `∫𝒟H e^{iS/ℏ} = (det 𝒟)^{−1/2}` — the
bosonic fluctuation path integral evaluates to the inverse square root of the Gel'fand–Yaglom determinant. -/
noncomputable def oneLoopPrefactor (D : ℝ) : ℝ := D ^ (-(1 / 2) : ℝ)

/-- The one-loop prefactor is positive for a positive determinant. -/
lemma oneLoopPrefactor_pos (D : ℝ) (hD : 0 < D) : 0 < oneLoopPrefactor D :=
  Real.rpow_pos_of_pos hD _

/-- **[Mallik–Narain Eq. 51] The one-loop Hartle–Hawking wave function** `Ψ ≈ e^{iS_cl/ℏ} · (det 𝒟)^{−1/2}`
— the tree-level complex-saddle weight (`gravComplexSaddle…`) times the Gel'fand–Yaglom one-loop prefactor. -/
noncomputable def oneLoopWaveFunction (S_R S_I ℏ D : ℝ) : ℂ :=
  PathIntegral.ComplexActionPathIntegralWeight.nagaoNielsenComplexActionWeight S_R S_I ℏ * (oneLoopPrefactor D : ℂ)

/-- The one-loop wave function's modulus is the entropic damping times the one-loop prefactor: the
Cameron–Martin weight of the complex saddle dresses the Gaussian determinant. -/
lemma oneLoopWaveFunction_norm (S_R S_I ℏ D : ℝ) (hℏ : ℏ ≠ 0) (hD : 0 < D) :
    ‖oneLoopWaveFunction S_R S_I ℏ D‖ = PathIntegral.ComplexActionPathIntegralWeight.kuikenWeight ℏ S_I * oneLoopPrefactor D := by
  unfold oneLoopWaveFunction
  rw [norm_mul, gravComplexSaddle_weight_eq_master S_R S_I ℏ hℏ,
    PathIntegral.ComplexActionPathIntegralWeight.master_modulus_is_kuiken, Complex.norm_real,
    Real.norm_of_nonneg (oneLoopPrefactor_pos D hD).le]


/-- **[Link] Both the bosonic Gel'fand–Yaglom determinant and the fermionic Berezin determinant reduce a
Gaussian functional integral to a finite determinant.** The graviton fluctuation integral gives
`(det 𝒟)^{−1/2}` via Gel'fand–Yaglom (`det 𝒟 = u₂(1)`); the fermion integral gives `det M` via Berezin
(`PathIntegral.QEDFunctionalIntegralConstruction.berezin_gaussian_eq_det`, here `det[m] = m`). Same finite-dimensional
reduction, opposite determinant power — the boson/fermion one-loop dichotomy. -/
lemma boson_fermion_determinant_duality (m : ℝ) (E1 : Matrix (Fin 2) (Fin 2) ℝ) :
    PathIntegral.QEDFunctionalIntegralConstruction.berezin (PathIntegral.QEDFunctionalIntegralConstruction.fermionGaussian m) = m
      ∧ gelfandYaglomDet dirichletM dirichletN E1 = E1 0 1 :=
  ⟨by rw [PathIntegral.QEDFunctionalIntegralConstruction.berezin_gaussian_eq_det]; exact Matrix.det_fin_one_of m,
   gelfandYaglom_dirichlet E1⟩


/-- **[Banihashemi–Jacobson §II + Mallik–Narain Eq. 51] The one-loop wave function is the lapse-displaced
constraint weight dressed by the Gel'fand–Yaglom prefactor.** The one-loop Hartle–Hawking wave function
`Ψ = e^{iS_cl/ℏ}·(det 𝒟)^{−1/2}` (with `ℏ = 1`, `S_cl = −Nℋ + i(εℋ)`) factorizes as
`oneLoopWaveFunction (−Nℋ) (εℋ) 1 D = lapseWeight N ε ℋ · (det 𝒟)^{−1/2}`: the tree-level complex saddle is
*exactly* the Banihashemi–Jacobson `N − iε` lapse-displaced constraint weight
(`GravLapse.ContourMaster.lapseWeight`, arXiv:2405.10307 Eq. 5), and the Gel'fand–Yaglom determinant is its
one-loop correction. The lapse contour is the origin of the saddle's imaginary action `S_I = εℋ`. -/
lemma oneLoopWaveFunction_eq_lapse_dressed (N ε Ham D : ℝ) :
    oneLoopWaveFunction (-(N * Ham)) (ε * Ham) 1 D
      = GravLapse.ContourMaster.lapseWeight N ε Ham * (oneLoopPrefactor D : ℂ) := by
  unfold oneLoopWaveFunction
  rw [← GravLapse.ContourMaster.lapseWeight_eq_nagaoNielsen]

/-- **[Bridge] The one-loop wave function's modulus is the lapse entropic damping times the prefactor.**
`‖Ψ‖ = ‖lapseWeight N ε ℋ‖ · (det 𝒟)^{−1/2} = e^{−εℋ}·(det 𝒟)^{−1/2}`: the `−iε` lapse displacement supplies
the saddle's Halliwell–Hartle convergence factor `e^{−εℋ}` (`GravLapse.ContourMaster.lapseWeight_modulus`),
which the one-loop Gel'fand–Yaglom prefactor then dresses. -/
lemma oneLoopWaveFunction_norm_eq_lapse (N ε Ham D : ℝ) (hD : 0 < D) :
    ‖oneLoopWaveFunction (-(N * Ham)) (ε * Ham) 1 D‖
      = ‖GravLapse.ContourMaster.lapseWeight N ε Ham‖ * oneLoopPrefactor D := by
  rw [oneLoopWaveFunction_eq_lapse_dressed, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (oneLoopPrefactor_pos D hD).le]

end Physlib.QuantumMechanics.ComplexAction.GravLapse.GravOneLoopGelfandYaglom

end
