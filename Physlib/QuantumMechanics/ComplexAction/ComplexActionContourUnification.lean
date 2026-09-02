/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ActionAngleNagaoNielsenComplexAction
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour
public import Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenFermionPathIntegralsTopologicalPhases
public import Physlib.QuantumMechanics.ComplexAction.Dirac.FoldyWouthuysenExact
public import Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
public import Physlib.QuantumMechanics.ComplexAction.ActionAngleGeneralizedTrigArithmetic

/-!
# One entropic weight across the complex-action contours: Nagao–Nielsen, Witten, Picard–Lefschetz, gravitational lapse, Dirac

This makes the action-angle complex-momentum connection **explicit** and unifies it with the other complex-action
**contour** constructions in the repository. All of them deform the integration contour into the complex plane and
weight it by the master complex-action weight `e^{(i/ℏ)(S_R + iS_I)}`, whose modulus is the entropic damping
`kuikenWeight ℏ S_I = e^{−S_I/ℏ}`. They differ only in what supplies the imaginary action `S_I`.

**The explicit action-angle connection.** In the classically-forbidden region the action-angle momentum is
imaginary (`ActionAngleNagaoNielsenComplexAction.nnReducedMomentum = i√(q^{α+1}/τ² − 2I/τ)`), so the action
increment `p·dq` is `i·(√(q^{α+1}/τ² − 2I/τ)·dq)` — **purely imaginary**: it is `i` times the WKB barrier integrand.
The imaginary momentum *is* the imaginary action `S_I = ∫|p|dq`, and the weight is damped by `e^{−S_I/ℏ}` — the
tunneling amplitude.

**One weight, four contours** — each contour weight's modulus is `kuikenWeight` of its own `S_I`:

| contour | module | `S_I` |
|---|---|---|
| **Nagao–Nielsen** (action-angle tunneling) | `ActionAngleNagaoNielsenComplexAction` | `∫|p|dq` (barrier) |
| **Witten** (Chern–Simons analytic continuation) | `ChernSimons.WittenFermionPathIntegralsTopologicalPhases` | `S_I` (same `nagaoNielsenComplexActionWeight`) |
| **Picard–Lefschetz** (Lefschetz-thimble / Morse flow) | `OperatorAlgebra.PicardLefschetzMorseContour` | `actionIm` along the flow |
| **gravitational lapse** (`−iε` contour) | `GravLapse.ContourMaster` | `εℋ` |
| **Dirac/Foldy** (relativistic mass shell) | `Dirac.FoldyWouthuysenExact` | contour coordinate `E+i|p|`, with `L=m²` |

* **§A — the explicit connection.** **`nnReducedMomentum_action_increment`** (`p·dq = i·(barrier integrand)`, the
  imaginary action).
* **§B — the contour unification.** `picardLefschetz_weightAt_modulus_is_kuiken`;
  **`contour_weights_unified`** — the Nagao–Nielsen/Witten, gravitational-lapse and Picard–Lefschetz contour
  weights all have modulus `kuikenWeight 1 S_I` at a common imaginary action.
* **§C — the Dirac/Foldy relativistic contour.** `foldyDiracMassShellContour` packages the relativistic
  mass shell as `q = E+i|p|`; `foldyDiracMassShellContour_mass` proves `L(q)=m²`; and
  `fw_intertwine_of_massShellContour` derives the exact Foldy-Wouthuysen intertwining from that contour
  equation.
* **§D — the decoherence-functional link.** `foldyDiracContourWeight` is the complex-action history
  weight with `S_I = |p|`; `foldyDiracContourWeight_eq_historyWeight` identifies it with the existing
  Sorkin-Johnston `historyWeight`; and `foldyDiracContourDecoherenceFunctional_diag_re` computes the
  Born diagonal of the induced rank-one decoherence functional.

**Scope.** Exact `Complex`/`Real.exp` identities; reuses each contour's own weight (`nnReducedMomentum`,
`weightAt`, `lapseWeight`, `nagaoNielsenComplexActionWeight`) and the Sorkin-Johnston history kernel
on the shared `kuikenWeight` hub. ## References

* Reuses `ActionAngleNagaoNielsenComplexAction`, `PicardLefschetzMorseContour`, `ContourMaster`,
  `WittenFermionPathIntegralsTopologicalPhases` on `PathIntegral.ComplexActionPathIntegralWeight`, and
  `Dirac.FoldyWouthuysenExact` on the relativistic mass-shell contour, plus
  `DecoherenceFunctionalSorkinJohnston` for the induced history decoherence kernel.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.ActionAngleNagaoNielsenComplexAction
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.PicardLefschetzMorseContour
open Physlib.QuantumMechanics.ComplexAction.GravLapse.ContourMaster
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.Dirac.FourSpinorDiracHamiltonian
open Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexActionContourUnification


/-- **The action increment of the forbidden-region momentum is purely imaginary** — the action-angle momentum
`p = i√(q^{α+1}/τ² − 2I/τ)` (`nnReducedMomentum`) times a real displacement `dq` is `i·(√(q^{α+1}/τ² − 2I/τ)·dq)`:
`i` times the WKB barrier integrand. So the imaginary momentum *is* the imaginary action `S_I = ∫|p|dq`, and the
complex-action weight is damped by `e^{−S_I/ℏ}` — the tunneling amplitude. This makes the
`ActionAngleNagaoNielsenComplexAction` connection explicit. -/
lemma nnReducedMomentum_action_increment (I α τ q dq : ℝ) :
    nnReducedMomentum I α τ q * (dq : ℂ)
      = Complex.I * ((Real.sqrt (q ^ (α + 1) / τ ^ 2 - 2 * I / τ) * dq : ℝ) : ℂ) := by
  unfold nnReducedMomentum
  push_cast
  ring


/-- **The Picard–Lefschetz (Lefschetz-thimble) weight is the entropic weight** — along the Morse/Stokes flow the
contour weight's modulus is `kuikenWeight ℏ (actionIm)`: the imaginary action accumulated on the thimble is the
entropic damping. -/
lemma picardLefschetz_weightAt_modulus_is_kuiken {α : Type*}
    (F : PicardLefschetzMorseFlow α) (hbar : ℝ) (n : ℕ) :
    ‖F.weightAt hbar n‖ = kuikenWeight hbar (F.actionIm (F.point n)) := by
  rw [F.weightAt_norm hbar n, kuikenWeight]

/-- **One entropic weight across the complex-action contours** — at a common imaginary action `S_I`, the
Nagao–Nielsen / Witten complex-action weight (`nagaoNielsenComplexActionWeight`, the weight Witten's Chern–Simons
analytic continuation reuses), the gravitational-lapse contour weight (`lapseWeight`) and the Picard–Lefschetz
Lefschetz-thimble weight (`weightAt`) **all** have modulus `kuikenWeight 1 S_I = e^{−S_I}`. The tunneling barrier,
the Chern–Simons `η`-invariant, the thimble descent and the `−iε` lapse are four faces of one contour-deformation
entropic weight. -/
lemma contour_weights_unified {α : Type*} (F : PicardLefschetzMorseFlow α)
    (S_R S_I N ε Ham : ℝ) (n : ℕ)
    (hLapse : ε * Ham = S_I) (hPL : F.actionIm (F.point n) = S_I) :
    ‖nagaoNielsenComplexActionWeight S_R S_I 1‖ = kuikenWeight 1 S_I
      ∧ ‖lapseWeight N ε Ham‖ = kuikenWeight 1 S_I
      ∧ ‖F.weightAt 1 n‖ = kuikenWeight 1 S_I := by
  refine ⟨?_, ?_, ?_⟩
  · rw [nagaoNielsen_eq_master _ _ _ one_ne_zero, master_modulus_is_kuiken]
  · rw [lapseWeight_modulus, hLapse]
  · rw [picardLefschetz_weightAt_modulus_is_kuiken, hPL]

/-- **The Foldy/Dirac relativistic mass-shell contour** `q = E + i|p|`. Its real coordinate is the
energy `E`; its imaginary coordinate is the spatial momentum magnitude `|p|`. The Nagao-Nielsen
Lorentzian contour form then reads `L(q)=E²-|p|²`. -/
noncomputable def foldyDiracMassShellContour (E p1 p2 p3 : ℝ) : ℂ :=
  (E : ℂ) + ((Real.sqrt (spatialMomentumSq p1 p2 p3) : ℝ) : ℂ) * Complex.I

/-- **The Dirac/Foldy contour realizes the relativistic quadratic form**:
`L(E+i|p|)=E²-|p|²`. -/
lemma foldyDiracMassShellContour_lorentzianForm (E p1 p2 p3 : ℝ) :
    lorentzianForm (foldyDiracMassShellContour E p1 p2 p3)
      = E ^ 2 - spatialMomentumSq p1 p2 p3 := by
  unfold foldyDiracMassShellContour lorentzianForm
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Real.sq_sqrt (spatialMomentumSq_nonneg p1 p2 p3)]

/-- **The relativistic Dirac mass shell is a contour level set**: if
`E²=|p|²+m²`, then the contour point `E+i|p|` lies on `L=m²`. -/
lemma foldyDiracMassShellContour_mass (E p1 p2 p3 m : ℝ)
    (hE : E ^ 2 = spatialMomentumSq p1 p2 p3 + m ^ 2) :
    lorentzianForm (foldyDiracMassShellContour E p1 p2 p3) = m ^ 2 := by
  rw [foldyDiracMassShellContour_lorentzianForm]
  linarith

/-- **The massive Dirac contour is timelike** when `m ≠ 0`: `L(E+i|p|)=m²>0`. -/
lemma foldyDiracMassShellContour_timelike (E p1 p2 p3 m : ℝ) (hm : m ≠ 0)
    (hE : E ^ 2 = spatialMomentumSq p1 p2 p3 + m ^ 2) :
    0 < lorentzianForm (foldyDiracMassShellContour E p1 p2 p3) := by
  rw [foldyDiracMassShellContour_mass E p1 p2 p3 m hE]
  exact sq_pos_of_ne_zero hm

/-- **The exact Foldy-Wouthuysen intertwining from the contour mass-shell equation.** If the
relativistic contour point `q=E+i|p|` satisfies `L(q)=m²`, then the on-shell identity required by
`fw_intertwine` follows, so the Dirac Hamiltonian is exactly diagonalized to `Eβ`. -/
lemma fw_intertwine_of_massShellContour (p1 p2 p3 m E : ℝ)
    (hContour : lorentzianForm (foldyDiracMassShellContour E p1 p2 p3) = m ^ 2) :
    fwOperator p1 p2 p3 m E * diracHamiltonian4 p1 p2 p3 m
      = ((E : ℂ) • diracBeta) * fwOperator p1 p2 p3 m E := by
  have hform := foldyDiracMassShellContour_lorentzianForm E p1 p2 p3
  have hE : E ^ 2 = p1 ^ 2 + p2 ^ 2 + p3 ^ 2 + m ^ 2 := by
    unfold spatialMomentumSq at hform
    linarith
  exact fw_intertwine p1 p2 p3 m E hE

/-- **The Foldy/Dirac contour history weight** is the master complex-action weight with real part
`E` and imaginary action `|p| = sqrt(p₁²+p₂²+p₃²)`. -/
noncomputable def foldyDiracContourWeight (E p1 p2 p3 ℏ : ℝ) : ℂ :=
  complexActionPathIntegralWeight E (Real.sqrt (spatialMomentumSq p1 p2 p3)) ℏ

/-- **The Foldy/Dirac contour weight is the existing Sorkin-Johnston history weight.** The history
entropy parameter is `S_ent = 2|p|/ℏ`, so `historyWeight` has imaginary action
`(ℏ/2)S_ent = |p|`. -/
lemma foldyDiracContourWeight_eq_historyWeight (E p1 p2 p3 ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    foldyDiracContourWeight E p1 p2 p3 ℏ =
      historyWeight E (2 * Real.sqrt (spatialMomentumSq p1 p2 p3) / ℏ) ℏ := by
  unfold foldyDiracContourWeight historyWeight
  have hS :
      ℏ / 2 * (2 * Real.sqrt (spatialMomentumSq p1 p2 p3) / ℏ)
        = Real.sqrt (spatialMomentumSq p1 p2 p3) := by
    field_simp [hℏ]
  rw [hS]

/-- **The Foldy/Dirac contour weight has Kuiken damping** `‖w‖ = kuikenWeight ℏ |p|`. -/
lemma foldyDiracContourWeight_norm (E p1 p2 p3 ℏ : ℝ) :
    ‖foldyDiracContourWeight E p1 p2 p3 ℏ‖ =
      kuikenWeight ℏ (Real.sqrt (spatialMomentumSq p1 p2 p3)) := by
  rw [foldyDiracContourWeight, master_modulus_is_kuiken]

/-- **The rank-one decoherence functional induced by the Foldy/Dirac contour weight.** -/
noncomputable def foldyDiracContourDecoherenceFunctional {ι : Type*}
    (E p1 p2 p3 ℏ : ℝ) : ι → ι → ℂ :=
  decoherenceFunctional (fun _ : ι => foldyDiracContourWeight E p1 p2 p3 ℏ)

/-- **Product form of the Foldy/Dirac contour decoherence functional.** -/
lemma foldyDiracContourDecoherenceFunctional_apply {ι : Type*}
    (E p1 p2 p3 ℏ : ℝ) (α β : ι) :
    foldyDiracContourDecoherenceFunctional E p1 p2 p3 ℏ α β =
      foldyDiracContourWeight E p1 p2 p3 ℏ *
        (starRingEnd ℂ) (foldyDiracContourWeight E p1 p2 p3 ℏ) := by
  simp [foldyDiracContourDecoherenceFunctional, decoherenceFunctional_apply]

/-- **Born diagonal of the Foldy/Dirac contour decoherence functional.** Its diagonal equals the
squared contour damping, so the same `kuikenWeight` controls both contour damping and the diagonal
history probability. -/
lemma foldyDiracContourDecoherenceFunctional_diag_re {ι : Type*}
    (E p1 p2 p3 ℏ : ℝ) (α : ι) :
    (foldyDiracContourDecoherenceFunctional E p1 p2 p3 ℏ α α).re =
      (kuikenWeight ℏ (Real.sqrt (spatialMomentumSq p1 p2 p3))) ^ 2 := by
  rw [foldyDiracContourDecoherenceFunctional, decoherenceFunctional_diag_re,
    Complex.normSq_eq_norm_sq, foldyDiracContourWeight_norm]

/-- **On the Foldy mass-shell contour, the decoherence-functional Born diagonal depends on the
mass-shell gap** `E²-m²`: if `L(E+i|p|)=m²`, then `|p|²=E²-m²`, so the diagonal is
`kuikenWeight ℏ sqrt(E²-m²)` squared. -/
lemma foldyDiracContourDecoherenceFunctional_diag_re_of_massShellContour {ι : Type*}
    (E p1 p2 p3 m ℏ : ℝ) (α : ι)
    (hContour : lorentzianForm (foldyDiracMassShellContour E p1 p2 p3) = m ^ 2) :
    (foldyDiracContourDecoherenceFunctional E p1 p2 p3 ℏ α α).re =
      (kuikenWeight ℏ (Real.sqrt (E ^ 2 - m ^ 2))) ^ 2 := by
  rw [foldyDiracContourDecoherenceFunctional_diag_re]
  have hform := foldyDiracMassShellContour_lorentzianForm E p1 p2 p3
  have hp : spatialMomentumSq p1 p2 p3 = E ^ 2 - m ^ 2 := by
    linarith
  rw [hp]

end Physlib.QuantumMechanics.ComplexAction.ComplexActionContourUnification

/-! ## Generating functions as contour actions -/

namespace Physlib.QuantumMechanics.ComplexAction.GeneratingFunctionContourWeight

open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight

/-- **The generating function is the action `S_R` in the master weight**: the Hamilton
characteristic function `W = generatingF pFun a q` enters the master complex-action weight
as the real action, and its modulus is the entropic damping `kuikenWeight ℏ S_I` of the
imaginary contour-deformation part. -/
lemma generatingF_masterWeight_modulus_is_kuiken (pFun : ℝ → ℝ) (a q S_I ℏ : ℝ) :
    ‖complexActionPathIntegralWeight (generatingF pFun a q) S_I ℏ‖ = kuikenWeight ℏ S_I :=
  master_modulus_is_kuiken _ _ _

/-- **A real generating function is reversible**: with no imaginary action, the
generating-function weight is a pure phase with unit modulus. -/
lemma generatingF_real_reversible (pFun : ℝ → ℝ) (a q ℏ : ℝ) :
    ‖complexActionPathIntegralWeight (generatingF pFun a q) 0 ℏ‖ = 1 := by
  rw [generatingF_masterWeight_modulus_is_kuiken, kuikenWeight, zero_div, neg_zero, Real.exp_zero]

end Physlib.QuantumMechanics.ComplexAction.GeneratingFunctionContourWeight
