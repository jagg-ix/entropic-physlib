/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ExteriorCalculusFrame
public import Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge

/-!
# Linking the exterior calculus to Weyl–Cartan gravity

Ties the frame exterior calculus (`ExteriorCalculusFrame`: `∧`, `⌟`, `d`) to the concrete Weyl–Cartan
curvature of `WeylCartanDilatonicCharge` (`homotheticCurvature`, the first-pair trace of the Riemann
tensor). The two descriptions of the dilatonic field strength meet:

* the **trace-based homothetic curvature** `Rᵃ_αcd` is a genuine exterior-calculus **2-form** — it is
  antisymmetric (`homotheticCurvature_isAntisym`, from `homotheticCurvature_antisymm`);
* the paper's **Weyl force one-form** `ē_σ ⌟ Rᵃ_α` (Eq. 3.2) is the interior product `interiorTwo` of
  the frame vector with that curvature (`weylForceOneForm`);
* it **vanishes in a metric-compatible (Riemann–Cartan) space**
  (`weylForceOneForm_zero_of_metricCompatible`) — Corollary 3 as a statement about the exterior-
  calculus force one-form, from `homotheticCurvature_zero_of_metricCompatible`.

So the abstract `⌟` of the exterior calculus, applied to the concrete `Rᵃ_α`, reproduces the paper's
dilatonic (Weyl) force — and the observability Corollary 3 becomes the vanishing of that one-form
where the nonmetricity is absent. (`Rᵃ_α = ½ dQ` of Eq. A.8 identifies this trace curvature with the
exterior derivative `dilatonicFieldStrength` of the Weyl one-form.)


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WeylCartanExteriorCalculus

open Physlib.QuantumMechanics.ComplexAction.ExteriorCalculusFrame
open Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge
open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*} [Fintype ι]

/-- **The homothetic curvature is an exterior-calculus 2-form**: the first-pair trace `Rᵃ_αcd`
(`WeylCartanDilatonicCharge.homotheticCurvature`) is antisymmetric, hence an `ExteriorCalculusFrame.
TwoForm` — the dilatonic field strength `Rᵃ_α = ½ dQ` as a genuine form. -/
lemma homotheticCurvature_isAntisym (gInv : ι → ι → ℝ) (Rm : RiemannTensor ι)
    (h : IsRiemannCurvature Rm) : IsAntisym (homotheticCurvature gInv Rm) :=
  fun c d => homotheticCurvature_antisymm gInv Rm h c d

/-- **The Weyl force one-form** `ē_σ ⌟ Rᵃ_α` (Babourova–Frolov Eq. 3.2): the interior product of the
frame vector with the homothetic curvature — the abstract `⌟` of the exterior calculus applied to the
concrete curvature 2-form. -/
noncomputable def weylForceOneForm (v : ι → ℝ) (gInv : ι → ι → ℝ) (Rm : RiemannTensor ι) : OneForm ι :=
  interiorTwo v (homotheticCurvature gInv Rm)

/-- **Corollary 3, as an exterior-calculus one-form**: in a metric-compatible (Riemann–Cartan) space
the Weyl force one-form `ē_σ ⌟ Rᵃ_α` vanishes — no nonmetricity, no dilatonic field strength, no Weyl
force, whatever the frame vector. -/
lemma weylForceOneForm_zero_of_metricCompatible (v : ι → ℝ) (gInv : ι → ι → ℝ) (Rm : RiemannTensor ι)
    (h : IsRiemannCurvature Rm) (hsym : ∀ a e, gInv a e = gInv e a) (j : ι) :
    weylForceOneForm v gInv Rm j = 0 := by
  unfold weylForceOneForm interiorTwo
  simp [homotheticCurvature_zero_of_metricCompatible gInv Rm h hsym]

end Physlib.QuantumMechanics.ComplexAction.WeylCartanExteriorCalculus
