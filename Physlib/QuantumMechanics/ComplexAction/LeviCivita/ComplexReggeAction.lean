/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
public import Physlib.QFT.Wick.Consistency
public import Physlib.QuantumMechanics.ComplexAction.BenderIdentity

/-!
# The complex Regge action and Sorkin's Section II C action

The complex-action theory of this development has a **complex action** `S = S_R + i S_I` whose
path weight is `complexActionWeight S_R S_I ℏ = exp(iS/ℏ)` (`Physlib.QFT.Wick.Consistency`), with
entropic modulus `‖exp(iS/ℏ)‖ = exp(−S_I/ℏ)`. Sorkin (1975) Sec. II C gives the gravitational
action as `S_ℓ = Σ_b θ(b) A(b)` (`TetradInvariant.sorkinReggeAction`, the discretized `−½∫R√(−g)`).

This file complexifies Sorkin's action — allowing a **complex defect** `θ = θ_R + i θ_I`, as in the
complex-action theory — and links it to the complex action weight:

* `complexReggeAction` — `Σ_b A(b) θ(b)` with `θ : Bone → ℂ`;
* `complexReggeAction_re` / `complexReggeAction_im` — its real and imaginary parts are Sorkin's real
  Regge action of the real and imaginary defects respectively;
* `reggeAction_complexActionWeight_norm` — the Regge path weight's entropic modulus is
  `exp(−S_I/ℏ)` with `S_I` the **imaginary (entropic) Regge action**: Sorkin's real action `S_R`
  fixes the phase, the imaginary defect fixes the damping;
* `reggeAction_real_defect_pure_phase` — a real defect (classical Regge gravity) gives a pure phase
  (no entropic damping), recovering the unitary limit.

## References

* R. Sorkin, "Time-evolution problem in Regge calculus", Phys. Rev. D **12**, 385 (1975)
  [`Sorkin:1975ah`], Sec. II C, Eq. (1) `S_ℓ = Σ_b η(b) A(b)`. Reuses `LeviCivita.TetradInvariant`
  (`sorkinReggeAction`, `cuspActionPerArea`), `QFT.Wick.Consistency` (`complexActionWeight`), and
  `Physlib.QuantumMechanics.ComplexAction.BenderIdentity` (`stationaryComplexAction_split`).

No new axioms.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction

open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant
open Physlib.QFT.Wick.Consistency
open Physlib.QuantumMechanics.ComplexAction

/-- The **complex Regge action** `Σ_b A(b) θ(b)`: Sorkin's Sec. II C action `Σ_b θ(b) A(b)` with a
complex defect `θ = θ_R + i θ_I` (the complexified curvature of the complex-action theory). -/
noncomputable def complexReggeAction {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect : Bone → ℂ) : ℂ :=
  ∑ b : Bone, (area b : ℂ) * defect b

/-- The **real part of the complex Regge action is Sorkin's real Regge action** of the real defect —
the classical `−½∫R√(−g)`. -/
theorem complexReggeAction_re {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect : Bone → ℂ) :
    (complexReggeAction area defect).re = sorkinReggeAction area (fun b => (defect b).re) := by
  unfold complexReggeAction sorkinReggeAction reggeAction
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [Complex.mul_re]

/-- The **imaginary part of the complex Regge action is the entropic Regge action** of the imaginary
defect. -/
theorem complexReggeAction_im {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect : Bone → ℂ) :
    (complexReggeAction area defect).im = sorkinReggeAction area (fun b => (defect b).im) := by
  unfold complexReggeAction sorkinReggeAction reggeAction
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [Complex.mul_im]

/-- **The Regge path weight's entropic modulus is the imaginary Regge action**: the complex-action
weight of Sorkin's complex Regge action has `‖exp(iS/ℏ)‖ = exp(−S_I/ℏ)` with `S_I` the imaginary
(entropic) Regge action `Σ_b A(b) (Im θ)(b)` — the real defect sets the phase, the imaginary defect
the damping. -/
theorem reggeAction_complexActionWeight_norm {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect : Bone → ℂ) (ℏ : ℝ) :
    ‖complexActionWeight (complexReggeAction area defect).re (complexReggeAction area defect).im ℏ‖
      = Real.exp (-(sorkinReggeAction area (fun b => (defect b).im) / ℏ)) := by
  rw [norm_complexActionWeight, complexReggeAction_im]

/-- **A real defect gives a pure phase** (unitary limit): classical Regge gravity `θ ∈ ℝ` has
`‖exp(iS/ℏ)‖ = 1` — no entropic damping. -/
theorem reggeAction_real_defect_pure_phase {Bone : Type*} [Fintype Bone]
    (area : Bone → ℝ) (defect : Bone → ℂ) (ℏ : ℝ) (h : ∀ b, (defect b).im = 0) :
    ‖complexActionWeight (complexReggeAction area defect).re
        (complexReggeAction area defect).im ℏ‖ = 1 := by
  rw [reggeAction_complexActionWeight_norm]
  have : sorkinReggeAction area (fun b => (defect b).im) = 0 := by
    unfold sorkinReggeAction reggeAction; simp [h]
  rw [this]; simp

/-! ## The complex thatch equation

The complex-action theory varies a complex action; by `stationaryComplexAction_split`
(`Physlib.QuantumMechanics.ComplexAction`) its stationarity splits into real and imaginary parts.
For the complex Regge action this means the **complex thatch equation** `G(ij) = 0` splits into the
classical real thatch equation `G_R(ij) = 0` (`−½∫R√−g` stationary) and the entropic imaginary thatch
equation `G_I(ij) = 0`. -/

/-- **Sorkin Eq. (2), complexified**: the derivative of the complex Regge action along one squared
leg length is `Σ_b (∂A(b)/∂l_ij²) θ(b)` with a complex defect — the complex thatch equation
`G(ij) ∈ ℂ` (reuses the real derivative structure via `HasDerivAt.sum`). -/
theorem hasDerivAt_complexReggeAction_leg {Bone : Type*} [Fintype Bone]
    (defect : Bone → ℂ) (boneArea : Bone → ℝ → ℝ) (dArea : Bone → ℝ) (t : ℝ)
    (h : ∀ b, HasDerivAt (boneArea b) (dArea b) t) :
    HasDerivAt (fun s => ∑ b : Bone, ((boneArea b s : ℝ) : ℂ) * defect b)
      (∑ b : Bone, ((dArea b : ℝ) : ℂ) * defect b) t := by
  have hfun : (fun s => ∑ b : Bone, ((boneArea b s : ℝ) : ℂ) * defect b)
      = ∑ b : Bone, (fun s => ((boneArea b s : ℝ) : ℂ) * defect b) := by
    funext s; rw [Finset.sum_apply]
  rw [hfun]
  exact HasDerivAt.sum (fun b _ => ((h b).ofReal_comp).mul_const (defect b))

/-- The complex thatch equation `G(ij) = Σ_b (∂A/∂l_ij²) θ(b)` decomposes into its real thatch
equation `G_R = Σ_b (∂A/∂l_ij²)(Re θ)` and imaginary thatch equation `G_I = Σ_b (∂A/∂l_ij²)(Im θ)`. -/
theorem complexThatch_split {Bone : Type*} [Fintype Bone]
    (defect : Bone → ℂ) (dArea : Bone → ℝ) :
    ∑ b : Bone, ((dArea b : ℝ) : ℂ) * defect b
      = ((∑ b : Bone, dArea b * (defect b).re : ℝ) : ℂ)
        + Complex.I * ((∑ b : Bone, dArea b * (defect b).im : ℝ) : ℂ) := by
  rw [Complex.ext_iff]
  refine ⟨?_, ?_⟩ <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.re_sum,
      Complex.im_sum, Complex.ofReal_re, Complex.ofReal_im]

/-- **The complex thatch equation splits into a classical and an entropic thatch equation** — reusing
the complex-action variational split `stationaryComplexAction_split`: the complex Einstein/thatch
equation `G(ij) = 0` holds iff the real (classical, `−½∫R√−g`) thatch equation and the imaginary
(entropic) thatch equation both vanish. -/
theorem complexThatch_stationary_iff {Bone : Type*} [Fintype Bone]
    (defect : Bone → ℂ) (dArea : Bone → ℝ) :
    (∑ b : Bone, ((dArea b : ℝ) : ℂ) * defect b = 0)
      ↔ (∑ b : Bone, dArea b * (defect b).re = 0)
        ∧ (∑ b : Bone, dArea b * (defect b).im = 0) := by
  rw [complexThatch_split]
  exact stationaryComplexAction_split _ _

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.ComplexReggeAction
