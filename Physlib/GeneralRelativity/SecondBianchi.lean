/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The second (differential) Bianchi identity and energy–momentum conservation

The second Bianchi identity of Riemannian geometry `R^a_{b[cd;e]} = 0` — the cyclic sum over the two curvature
indices and the derivative index of the covariant derivative of the Riemann tensor vanishes. Its **contracted**
form is `∇^μ G_{μν} = 0`: the Einstein tensor is automatically divergence-free. Combined with the Einstein field
equation `G = κ T`, this forces **energy–momentum conservation** `∇^μ T_{μν} = 0` — conservation is a geometric
identity, not an extra assumption.

References: the second Bianchi identity; the contracted Bianchi identity `∇G = 0`. No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.GeneralRelativity.SecondBianchi

/-- **The second (differential) Bianchi identity** `R^a_{bcd;e} + R^a_{bde;c} + R^a_{bec;d} = 0` — the cyclic sum
in the two curvature indices and the covariant-derivative index of `D = R^a_{bcd;e}`. -/
def IsSecondBianchi {κ : Type*} (D : κ → κ → κ → κ → κ → ℝ) : Prop :=
  ∀ a b c d e, D a b c d e + D a b d e c + D a b e c d = 0

/-- **The Einstein-tensor divergence** `∇^μ G_{μν} = ∇^μ R_{μν} − ½ ∇_ν R`. -/
noncomputable def einsteinDivergence {ι : Type*} (divRicci gradScalar : ι → ℝ) (ν : ι) : ℝ :=
  divRicci ν - (1 / 2) * gradScalar ν

/-- **The contracted second Bianchi identity** `∇^μ R_{μν} = ½ ∇_ν R`. -/
def ContractedSecondBianchi {ι : Type*} (divRicci gradScalar : ι → ℝ) : Prop :=
  ∀ ν, divRicci ν = (1 / 2) * gradScalar ν

/-- **The Einstein tensor is divergence-free iff the contracted Bianchi holds**
`(∀ν, ∇^μ G_{μν} = 0) ↔ ∇^μ R_{μν} = ½ ∇_ν R`. -/
theorem einstein_divergence_free_iff {ι : Type*} (divRicci gradScalar : ι → ℝ) :
    (∀ ν, einsteinDivergence divRicci gradScalar ν = 0)
      ↔ ContractedSecondBianchi divRicci gradScalar := by
  unfold einsteinDivergence ContractedSecondBianchi
  constructor <;> intro h ν <;> have := h ν <;> linarith

/-- **The second Bianchi identity forces energy–momentum conservation** `∇^μ G_{μν} = 0 ∧ G = κT ⟹ ∇^μ T_{μν} = 0`.
The divergence-free Einstein tensor (from the contracted second Bianchi) together with the field equation `G = κT`
makes energy–momentum conservation a geometric consequence, not a separate postulate. -/
theorem einstein_equation_forces_conservation {ι : Type*} (divG divT : ι → ℝ) (kappa : ℝ)
    (hk : kappa ≠ 0) (hEq : ∀ ν, divG ν = kappa * divT ν) (hBianchi : ∀ ν, divG ν = 0) :
    ∀ ν, divT ν = 0 := by
  intro ν
  have h := hEq ν
  rw [hBianchi ν] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hk

end Physlib.GeneralRelativity.SecondBianchi

end
