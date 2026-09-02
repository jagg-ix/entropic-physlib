/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.MoulinDoubleDualCotton

/-!
# Moulin §4.7 — energy-momentum conservation fixes `a = −1/(n−3)`

Implements §4.7 of F. Moulin, *Generalization of Einstein's gravitational field equations*
(arXiv:2405.03698): the covariant divergence of the 4-index Einstein tensor is proportional to the Cotton
tensor (Eq. 50),

  `∇^i G_{ijkl} = −(1 + a(n−3))/(n−2) C_{jkl}`,

so demanding total energy-momentum conservation `∇^i G_{ijkl} = 0` (equivalently `∇^i T_{ijkl} = 0`, Eqs. 49,
55–56) fixes the parameter at `a = −1/(n−3)` (Eq. 51).

Because physlib has no covariant-derivative operator, the divergence `∇^i G_{ijkl}` enters through its
Cotton-tensor form (Moulin's computed Eq. 50): `einsteinDivergence4 a n C` is the structural right-hand side.
The conservation logic — that the proportionality coefficient `−(1 + a(n−3))/(n−2)` vanishes exactly at
`a = −1/(n−3)` (`conservation_coefficient_*` of `GravitationalFieldEquations.MoulinDoubleDualCotton`) — is then exact.

* `einsteinDivergence4` — `∇^i G_{ijkl}` as `−(1 + a(n−3))/(n−2)` times the Cotton tensor.
* `einsteinDivergence4_conserving` — it vanishes at `a = −1/(n−3)` (energy conservation).
* `einsteinDivergence4_eq_zero_iff` — with a non-vanishing Cotton tensor, `∇^i G = 0 ⟺ a = −1/(n−3)`
  (Moulin Eq. 51).

## References

* F. Moulin (2024), arXiv:2405.03698, §4.7, Eqs. 49–51. Carrier: `Physlib` (`GravitationalFieldEquations.MoulinDoubleDualCotton`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*}

/-- **The covariant divergence of the 4-index Einstein tensor** `∇^i G_{ijkl} = −(1 + a(n−3))/(n−2) C_{jkl}`
(Moulin Eq. 50), expressed through the Cotton tensor `C` (the `∇`-derivation needs a connection; this is the
structural right-hand side). -/
noncomputable def einsteinDivergence4 (a n : ℝ) (cotton : ι → ι → ι → ℝ) : ι → ι → ι → ℝ :=
  fun j k l => (-(1 + a * (n - 3)) / (n - 2)) * cotton j k l

/-- **[Energy conservation] the 4-index Einstein-tensor divergence vanishes at `a = −1/(n−3)`.** -/
lemma einsteinDivergence4_conserving (n : ℝ) (cotton : ι → ι → ι → ℝ) (hn3 : n - 3 ≠ 0)
    (j k l : ι) :
    einsteinDivergence4 (-1 / (n - 3)) n cotton j k l = 0 := by
  rw [einsteinDivergence4, conservation_coefficient_zero n hn3]
  simp

/-- **[Moulin Eq. 51] energy conservation fixes `a = −1/(n−3)`.** With the Cotton tensor not identically
zero, total energy-momentum conservation `∇^i G_{ijkl} = 0` holds iff `a = −1/(n−3)`. -/
lemma einsteinDivergence4_eq_zero_iff (a n : ℝ) (cotton : ι → ι → ι → ℝ)
    (hn2 : n - 2 ≠ 0) (hn3 : n - 3 ≠ 0) (hc : ∃ j k l, cotton j k l ≠ 0) :
    (∀ j k l, einsteinDivergence4 a n cotton j k l = 0) ↔ a = -1 / (n - 3) := by
  constructor
  · intro hyp
    obtain ⟨j, k, l, hne⟩ := hc
    have h0 : (-(1 + a * (n - 3)) / (n - 2)) * cotton j k l = 0 := hyp j k l
    rcases mul_eq_zero.mp h0 with hcoeff | hcot
    · have h1 : 1 + a * (n - 3) = 0 := by
        rw [div_eq_zero_iff, neg_eq_zero] at hcoeff
        rcases hcoeff with h | h
        · simpa using h
        · exact absurd h hn2
      exact (conservation_coefficient_iff a n hn3).mp h1
    · exact absurd hcot hne
  · intro hyp j k l
    rw [hyp]
    exact einsteinDivergence4_conserving n cotton hn3 j k l

end Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

end
