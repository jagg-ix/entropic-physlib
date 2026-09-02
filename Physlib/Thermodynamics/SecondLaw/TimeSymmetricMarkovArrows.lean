/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Special.SimultaneityConventionShear
public import Physlib.QuantumMechanics.ComplexAction.CartanDecompositionLorentzGroup
public import Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Opposing arrows of time: the time-symmetric Markov approximation

Formalizes the exact core of Guff–Shastry–Rocco, *Emergence of Opposing Arrows of Time
in Open Quantum Systems* (arXiv:2311.08486): the Markov approximation does *not* break
time-reversal symmetry — done symmetrically it produces master equations with a
`sgn(t)` dissipator (their Eqs. for the symmetric Lindblad and Pauli equations), which
thermalize toward **both** time directions; what breaks is time-*translation* symmetry,
at the temporal origin.  On the explicit two-level symmetric Pauli solution:

* `symmetricRelaxation` — the exact two-sided solution
  `ρ(t) = 1/2 + c·e^{−2W|t|}`, with `symmetricRelaxation_ode`: away from the origin it
  satisfies the sgn-master equation `ρ̇ = sgn(t)·W·(1 − 2ρ)` — the `sgn` arising
  exactly as the derivative of `|t|` (`hasDerivAt_abs`), the paper's mechanism (the
  odd `sin` memory kernel);
* `symmetricRelaxation_even` and `time_reversal_maps_solutions` — the paper's central
  claim at the ODE level: the equation is time-reversal symmetric (reflection about
  the origin maps solutions to solutions, and the explicit solution is even);
* `reflection_about_nonzero_fails` — **time-translation symmetry is what breaks**:
  reflection about any `a ≠ 0` fails on the explicit solution (their
  §"Breakdown of Time-Translation Symmetry") — the origin is a genuine temporal
  boundary, not a choice of the observer;
* `equilibration_both_directions` — the **opposing arrows**: the solution relaxes to
  equilibrium `1/2` toward *both* `t → +∞` and `t → −∞`; entropy increases away from
  the origin in each direction (per direction, the existing Snoke H-theorem
  `SecondLawQuantumBoltzmann.hTheorem` supplies the entropy-production sign);
* `time_reversal_conjugates_boost`, `time_reversal_conjugates_shear` — the kinematic
  weld to the conventionality arc: conjugating the Ghosal frames by the time-reversal
  matrix `T = diag(1, −1)` flips the boost velocity and the synchrony gauge,
  `T·L(β)·T = L(−β)` and `T·S(κ)·T = S(−κ)` — the arrow's direction is gauge exactly
  as the synchrony was, and the invariant is the distance `|t|` from the temporal
  boundary, mirroring `synchronyShear_fixes_space` and the relative-state invariance
  of `Foundations.RelativeStateConventionality`.

**Honest layering.**  The derivation chain from the microscopic von Neumann equation —
Born–Markov, secular approximation, the `sin → sgn·πδ` continuum limit — is the
paper's analytic layer, cited not re-proven; the two-level explicit solution carries
its exact ODE content.  The general symmetric Lindblad generator on `MState` carriers
and the weld to `Foundations.MinimalModalOnticDynamics.semigroup_property_fails` (the
two-sided semigroup composition) are natural follow-ups.

## References

* T. Guff, C. U. Shastry, A. Rocco, *Emergence of opposing arrows of time in open
  quantum systems*, arXiv:2311.08486, Sci. Rep. **15** (2025).
* Carrier reuse: `Relativity.Special.SimultaneityConventionShear` (`lorentzFrame`,
  `synchronyShear`), `Thermodynamics.SecondLawQuantumBoltzmann.hTheorem` (cited),
  Mathlib `hasDerivAt_abs` (the `sgn` mechanism).
-/

set_option autoImplicit false

open Physlib.Relativity.Special.SimultaneityConventionShear
open Physlib.QuantumMechanics.ComplexAction.CartanDecompositionLorentzGroup
open Physlib.QuantumMechanics.Foundations.RelativeStateConventionality
open Physlib.QuantumMechanics.SpinDensityFunctionalOperators

@[expose] public section

namespace Physlib.Thermodynamics.SecondLaw.TimeSymmetricMarkovArrows

/-! ## §A — the exact two-sided relaxation of the symmetric Pauli equation -/

/-- **The two-sided relaxation solution** `ρ(t) = 1/2 + c·e^{−2W|t|}` of the symmetric
two-level Pauli equation: equilibrium `1/2`, initial offset `c` at the temporal
origin. -/
noncomputable def symmetricRelaxation (W c : ℝ) : ℝ → ℝ :=
  fun t => 1 / 2 + c * Real.exp (-(2 * W) * |t|)

/-- **The sgn-master equation** (the paper's symmetric Pauli equation, two-level):
away from the origin, `ρ̇ = sgn(t)·W·(1 − 2ρ)` — the `sgn(t)` arises exactly as the
derivative of `|t|`, the ODE face of the odd memory kernel. -/
theorem symmetricRelaxation_ode (W c t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (symmetricRelaxation W c)
      ((SignType.sign t : ℝ) * (W * (1 - 2 * symmetricRelaxation W c t))) t := by
  have h := ((((hasDerivAt_abs ht).const_mul (-(2 * W))).exp).const_mul c).const_add
    (1 / 2 : ℝ)
  have hval : (SignType.sign t : ℝ) * (W * (1 - 2 * symmetricRelaxation W c t))
      = c * (Real.exp (-(2 * W) * |t|) * (-(2 * W) * (SignType.sign t : ℝ))) := by
    unfold symmetricRelaxation
    ring
  rw [hval]
  exact h

/-- **The solution is even**: the relaxation looks identical toward past and future —
the time-reversal symmetry of the dynamics, realized. -/
theorem symmetricRelaxation_even (W c t : ℝ) :
    symmetricRelaxation W c (-t) = symmetricRelaxation W c t := by
  unfold symmetricRelaxation
  rw [abs_neg]

/-- **Time reversal maps solutions to solutions** — the paper's central claim at the
ODE level: for *any* collision functional `F`, if `ρ` solves the sgn-master equation
`ρ̇ = sgn(t)·F(ρ)`, so does the reflected `t ↦ ρ(−t)` — the oddness of `sgn` exactly
compensates the reflection. -/
theorem time_reversal_maps_solutions (F : ℝ → ℝ) (ρ : ℝ → ℝ)
    (h : ∀ t ≠ (0 : ℝ), HasDerivAt ρ ((SignType.sign t : ℝ) * F (ρ t)) t)
    (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s => ρ (-s)) ((SignType.sign t : ℝ) * F (ρ (-t))) t := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
  have hcomp := (h (-t) (neg_ne_zero.mpr ht)).comp t hneg
  have hsign : ((SignType.sign (-t) : ℝ)) = -(SignType.sign t : ℝ) := by
    rw [Left.sign_neg]
    push_cast
    ring
  have hval : (SignType.sign t : ℝ) * F (ρ (-t))
      = (SignType.sign (-t) : ℝ) * F (ρ (-t)) * (-1) := by
    rw [hsign]
    ring
  rw [hval]
  exact hcomp

/-- **Time-translation symmetry is what breaks**: reflection about any `a ≠ 0` fails
on the explicit solution — the temporal origin (where the Markov approximation is
made) is a genuine boundary between the two arrows, not a relabeling. -/
theorem reflection_about_nonzero_fails (W c a : ℝ) (hW : 0 < W) (hc : c ≠ 0)
    (ha : a ≠ 0) :
    ∃ t, symmetricRelaxation W c (a + t) ≠ symmetricRelaxation W c (a - t) := by
  refine ⟨a, fun h => ?_⟩
  unfold symmetricRelaxation at h
  have h2 : Real.exp (-(2 * W) * |a + a|) = Real.exp (-(2 * W) * |a - a|) := by
    have hcan := add_left_cancel h
    exact mul_left_cancel₀ hc hcan
  rw [sub_self, abs_zero, mul_zero, Real.exp_zero] at h2
  have h3 : -(2 * W) * |a + a| = 0 := by
    have h2' : Real.exp (-(2 * W) * |a + a|) = Real.exp 0 := by
      rw [Real.exp_zero]
      exact h2
    exact Real.exp_injective h2'
  have h4 : |a + a| ≠ 0 := abs_ne_zero.mpr (by intro h0; exact ha (by linarith))
  exact h4 (by
    rcases mul_eq_zero.mp h3 with h5 | h5
    · linarith
    · exact h5)

/-- **The opposing arrows**: the solution relaxes to the equilibrium `1/2` toward
*both* time infinities — thermalization into the future *and* into the past of the
temporal origin. -/
theorem equilibration_both_directions (W c : ℝ) (hW : 0 < W) :
    Filter.Tendsto (symmetricRelaxation W c) Filter.atTop (nhds (1 / 2)) ∧
    Filter.Tendsto (symmetricRelaxation W c) Filter.atBot (nhds (1 / 2)) := by
  have hexp : Filter.Tendsto (fun x : ℝ => Real.exp (-(2 * W) * x)) Filter.atTop
      (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hlin : Filter.Tendsto (fun x : ℝ => 2 * W * x) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
    have hneg := Filter.tendsto_neg_atTop_atBot.comp hlin
    refine hneg.congr fun x => ?_
    simp [Function.comp]
  have key : ∀ (l : Filter ℝ), Filter.Tendsto (fun t : ℝ => |t|) l Filter.atTop →
      Filter.Tendsto (symmetricRelaxation W c) l (nhds (1 / 2)) := by
    intro l habs
    have h1 : Filter.Tendsto (fun t => c * Real.exp (-(2 * W) * |t|)) l (nhds 0) := by
      have hmul := (hexp.comp habs).const_mul c
      simpa using hmul
    have h2 := h1.const_add (1 / 2 : ℝ)
    rw [add_zero] at h2
    exact h2
  exact ⟨key _ (Filter.tendsto_abs_atTop_atTop),
    key _ (Filter.tendsto_abs_atBot_atTop)⟩

/-! ## §B — the kinematic weld: the arrow flip is a gauge flip -/

/-- The time-reversal matrix `T = diag(1, −1)` on `(x, t)`. -/
noncomputable def timeReversalMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- **Time reversal conjugates the boost to the opposite velocity**:
`T·L(β)·T = L(−β)` — flipping the arrow of time flips the rocket's velocity, exactly
as it flips the sign of the sgn-dissipator: the arrow's direction is frame gauge. -/
theorem time_reversal_conjugates_boost (β c γ : ℝ) :
    timeReversalMatrix * lorentzFrame β c γ * timeReversalMatrix
      = lorentzFrame (-β) c γ := by
  unfold timeReversalMatrix lorentzFrame
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      try ring

/-- **Time reversal conjugates the synchrony shear to the opposite gauge**:
`T·S(κ)·T = S(−κ)` — the resynchronization direction flips with the arrow, welding
the Guff–Shastry–Rocco temporal boundary to the Ghosal conventionality arc: in both,
the invariant content is the distance from the boundary (`|t|`, resp. the shear-orbit
invariants), and the direction is gauge. -/
theorem time_reversal_conjugates_shear (κ : ℝ) :
    timeReversalMatrix * synchronyShear κ * timeReversalMatrix
      = synchronyShear (-κ) := by
  unfold timeReversalMatrix synchronyShear
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      try ring

/-! ## §C — the two-sided semigroup: two flows glued at the temporal boundary -/

/-- **The offset flow** of the symmetric relaxation: the deviation from equilibrium
evolves by `c ↦ c·e^{−2W|t|}`. -/
noncomputable def offsetFlow (W t c : ℝ) : ℝ := c * Real.exp (-(2 * W) * |t|)

/-- **Future-branch semigroup law**: for `s, t ≥ 0` the offset flow composes,
`Φ_s ∘ Φ_t = Φ_{s+t}` — toward the future the sgn-dynamics is an honest semigroup. -/
theorem offsetFlow_semigroup_future (W s t c : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    offsetFlow W s (offsetFlow W t c) = offsetFlow W (s + t) c := by
  unfold offsetFlow
  rw [abs_of_nonneg hs, abs_of_nonneg ht, abs_of_nonneg (by linarith : (0:ℝ) ≤ s + t),
    mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Past-branch semigroup law**: for `s, t ≤ 0` the flow composes as well — toward
the past the sgn-dynamics is the *opposite* honest semigroup. -/
theorem offsetFlow_semigroup_past (W s t c : ℝ) (hs : s ≤ 0) (ht : t ≤ 0) :
    offsetFlow W s (offsetFlow W t c) = offsetFlow W (s + t) c := by
  unfold offsetFlow
  rw [abs_of_nonpos hs, abs_of_nonpos ht, abs_of_nonpos (by linarith : s + t ≤ 0),
    mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **The semigroup law fails across the origin**: running forward by `t` and then
backward by `t` does not return to the start — both legs damp, so the composite is a
double damping, not the identity.  The two-sided dynamics is two semigroups glued at
the temporal boundary, never a one-parameter group; this is the same obstruction as
`Foundations.MinimalModalOnticDynamics.semigroup_property_fails`. -/
theorem offsetFlow_fails_across_origin (W t c : ℝ) (hW : 0 < W) (ht : t ≠ 0)
    (hc : c ≠ 0) :
    offsetFlow W (-t) (offsetFlow W t c) ≠ offsetFlow W (t + -t) c := by
  unfold offsetFlow
  rw [add_neg_cancel, abs_zero, mul_zero, Real.exp_zero, mul_one, abs_neg,
    mul_assoc, ← Real.exp_add]
  intro h
  have h2 : Real.exp (-(2 * W) * |t| + -(2 * W) * |t|) = Real.exp 0 := by
    rw [Real.exp_zero]
    exact mul_left_cancel₀ hc (by rw [mul_one]; exact h)
  have h3 := Real.exp_injective h2
  have h4 : |t| ≠ 0 := abs_ne_zero.mpr ht
  have h5 : (0:ℝ) < |t| := lt_of_le_of_ne (abs_nonneg t) (Ne.symm h4)
  nlinarith [h3]

/-! ## §D — the CPT gauge: arrow, parity, and charge flips; chirality as the
Everett–Deutsch branch label -/

/-- The parity matrix `P = diag(−1, 1)` on `(x, t)`. -/
noncomputable def parityMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]

/-- **Parity also flips the boost velocity**: `P·L(β)·P = L(−β)` — like the arrow
flip, the parity flip is a velocity-reversing gauge. -/
theorem parity_conjugates_boost (β c γ : ℝ) :
    parityMatrix * lorentzFrame β c γ * parityMatrix = lorentzFrame (-β) c γ := by
  unfold parityMatrix lorentzFrame
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      try ring

/-- `P·T = −1`: the combined parity–time flip is the central element. -/
theorem parity_mul_timeReversal :
    parityMatrix * timeReversalMatrix = -1 := by
  unfold parityMatrix timeReversalMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **The PT-combined conjugation is the identity gauge**: conjugating *any* frame by
`P·T = −1` changes nothing — parity and time reversal each flip the velocity
(`parity_conjugates_boost`, `time_reversal_conjugates_boost`), but their combination
is invisible: individually gauge, jointly invariant.  (On these real kinematic
carriers charge conjugation acts trivially, so this is the kinematic face of CPT.) -/
theorem PT_conjugation_fixes (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (parityMatrix * timeReversalMatrix) * M * (parityMatrix * timeReversalMatrix)
      = M := by
  rw [parity_mul_timeReversal]
  simp

/-- **Charge conjugation fixes the `x` and `z` Weyl generators** (real entries). -/
theorem chargeConj_weylLeft1 :
    weylLeft1.map (starRingEnd ℂ) = weylLeft1 := by
  rw [weylLeft_closed_form.1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, pauliX, map_ofNat]

/-- **Charge conjugation flips the `y` Weyl generator** (imaginary entries). -/
theorem chargeConj_weylLeft2 :
    weylLeft2.map (starRingEnd ℂ) = -weylLeft2 := by
  rw [weylLeft_closed_form.2.1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, pauliY, map_ofNat, Complex.conj_I]

/-- **Charge conjugation fixes the `z` Weyl generator**. -/
theorem chargeConj_weylLeft3 :
    weylLeft3.map (starRingEnd ℂ) = weylLeft3 := by
  rw [weylLeft_closed_form.2.2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, pauliZ, map_ofNat]

/-- **Charge conjugation flips the chirality sign**: the conjugated (positronic) Weyl
generators close on `su(2)` with the *opposite* structure sign,
`[X̄ᵢ, X̄ⱼ] = −iε·X̄ₖ` — the fermionic/positronic flip inverts the chiral orientation
exactly as the time flip inverts the sgn-dissipator: `C` and `T` are the same kind of
gauge, acting on charge and on the arrow. -/
theorem chargeConj_flips_chirality :
    (weylLeft1.map (starRingEnd ℂ)) * (weylLeft2.map (starRingEnd ℂ))
        - (weylLeft2.map (starRingEnd ℂ)) * (weylLeft1.map (starRingEnd ℂ))
      = -(Complex.I • weylLeft3.map (starRingEnd ℂ)) ∧
    (weylLeft2.map (starRingEnd ℂ)) * (weylLeft3.map (starRingEnd ℂ))
        - (weylLeft3.map (starRingEnd ℂ)) * (weylLeft2.map (starRingEnd ℂ))
      = -(Complex.I • weylLeft1.map (starRingEnd ℂ)) ∧
    (weylLeft3.map (starRingEnd ℂ)) * (weylLeft1.map (starRingEnd ℂ))
        - (weylLeft1.map (starRingEnd ℂ)) * (weylLeft3.map (starRingEnd ℂ))
      = -(Complex.I • weylLeft2.map (starRingEnd ℂ)) := by
  obtain ⟨h1, h2, h3⟩ := weylLeft_su2
  rw [chargeConj_weylLeft1, chargeConj_weylLeft2, chargeConj_weylLeft3]
  refine ⟨?_, ?_, ?_⟩
  · calc weylLeft1 * -weylLeft2 - -weylLeft2 * weylLeft1
        = -(weylLeft1 * weylLeft2 - weylLeft2 * weylLeft1) := by noncomm_ring
      _ = -(Complex.I • weylLeft3) := by rw [h1]
  · calc -weylLeft2 * weylLeft3 - weylLeft3 * -weylLeft2
        = -(weylLeft2 * weylLeft3 - weylLeft3 * weylLeft2) := by noncomm_ring
      _ = -(Complex.I • weylLeft1) := by rw [h2]
  · calc weylLeft3 * weylLeft1 - weylLeft1 * weylLeft3
        = Complex.I • weylLeft2 := h3
      _ = -(Complex.I • -weylLeft2) := by rw [smul_neg, neg_neg]

/-- **The binary gauge carries no weight** — the Everett–Deutsch identification: the
choice of label on the two-element gauge — fermionic/positronic, future-branch/
past-branch of the two-sided semigroup, left/right chirality — is a branch relabeling,
and by Deutsch's symmetry step any relabeling-invariant normalized weight assigns each
label exactly `1/2`.  The physics lives in the CPT-invariant pair, never in which
member is called "particle", "forward", or "left". -/
theorem opposing_branch_weights (w : Bool → ℝ)
    (hsym : ∀ σ : Equiv.Perm Bool, ∀ b, w (σ b) = w b)
    (hsum : ∑ b, w b = 1) (b : Bool) : w b = 1 / 2 := by
  have h := branchWeight_symmetric_uniform w hsym hsum b
  simpa [Fintype.card_bool] using h

end Physlib.Thermodynamics.SecondLaw.TimeSymmetricMarkovArrows

end
