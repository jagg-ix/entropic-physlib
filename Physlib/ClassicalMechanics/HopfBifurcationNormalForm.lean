/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# The supercritical Hopf bifurcation normal form and the birth of a clock

The exact algebra of the supercritical Hopf normal form (E. Hopf 1942;
Marsden-McCracken): in polar form the radial equation is
`r' = r (μ - r²)` and the angular equation is uniform rotation. This module
proves the exact identities of the bifurcation - no genericity, center
manifold, or flow existence enters:

* **Critical points and the bifurcation.** The origin is critical for every
  parameter value (`radialField_origin`), and its linearization is the
  parameter itself (`hasDerivAt_radialField_origin`): the eigenvalue crosses
  zero exactly at `μ = 0` - the bifurcation. For `μ ≥ 0` the radius `√μ` is
  critical (`radialField_cycle`) with linearization `-2μ`
  (`hasDerivAt_radialField_cycle`): the born cycle is linearly attracting
  for `μ > 0`.
* **Flow toward the cycle.** Between the origin and the cycle the radius
  grows, beyond the cycle it shrinks (`radialField_pos`, `radialField_neg`),
  and the certificate `V(r) = (r² - μ)²` dissipates exactly:
  `V'(r) · f(r) = -4 r² (r² - μ)² ≤ 0`, vanishing precisely at the origin
  and on the cycle (`lyapunov_dissipation`, `lyapunov_dissipation_nonpos`,
  `lyapunov_dissipation_eq_zero_iff`) - the continuous counterpart of the
  strict-Lyapunov language of
  `Physlib.Thermodynamics.FiniteRecurrenceStrictLyapunov`.
* **The attractor is a clock.** On the bifurcated cycle `x² + y² = μ` the
  planar normal-form field reduces exactly to the uniform rotation field
  `(-ω y, ω x)` (`hopfField_on_cycle`), which preserves the radius
  (`rotationField_radial`); the radial component of the planar field is the
  radial equation (`hopfField_radial`). The attractor born at the
  bifurcation is a uniform circular clock - the continuous rotator whose
  stroboscopic quantization is the cyclic automaton of
  `Physlib.QuantumMechanics.CyclicAutomatonSpectrum`.

**Honest boundary.** Exact pointwise identities of the normal form only: no
center-manifold reduction from a general vector field, no ODE flow existence
or orbital-stability theorem (the stability readings are linearization signs
and dissipation inequalities), and the stroboscopic link to the cyclic
automaton is stated in prose, not as a conjugacy theorem.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.ClassicalMechanics.HopfBifurcationNormalForm

/-- **The radial field of the supercritical Hopf normal form**:
`f(r) = r (μ - r²)`. -/
def radialField (μ r : ℝ) : ℝ := r * (μ - r ^ 2)

@[simp] lemma radialField_origin (μ : ℝ) : radialField μ 0 = 0 := by
  simp [radialField]

/-- For `μ ≥ 0` the radius `√μ` is a critical point of the radial flow - the
bifurcated cycle. -/
@[zil_level physical_theorem]
theorem radialField_cycle {μ : ℝ} (hμ : 0 ≤ μ) :
    radialField μ (Real.sqrt μ) = 0 := by
  rw [radialField, Real.sq_sqrt hμ, sub_self, mul_zero]

/-- The radial field differentiates to `μ - 3 r²`. -/
theorem hasDerivAt_radialField (μ r : ℝ) :
    HasDerivAt (radialField μ) (μ - 3 * r ^ 2) r := by
  have h1 : HasDerivAt (fun x : ℝ => x * μ) μ r := by
    simpa using (hasDerivAt_id r).mul_const μ
  have h2 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * r ^ 2) r := by
    simpa using hasDerivAt_pow 3 r
  have h := h1.sub h2
  have hfun : radialField μ = fun x : ℝ => x * μ - x ^ 3 := by
    funext x
    unfold radialField
    ring
  rw [hfun]
  exact h

/-- **The bifurcation**: the linearization of the radial flow at the origin
is the parameter itself - stable for `μ < 0`, unstable for `μ > 0`, the
eigenvalue crossing zero exactly at `μ = 0`. -/
@[zil_level physical_theorem]
theorem hasDerivAt_radialField_origin (μ : ℝ) :
    HasDerivAt (radialField μ) μ 0 := by
  simpa using hasDerivAt_radialField μ 0

/-- **The born cycle is linearly attracting**: the linearization at `√μ` is
`-2μ`, strictly negative for `μ > 0`. -/
@[zil_level physical_theorem]
theorem hasDerivAt_radialField_cycle {μ : ℝ} (hμ : 0 ≤ μ) :
    HasDerivAt (radialField μ) (-(2 * μ)) (Real.sqrt μ) := by
  have h := hasDerivAt_radialField μ (Real.sqrt μ)
  rw [Real.sq_sqrt hμ] at h
  have harith : μ - 3 * μ = -(2 * μ) := by ring
  rwa [harith] at h

/-- Between the origin and the cycle the radius grows. -/
@[zil_level physical_theorem]
theorem radialField_pos {μ r : ℝ} (hr : 0 < r) (hlt : r ^ 2 < μ) :
    0 < radialField μ r :=
  mul_pos hr (by linarith)

/-- Beyond the cycle the radius shrinks. -/
@[zil_level physical_theorem]
theorem radialField_neg {μ r : ℝ} (hr : 0 < r) (hgt : μ < r ^ 2) :
    radialField μ r < 0 :=
  mul_neg_of_pos_of_neg hr (by linarith)

/-- **The cycle certificate**: `V(r) = (r² - μ)²`, vanishing exactly on the
cycle and measuring the squared distance to it in the radial variable. -/
def cycleLyapunov (μ r : ℝ) : ℝ := (r ^ 2 - μ) ^ 2

/-- The certificate differentiates to `4 r (r² - μ)`. -/
theorem hasDerivAt_cycleLyapunov (μ r : ℝ) :
    HasDerivAt (cycleLyapunov μ) (4 * r * (r ^ 2 - μ)) r := by
  have hinner : HasDerivAt (fun x : ℝ => x ^ 2 - μ) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).sub_const μ
  have h := hinner.mul hinner
  have hfun : cycleLyapunov μ = fun x : ℝ => (x ^ 2 - μ) * (x ^ 2 - μ) := by
    funext x
    unfold cycleLyapunov
    ring
  rw [hfun]
  convert h using 1 <;>
    first
      | rfl
      | ring

/-- **Exact dissipation along the radial flow**:
`V'(r) · f(r) = -4 r² (r² - μ)²`. -/
@[zil_level physical_theorem]
theorem lyapunov_dissipation (μ r : ℝ) :
    (4 * r * (r ^ 2 - μ)) * radialField μ r
      = -(4 * r ^ 2 * (r ^ 2 - μ) ^ 2) := by
  unfold radialField
  ring

/-- **The certificate never increases along the flow.** -/
@[zil_level physical_theorem]
theorem lyapunov_dissipation_nonpos (μ r : ℝ) :
    (4 * r * (r ^ 2 - μ)) * radialField μ r ≤ 0 := by
  rw [lyapunov_dissipation]
  have h : 0 ≤ 4 * r ^ 2 * (r ^ 2 - μ) ^ 2 := by positivity
  linarith

/-- **Dissipation vanishes exactly at the origin and on the cycle.** -/
@[zil_level physical_theorem]
theorem lyapunov_dissipation_eq_zero_iff (μ r : ℝ) :
    (4 * r * (r ^ 2 - μ)) * radialField μ r = 0 ↔ r = 0 ∨ r ^ 2 = μ := by
  rw [lyapunov_dissipation, neg_eq_zero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · norm_num at h3
      · exact Or.inl (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h4)
    · have := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2
      exact Or.inr (by linarith)
  · rintro (h | h)
    · subst h
      ring
    · rw [h]
      ring

/-- **The planar Hopf normal-form field** with rotation frequency `ω`:
`(μ x - ω y - (x² + y²) x, ω x + μ y - (x² + y²) y)`. -/
def hopfField (μ ω : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (μ * p.1 - ω * p.2 - (p.1 ^ 2 + p.2 ^ 2) * p.1,
   ω * p.1 + μ * p.2 - (p.1 ^ 2 + p.2 ^ 2) * p.2)

/-- **The uniform rotation field**: `(-ω y, ω x)` - a circular clock of
frequency `ω`. -/
def rotationField (ω : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (-(ω * p.2), ω * p.1)

/-- **On the bifurcated cycle the Hopf field is a uniform clock**: at every
point of the circle `x² + y² = μ` the planar normal-form field reduces
exactly to the rotation field - the attractor born at the bifurcation is a
uniform circular clock. -/
@[zil_level physical_theorem]
theorem hopfField_on_cycle {μ ω : ℝ} {p : ℝ × ℝ}
    (h : p.1 ^ 2 + p.2 ^ 2 = μ) :
    hopfField μ ω p = rotationField ω p := by
  unfold hopfField rotationField
  rw [h]
  exact Prod.ext_iff.mpr ⟨by ring, by ring⟩

/-- **The radial component of the planar field is the radial equation**:
`x f₁ + y f₂ = (x² + y²)(μ - (x² + y²))` - one half the derivative of the
squared radius along the flow. -/
@[zil_level physical_theorem]
theorem hopfField_radial (μ ω : ℝ) (p : ℝ × ℝ) :
    p.1 * (hopfField μ ω p).1 + p.2 * (hopfField μ ω p).2
      = (p.1 ^ 2 + p.2 ^ 2) * (μ - (p.1 ^ 2 + p.2 ^ 2)) := by
  unfold hopfField
  ring

/-- **The clock preserves the radius**: the rotation field is orthogonal to
the position at every point. -/
@[zil_level physical_theorem]
theorem rotationField_radial (ω : ℝ) (p : ℝ × ℝ) :
    p.1 * (rotationField ω p).1 + p.2 * (rotationField ω p).2 = 0 := by
  unfold rotationField
  ring

/-! ## Orbital stability and the critical center direction -/

/-- **At criticality the radial field is the pure cubic** - the reduced
dynamics on the center direction, where the linearization vanishes. -/
@[zil_level physical_theorem]
theorem radialField_critical (r : ℝ) : radialField 0 r = -(r ^ 3) := by
  unfold radialField
  ring

/-- **Nonlinear stability at criticality**: on the center direction the cubic
still dissipates the squared radius, `(2r) · f(0, r) = -2 r⁴ ≤ 0` - the
origin is nonlinearly stable exactly at the bifurcation, where its
linearization vanishes. This is the stability content of the normal form as
the center-manifold-reduced dynamics. -/
@[zil_level physical_theorem]
theorem critical_dissipation_nonpos (r : ℝ) :
    (2 * r) * radialField 0 r ≤ 0 := by
  have h : (2 * r) * radialField 0 r = -(2 * r ^ 4) := by
    unfold radialField
    ring
  rw [h]
  have hpos : (0 : ℝ) ≤ 2 * r ^ 4 := by positivity
  linarith

/-- **Lyapunov orbital stability of the cycle**: along any radial solution of
the normal form the cycle certificate never increases - the derivative of
`V ∘ r` is the exact dissipation, which is nonpositive everywhere. -/
@[zil_level physical_theorem]
theorem cycleLyapunov_antitone_along_solutions {μ : ℝ} {r : ℝ → ℝ}
    (hode : ∀ t, HasDerivAt r (radialField μ (r t)) t) :
    Antitone fun t => cycleLyapunov μ (r t) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s => cycleLyapunov μ (r s))
      ((4 * r t * ((r t) ^ 2 - μ)) * radialField μ (r t)) t := fun t =>
    (hasDerivAt_cycleLyapunov μ (r t)).comp t (hode t)
  refine antitone_of_deriv_nonpos (fun t => (hderiv t).differentiableAt) ?_
  intro t
  rw [(hderiv t).deriv]
  exact lyapunov_dissipation_nonpos μ (r t)

/-- **Sublevel invariance - orbital stability in the Lyapunov sense**: a
radial solution starting inside a certificate sublevel neighbourhood of the
cycle remains inside it at all later times. -/
@[zil_level physical_theorem]
theorem cycle_sublevel_invariant {μ c : ℝ} {r : ℝ → ℝ}
    (hode : ∀ t, HasDerivAt r (radialField μ (r t)) t)
    (h0 : cycleLyapunov μ (r 0) ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    cycleLyapunov μ (r t) ≤ c :=
  le_trans (cycleLyapunov_antitone_along_solutions hode ht) h0

end Physlib.ClassicalMechanics.HopfBifurcationNormalForm

end

open Physlib.ClassicalMechanics.HopfBifurcationNormalForm in
#physlib_axiom_clean_all [
  radialField_cycle,
  hasDerivAt_radialField,
  hasDerivAt_radialField_origin,
  hasDerivAt_radialField_cycle,
  radialField_pos,
  radialField_neg,
  hasDerivAt_cycleLyapunov,
  lyapunov_dissipation,
  lyapunov_dissipation_nonpos,
  lyapunov_dissipation_eq_zero_iff,
  hopfField_on_cycle,
  hopfField_radial,
  rotationField_radial,
  radialField_critical,
  critical_dissipation_nonpos,
  cycleLyapunov_antitone_along_solutions,
  cycle_sublevel_invariant ]

open Physlib.ClassicalMechanics.HopfBifurcationNormalForm in
#physlib_non_vacuous_all [
  radialField_cycle,
  hasDerivAt_radialField,
  hasDerivAt_radialField_origin,
  hasDerivAt_radialField_cycle,
  radialField_pos,
  radialField_neg,
  hasDerivAt_cycleLyapunov,
  lyapunov_dissipation_nonpos,
  lyapunov_dissipation_eq_zero_iff,
  hopfField_on_cycle,
  hopfField_radial,
  radialField_critical,
  critical_dissipation_nonpos,
  cycleLyapunov_antitone_along_solutions,
  cycle_sublevel_invariant ]

/- ZIL-BEGIN -/

zil attach Physlib.ClassicalMechanics.HopfBifurcationNormalForm.hasDerivAt_radialField_origin where
  formalizes @ "claim:the-origin-linearization-eigenvalue-crosses-zero-exactly-at-the-hopf-bifurcation",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hopf-1942-abzweigung-einer-periodischen-loesung-von-einer-stationaeren-loesung"

zil attach Physlib.ClassicalMechanics.HopfBifurcationNormalForm.hasDerivAt_radialField_cycle where
  formalizes @ "claim:the-bifurcated-cycle-has-attracting-linearization-minus-two-mu",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hopf-1942-abzweigung-einer-periodischen-loesung-von-einer-stationaeren-loesung",
  caveat @ "claim:linearization-sign-only-no-orbital-stability-theorem-is-proved"

zil attach Physlib.ClassicalMechanics.HopfBifurcationNormalForm.lyapunov_dissipation_eq_zero_iff where
  formalizes @ "claim:the-cycle-certificate-dissipates-exactly-vanishing-only-at-the-origin-and-on-the-cycle",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:marsden-mccracken-1976-the-hopf-bifurcation-and-its-applications"

zil attach Physlib.ClassicalMechanics.HopfBifurcationNormalForm.hopfField_on_cycle where
  formalizes @ "claim:on-the-bifurcated-cycle-the-normal-form-field-is-a-uniform-circular-clock",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hopf-1942-abzweigung-einer-periodischen-loesung-von-einer-stationaeren-loesung",
  caveat @ "claim:the-stroboscopic-link-to-the-cyclic-automaton-is-a-reading-not-a-conjugacy-theorem"

zil attach Physlib.ClassicalMechanics.HopfBifurcationNormalForm.critical_dissipation_nonpos where
  formalizes @ "claim:the-origin-is-nonlinearly-stable-exactly-at-the-bifurcation-where-the-linearization-vanishes",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:marsden-mccracken-1976-the-hopf-bifurcation-and-its-applications",
  caveat @ "claim:stability-of-the-normal-form-as-the-reduced-center-dynamics-no-center-manifold-existence-theorem-for-general-fields"

zil attach Physlib.ClassicalMechanics.HopfBifurcationNormalForm.cycleLyapunov_antitone_along_solutions where
  formalizes @ "claim:the-cycle-certificate-never-increases-along-radial-solutions-lyapunov-orbital-stability",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:hopf-1942-abzweigung-einer-periodischen-loesung-von-einer-stationaeren-loesung"

zil attach Physlib.ClassicalMechanics.HopfBifurcationNormalForm.cycle_sublevel_invariant where
  formalizes @ "claim:certificate-sublevel-neighbourhoods-of-the-cycle-are-forward-invariant",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:marsden-mccracken-1976-the-hopf-bifurcation-and-its-applications",
  caveat @ "claim:orbital-stability-in-the-radial-lyapunov-sublevel-sense-full-planar-asymptotic-phase-is-not-stated"

zil_file_contract physlib.hopfBifurcationNormalForm where
  promises "The exact algebra of the supercritical Hopf normal form: the origin is critical for every parameter with linearization equal to the parameter - the eigenvalue crossing at the bifurcation - the radius square root of mu is critical with attracting linearization minus two mu, the radial flow points toward the cycle on both sides, the cycle certificate dissipates exactly and vanishes only at the origin and on the cycle, and on the bifurcated cycle the planar field reduces exactly to the radius-preserving uniform rotation field - the attractor born at the bifurcation is a uniform circular clock."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:HasDerivAt", "lean:Real.sqrt", "lean:Real.sq_sqrt"]
  forbids_substitutes ["a center-manifold existence or reduction theorem for a general vector field",
    "ODE flow existence or full planar asymptotic orbital stability with phase, beyond radial certificate sublevel invariance",
    "a smooth circle-parametrized conjugacy: the roots-of-unity stroboscopic conjugacy lives in the cyclic-automaton module"]
  witnessed_by [
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.radialField_cycle,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.hasDerivAt_radialField_origin,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.hasDerivAt_radialField_cycle,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.radialField_pos,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.radialField_neg,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.lyapunov_dissipation,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.lyapunov_dissipation_nonpos,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.lyapunov_dissipation_eq_zero_iff,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.hopfField_on_cycle,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.hopfField_radial,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.rotationField_radial,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.radialField_critical,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.critical_dissipation_nonpos,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.cycleLyapunov_antitone_along_solutions,
    Physlib.ClassicalMechanics.HopfBifurcationNormalForm.cycle_sublevel_invariant ]

/- ZIL-END -/

#zil_formalization_lint physlib.hopfBifurcationNormalForm
