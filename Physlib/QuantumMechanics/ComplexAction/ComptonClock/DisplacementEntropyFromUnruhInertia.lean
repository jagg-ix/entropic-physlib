/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Thermodynamics.VerlindeEntropicForce
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
meta import Zil

/-!
# Verlinde's displacement entropy: a conditional uniqueness theorem

**What is proved, precisely.**  Within the scalar Verlinde interface: for nonzero
acceleration and displacement, positive `ħ, k_B, c`, the exact Unruh temperature, the
entropic-force constitutive relation `F = T·ΔS/Δx`, and the inertial-response equality
`F = ma` uniquely determine the scalar entropy change
`ΔS = 2πk_B(mc/ħ)Δx` (`displacementEntropy_unique_from_unruh_inertia`,
`existsUnique_displacementEntropy`).  The acceleration cancels, so the determined value is
independent of *which* nonzero acceleration was used (`displacementEntropy_a_independent`
— acceleration-independence; no quantum state appears in the statement).  Conversely
(`newton_second_law_from_verlinde_unruh`) that entropy reproduces inertia.  Together:

  **Verlinde entropy law ⟺ `F = ma`, given the entropic-force and Unruh relations.**

**What is NOT proved.**  This is an identifiability/equivalence result, not a premise-free
microscopic derivation: inertia (or equivalently the ansatz) remains an explicit premise;
at `a = 0` both sides vanish for every `S` and uniqueness fails; the quantified object is
a scalar finite entropy change, not a gradient field.  The rewrite
`displacementEntropy_eq_two_pi_nats_per_comptonCell` expresses `ΔS` as `2π` nats per
*probe-mass* Compton wavelength crossed — identifying that cell with the screen's
*inference-mass* cell (`comptonBitDensity` uses `1/σ₀²`) is an additional physical
identification this module does not make.

The pre-existing entropic-action discharge (`RelationalClaimLedger`) is conditional on
the Compton-anchor calibration; this route is conditional on inertia instead.  Two
different premise sets, one identified quantity — the postulate is *characterized*, and
its equivalence class of premises is now explicit, but nothing here is unconditional.
-/

set_option autoImplicit false

open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia

/-! ## A. Nonzero-acceleration characterization -/

/-- **The ansatz is forced**: if the entropic force at the Unruh temperature of one
nonzero acceleration reproduces inertia `F = ma`, the displacement entropy is uniquely
`2πk_B(mc/ħ)Δx`.  The acceleration cancels: thermality and inertia fix both form and
normalization. -/
theorem displacementEntropy_unique_from_unruh_inertia
    (ħ kB m c a Δx S : ℝ)
    (hħ : 0 < ħ) (hkB : 0 < kB) (hc : 0 < c) (ha : a ≠ 0) (hΔx : Δx ≠ 0)
    (h : verlindeEntropicForce (unruhTemperature ħ kB c a) S Δx = m * a) :
    S = verlindeDisplacementEntropy ħ kB m c Δx := by
  unfold verlindeEntropicForce unruhTemperature at h
  unfold verlindeDisplacementEntropy
  rw [div_mul_eq_mul_div, div_div, div_eq_iff
    (mul_ne_zero (by positivity : (2 * Real.pi * kB * c : ℝ) ≠ 0) hΔx)] at h
  have hcancel : a * (ħ * S) = a * (2 * Real.pi * kB * m * c * Δx) := by
    linear_combination h
  have h3 := mul_left_cancel₀ ha hcancel
  rw [eq_div_iff hħ.ne']
  linear_combination h3

/-- **Exactly one entropy gradient is compatible with Unruh thermality and inertia.** -/
theorem existsUnique_displacementEntropy
    (ħ kB m c a Δx : ℝ)
    (hħ : 0 < ħ) (hkB : 0 < kB) (hc : 0 < c) (ha : a ≠ 0) (hΔx : Δx ≠ 0) :
    ∃! S : ℝ, verlindeEntropicForce (unruhTemperature ħ kB c a) S Δx = m * a := by
  refine ⟨verlindeDisplacementEntropy ħ kB m c Δx, ?_, fun S hS =>
    displacementEntropy_unique_from_unruh_inertia ħ kB m c a Δx S hħ hkB hc ha hΔx hS⟩
  unfold verlindeEntropicForce unruhTemperature verlindeDisplacementEntropy
  field_simp

/-- **The precise logical result is an equivalence.**  At nonzero acceleration and
displacement, the scalar entropy has Verlinde's value if and only if the entropic force
at the exact Unruh temperature reproduces the supplied inertial response `F = ma`. -/
lemma displacementEntropy_eq_iff_unruh_inertial_response
    (ħ kB m c a Δx S : ℝ)
    (hħ : 0 < ħ) (hkB : 0 < kB) (hc : 0 < c) (ha : a ≠ 0) (hΔx : Δx ≠ 0) :
    S = verlindeDisplacementEntropy ħ kB m c Δx ↔
      verlindeEntropicForce (unruhTemperature ħ kB c a) S Δx = m * a := by
  constructor
  · rintro rfl
    unfold verlindeEntropicForce unruhTemperature verlindeDisplacementEntropy
    field_simp
  · exact displacementEntropy_unique_from_unruh_inertia ħ kB m c a Δx S
      hħ hkB hc ha hΔx

/-- **The equivalence at the level of the response law — no acceleration side
condition.**  The entropic force at the exact Unruh temperature reproduces `F = m·a` at
*every* acceleration if and only if the scalar entropy is Verlinde's displacement
entropy.  The pointwise version needs `a ≠ 0`; quantifying over the whole law absorbs
the degenerate point, since at `a = 0` the equation holds for every `S`.  The premises
are the entropic-force interface and exact Unruh thermality; the equivalence
establishes neither side. -/
lemma verlindeEntropy_iff_inertial_response_law
    (ħ kB m c Δx S : ℝ)
    (hħ : 0 < ħ) (hkB : 0 < kB) (hc : 0 < c) (hΔx : Δx ≠ 0) :
    (∀ a : ℝ, verlindeEntropicForce (unruhTemperature ħ kB c a) S Δx = m * a) ↔
      S = verlindeDisplacementEntropy ħ kB m c Δx := by
  constructor
  · intro h
    exact displacementEntropy_unique_from_unruh_inertia ħ kB m c 1 Δx S
      hħ hkB hc one_ne_zero hΔx (h 1)
  · rintro rfl a
    rcases eq_or_ne a 0 with rfl | ha
    · simp [verlindeEntropicForce, unruhTemperature]
    · exact (displacementEntropy_eq_iff_unruh_inertial_response ħ kB m c a Δx _
        hħ hkB hc ha hΔx).mp rfl

/-- **Acceleration-independence**: the entropy determined at one nonzero acceleration
equals the entropy determined at any other.  (This is independence from `a` only — no
quantum state appears in the statement.) -/
theorem displacementEntropy_a_independent
    (ħ kB m c a₁ a₂ Δx S₁ S₂ : ℝ)
    (hħ : 0 < ħ) (hkB : 0 < kB) (hc : 0 < c)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hΔx : Δx ≠ 0)
    (h₁ : verlindeEntropicForce (unruhTemperature ħ kB c a₁) S₁ Δx = m * a₁)
    (h₂ : verlindeEntropicForce (unruhTemperature ħ kB c a₂) S₂ Δx = m * a₂) :
    S₁ = S₂ := by
  rw [displacementEntropy_unique_from_unruh_inertia ħ kB m c a₁ Δx S₁ hħ hkB hc ha₁ hΔx h₁,
    displacementEntropy_unique_from_unruh_inertia ħ kB m c a₂ Δx S₂ hħ hkB hc ha₂ hΔx h₂]

/-! ## B. Zero-acceleration boundary -/

/-- **At zero acceleration every scalar entropy is compatible.**  Both the Unruh
temperature and `m * a` vanish, so the response equation contains no information about
`S`.  This is the degenerate case excluded by the uniqueness theorem. -/
lemma every_displacementEntropy_compatible_at_zero_acceleration
    (ħ kB m c Δx S : ℝ) :
    verlindeEntropicForce (unruhTemperature ħ kB c 0) S Δx = m * 0 := by
  simp [verlindeEntropicForce, unruhTemperature]

/-- **Uniqueness fails at zero acceleration.**  Since both `S = 0` and `S = 1`
satisfy the response equation, there cannot be a unique compatible scalar entropy. -/
lemma not_existsUnique_displacementEntropy_at_zero_acceleration
    (ħ kB m c Δx : ℝ) :
    ¬ ∃! S : ℝ,
      verlindeEntropicForce (unruhTemperature ħ kB c 0) S Δx = m * 0 := by
  intro h
  have h01 : (0 : ℝ) = 1 := h.unique
    (every_displacementEntropy_compatible_at_zero_acceleration ħ kB m c Δx 0)
    (every_displacementEntropy_compatible_at_zero_acceleration ħ kB m c Δx 1)
  norm_num at h01

/-! ## C. Compton-wavelength rewrite -/

/-- **A rewrite, not a link**: the determined entropy is `2π` nats per *probe-mass*
Compton wavelength crossed.  Identifying this cell with the screen's inference-mass cell
(`comptonBitDensity` at `m = 1/σ₀²`) is an additional identification not made here. -/
theorem displacementEntropy_eq_two_pi_nats_per_comptonCell
    (ħ kB m c Δx : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    verlindeDisplacementEntropy ħ kB m c Δx
      = 2 * Real.pi * kB * (Δx / comptonWavelength m c ħ) := by
  unfold verlindeDisplacementEntropy comptonWavelength
  field_simp

/-- Crossing one probe-mass reduced Compton wavelength gives the dimensionless entropy
change `ΔS / k_B = 2π`, equivalently `ΔS = 2π k_B`. -/
lemma displacementEntropy_at_one_comptonWavelength
    (ħ kB m c : ℝ) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) :
    verlindeDisplacementEntropy ħ kB m c (comptonWavelength m c ħ)
      = 2 * Real.pi * kB := by
  rw [displacementEntropy_eq_two_pi_nats_per_comptonCell ħ kB m c
    (comptonWavelength m c ħ) hm hc hħ]
  have hlam : comptonWavelength m c ħ ≠ 0 := by
    unfold comptonWavelength
    exact div_ne_zero hħ (mul_ne_zero hm hc)
  rw [div_self hlam, mul_one]

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia

zil attach displacementEntropy_unique_from_unruh_inertia where
  caveat @ "claim:the-thermality-premise-is-empirically-untested-for-real-masses-at-\
achievable-accelerations-the-massive-field-unruh-response-is-boltzmann-suppressed-below-\
the-compton-unruh-weld-with-the-engineered-low-mass-analog-regime-the-falsifiable-route",
  supported_by @ "paper:toussaint-2025-detecting-the-unruh-effect-via-an-engineered-low-mass-field-in-a-superconducting-qubit-arxiv-2512-17959",
  discloses @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  formalizes @ "claim:verlindes-displacement-entropy-is-the-unique-entropy-gradient-for-\
which-the-entropic-force-at-the-unruh-temperature-reproduces-inertia-the-acceleration-\
cancels-so-thermality-and-newtons-second-law-force-both-form-and-normalization",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  caveat @ "claim:this-is-a-conditional-identifiability-theorem-not-a-premise-free-\
derivation-the-ansatz-and-newtons-second-law-are-equivalent-given-the-entropic-force-and-\
unruh-relations-with-nonzero-acceleration-and-inertia-remains-an-explicit-premise"

zil attach existsUnique_displacementEntropy where
  discloses @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  formalizes @ "claim:exactly-one-scalar-finite-entropy-change-is-compatible-with-the-\
entropic-force-equation-exact-unruh-temperature-and-supplied-newtonian-inertial-response-\
at-nonzero-acceleration-and-displacement",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_unique_from_unruh_inertia"

zil attach displacementEntropy_eq_iff_unruh_inertial_response where
  discloses @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  formalizes @ "claim:the-verlinde-displacement-entropy-formula-and-newtonian-inertial-\
response-are-equivalent-given-the-entropic-force-equation-exact-unruh-temperature-and-\
nonzero-acceleration-and-displacement-neither-side-is-established-by-the-equivalence-alone",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_unique_from_unruh_inertia",
  supported_by @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh"

zil attach verlindeEntropy_iff_inertial_response_law where
  discloses @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  formalizes @ "claim:quantified-over-all-accelerations-the-entropic-force-at-the-exact-\
unruh-temperature-reproduces-newtonian-inertia-if-and-only-if-the-scalar-entropy-is-\
verlindes-displacement-entropy-the-nonzero-acceleration-side-condition-is-absorbed-by-\
the-quantifier-and-neither-side-is-established-by-the-equivalence",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_unique_from_unruh_inertia",
  supported_by @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh"

zil attach not_existsUnique_displacementEntropy_at_zero_acceleration where
  formalizes @ "claim:at-zero-acceleration-the-unruh-temperature-and-inertial-response-\
both-vanish-for-every-scalar-entropy-so-the-compatible-entropy-is-not-unique",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.every_displacementEntropy_compatible_at_zero_acceleration"

zil attach displacementEntropy_eq_two_pi_nats_per_comptonCell where
  discloses @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  formalizes @ "claim:the-determined-displacement-entropy-is-two-pi-nats-per-probe-mass-\
compton-wavelength-crossed-identifying-this-cell-with-the-screens-inference-mass-cell-is-\
a-separate-physical-identification",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_unique_from_unruh_inertia"

zil attach displacementEntropy_at_one_comptonWavelength where
  discloses @ "lean:Physlib.Thermodynamics.newton_second_law_from_verlinde_unruh",
  formalizes @ "claim:crossing-one-probe-mass-reduced-compton-wavelength-gives-entropy-\
two-pi-kb-or-two-pi-nats-after-division-by-kb-with-no-screen-cell-identification",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia.displacementEntropy_eq_two_pi_nats_per_comptonCell"

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.DisplacementEntropyFromUnruhInertia
