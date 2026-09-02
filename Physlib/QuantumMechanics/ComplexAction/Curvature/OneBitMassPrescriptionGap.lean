/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric
public import Mathlib.Analysis.Real.Pi.Bounds

meta import Zil

/-!
# One theorem, one constructed matching, and the exact factors between them

An audit trail: this module was written in four passes and the first three overclaimed.  The
corrected reading is kept together with the exact algebra, because how it went wrong is a reusable
lesson (`analysis/empirical-discrimination-plan.md` C7).

**What the repository provides.**  One prescription:
`SchwarzschildInteriorFoliationMetric.erEpr_wormholeMass` inverts the one-bit horizon-entropy
condition `S_BH = k_B ln 2` into `M_ER = √(ħc ln2/(4πG)) ≈ 5.11 × 10⁻⁹ kg`.

**What this module constructs.**  A one-parameter *matching family*: set the one-bit entropic
proper distance `λ_C log 2 = ħ ln2/(Mc)` (`ComptonClock.EntropicProperDistance`) equal to `α·r_s`
with `r_s = 2GM/c²`.  Each `α > 0` fixes a mass; `α = 1` gives
`entropicOneBitMass = √(ħc ln2/(2G)) ≈ 1.28 × 10⁻⁸ kg`.  Two silent choices enter, and neither is
the framework's:

* the coefficient `α` — earlier revisions called `α = 1` "the natural horizon matching", then
  `α = 2π` "the geometrically natural" one, *after* computing that `2π` closes the gap;
* the mass in `λ_C` is the **hole's own mass**: the black hole is treated as the quantum particle
  whose vacuum correlations decay.  `EntropicRadarDistanceBridge` explicitly declines to fix which
  mass sets `λ_C`; this module fixed it silently.

**Exactness is automatic and carries no evidential weight.**  Every condition here has the form
`M² = ħc·k/G`, so any two differ by the exact factor `√(k₂/k₁)` *by construction*.  `√(2π)` is
`√((1/2)/(1/4π))` — the horizon **area** coefficient `4π` against the radius coefficient `2` — and
§D's `2√(ln 2)` is the entropy↔cell-count conversion fixed by the proven `S = N/4`.  Earlier
revisions presented the exactness as remarkable and the numerical match to `√(2π)` as a finding;
both were guaranteed before any computation.

**Consequently there is no internal inconsistency here, and no consistency check either.**  An
earlier revision claimed "two of CAT/EPT's own cross-sector routes disagree".  Wrong: the second
route was this module's constructed matching, so the disagreement is between a repository theorem
and a free parameter introduced here.  The framework's content is untouched in both directions.

**The `α = 2π` theorem (§C), read honestly.**  Within the family, `α = 2π` is the unique matching
under which the constructed mass coincides with `M_ER` — proved, and nothing independent selects
it.  It *can* be read as the great-circle circumference of the horizon 2-sphere; deflationarily it
is `4π/2`, area coefficient over radius coefficient.  The deflationary reading is the default,
because it is derivable from how the two conditions were built; the geometric reading was adopted
post hoc and an earlier revision presented it as "the resolution".

**A signature caution** (unchanged).  `entropicProperDistance` comes from *spacelike* correlation
decay (Reeh–Schlieder, Lorentzian) while the standard derivation of `S_BH` is Euclidean, `2π` the
angular period of the smooth cigar; the comparison here does not verify the continuation.  For the
record the Euclidean period in length units is `cβ = 4π r_s`, which is not the factor found.

Scope.  `M_ER` is transcribed; everything else is this module's construction, and §D rests on the
proven `S = N/4`.  What survives as content: the algebra, the unit conversion, and the recorded
trap — single-scale prescriptions always differ by exact factors, and choosing the coefficient that
closes such a gap is a fit, not a resolution.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Curvature.OneBitMassPrescriptionGap

/-! ### §A — the two prescriptions -/

/-- The ER=EPR one-bit mass, `M = √(ħc ln2/(4πG))`: the positive mass whose Bekenstein–Hawking
entropy is exactly one bit (`erEpr_wormholeMass`). -/
def erEprOneBitMass (G c ħ : ℝ) : ℝ := Real.sqrt (ħ * c * Real.log 2 / (4 * Real.pi * G))

/-- The `α = 1` member of the matching family: the mass at which the one-bit entropic proper
distance `λ_C log 2 = ħ ln2/(Mc)` equals the Schwarzschild radius, with `λ_C` built from the
**hole's own mass**.  Both the coefficient and that mass identification are constructions of this
module, not of the framework; an earlier revision called this "the natural horizon matching", a
naturalness claim withdrawn on re-evaluation. -/
def entropicOneBitMass (G c ħ : ℝ) : ℝ := Real.sqrt (ħ * c * Real.log 2 / (2 * G))

/-! ### §B — the gap, exactly -/

/-- **The `α = 1` constructed mass differs from the ER=EPR mass by exactly `√(2π)` — automatically.**
Both conditions have the form `M² = ħc·k/G`, so the ratio is `√(k₂/k₁) = √(4π/2)` by construction:
the exactness is guaranteed, not discovered.  An earlier revision added "`2π` is the Unruh–Hawking
normalization, which is where a resolution should be looked for"; that association was unsupported
and is withdrawn — the derivable account of the factor is area coefficient over radius
coefficient. -/
theorem oneBitMass_ratio_eq_sqrt_two_pi {G c ħ : ℝ} (hG : 0 < G) (hc : 0 < c) (hħ : 0 < ħ) :
    entropicOneBitMass G c ħ = Real.sqrt (2 * Real.pi) * erEprOneBitMass G c ħ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hA : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hB : (0 : ℝ) ≤ ħ * c * Real.log 2 / (4 * Real.pi * G) := by positivity
  unfold entropicOneBitMass erEprOneBitMass
  rw [← Real.sqrt_mul hA]
  congr 1
  field_simp
  ring

/-- **The constructed mass is strictly the larger.**  Since `√(2π) > 1` the two are never equal at
physical parameters, so an argument must not silently switch between the `α = 1` matching and the
ER=EPR prescription — it would be off by `√(2π)`. -/
theorem erEprOneBitMass_lt_entropicOneBitMass {G c ħ : ℝ} (hG : 0 < G) (hc : 0 < c) (hħ : 0 < ħ) :
    erEprOneBitMass G c ħ < entropicOneBitMass G c ħ := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpos : 0 < erEprOneBitMass G c ħ := by
    unfold erEprOneBitMass
    exact Real.sqrt_pos.mpr (by positivity)
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  have hgt : 1 < Real.sqrt (2 * Real.pi) := by
    nlinarith [Real.pi_gt_three, hsq, hsqrtnn]
  rw [oneBitMass_ratio_eq_sqrt_two_pi hG hc hħ]
  nlinarith [hpos, hgt]


/-! ### §C — the gap-closing coefficient is exactly `2π` -/

/-- **Within the matching family, `α = 2π` is the unique gap-closing coefficient.**  The one-bit
entropic distance equals `2π·r_s` exactly when `M` is the ER=EPR one-bit mass.

Read honestly: this proves *which* coefficient closes the gap, not that anything selects it.
`2π·r_s` can be read as a great-circle circumference of the horizon 2-sphere; deflationarily the
`2π` is `4π/2`, the area coefficient over the radius coefficient, which is derivable from how the
two conditions were built.  An earlier revision of this section presented the circumference reading
as "the resolution" and "the geometrically natural pairing"; that was post hoc — the radius matching
had been called natural one commit earlier, and the circumference became "natural" only after the
mismatch was computed. -/
theorem entropicOneBit_matching_twoPi_imp_erEpr {M G c ħ : ℝ}
    (hM : 0 < M) (hG : 0 < G) (hc : 0 < c) (hħ : 0 < ħ)
    (hmatch : ħ * Real.log 2 / (M * c) = 2 * Real.pi * (2 * G * M / c ^ 2)) :
    M = erEprOneBitMass G c ħ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : M ^ 2 = ħ * c * Real.log 2 / (4 * Real.pi * G) := by
    field_simp at hmatch
    field_simp
    nlinarith [hmatch]
  unfold erEprOneBitMass
  rw [← hsq, Real.sqrt_sq hM.le]


/-! ### §D — the cell count is not the bit count: `S = N/4` fixes the conversion -/

/-- The **one-cell mass**: the mass whose horizon carries exactly one holographic cell,
`N = A c³/(Għ) = 1` with `A = 4π r_s²`; solving gives `M = √(ħc/(16πG))`.

The repository's `holographicBits` counts Planck **cells**.  By the proven `S_BH = N/4`
(`HolographicNewtonFromBlackHoleHorizon.bekensteinHawking_eq_holographicBits_div_four`, in nats)
each cell carries a quarter nat ≈ `0.36` bits — so `N = 1` is *not* one bit of entropy, and the
`Bits` in that name is loose. -/
def holographicOneCellMass (G c ħ : ℝ) : ℝ := Real.sqrt (ħ * c / (16 * Real.pi * G))

/-- **One bit of horizon entropy is `4 ln 2` cells, and the two masses convert accordingly.**
`S_BH = N/4` makes the ER=EPR condition `S_BH = k_B ln 2` read `N = 4 ln 2 ≈ 2.77` cells, so the
ER=EPR mass exceeds the one-cell mass by exactly `2√(ln 2) ≈ 1.665`.

This factor is a **unit conversion fixed by the proven `S = N/4`**, not a convention gap: once
"one bit" means one bit of *entropy*, the cell count is determined.  An earlier revision of this
section presented cell count and entropy as two of "three inequivalent readings of one bit"; that
was wrong — their inequivalence *is* the proven conversion, the same way a joule and a calorie are
not two readings of energy.  The genuine prescription freedom in this module remains the §B/§C
distance matching alone. -/
theorem erEprOneBitMass_eq_two_sqrt_log_two_mul_oneCell {G c ħ : ℝ}
    (hG : 0 < G) (hc : 0 < c) (hħ : 0 < ħ) :
    erEprOneBitMass G c ħ = 2 * Real.sqrt (Real.log 2) * holographicOneCellMass G c ħ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : (0 : ℝ) ≤ 4 * Real.log 2 := by positivity
  have hHnn : (0 : ℝ) ≤ ħ * c / (16 * Real.pi * G) := by positivity
  have hfac : (2 : ℝ) * Real.sqrt (Real.log 2) = Real.sqrt (4 * Real.log 2) := by
    rw [show (4 : ℝ) * Real.log 2 = 2 ^ 2 * Real.log 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  unfold erEprOneBitMass holographicOneCellMass
  rw [hfac, ← Real.sqrt_mul h4]
  congr 1
  field_simp
  ring


/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.OneBitMassPrescriptionGap.erEprOneBitMass_eq_two_sqrt_log_two_mul_oneCell where
  formalizes @ "claim:one-bit-of-horizon-entropy-is-four-log-two-holographic-cells-by-the-proven-s-equals-n-over-four-so-the-er-epr-and-one-cell-masses-differ-by-a-fixed-unit-conversion-not-a-convention-choice",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.HolographicNewtonFromBlackHoleHorizon.bekensteinHawking_eq_holographicBits_div_four",
  caveat @ "the-holographic-bits-name-counts-planck-cells-each-carrying-a-quarter-nat-so-it-is-not-a-bit-count-and-the-only-genuine-prescription-freedom-in-this-module-remains-the-entropic-distance-matching-of-sections-b-and-c"

zil attach Physlib.QuantumMechanics.ComplexAction.Curvature.OneBitMassPrescriptionGap.oneBitMass_ratio_eq_sqrt_two_pi where
  formalizes @ "claim:the-alpha-equals-one-matching-of-the-one-bit-entropic-distance-to-the-schwarzschild-radius-differs-from-the-er-epr-one-bit-mass-by-exactly-root-two-pi-an-automatic-coefficient-ratio-for-single-scale-prescriptions-carrying-no-evidential-weight",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.SchwarzschildInteriorFoliationMetric.erEpr_wormholeMass",
  caveat @ "the-comparison-is-between-a-repository-theorem-and-a-matching-family-constructed-in-this-module-with-a-free-coefficient-and-the-holes-own-mass-in-the-compton-wavelength-so-it-is-neither-an-internal-inconsistency-of-the-framework-nor-a-consistency-check-of-it",
  caveat @ "the-arithmetic-factor-two-pi-is-exact-but-its-interpretation-is-open-a-great-circle-circumference-reading-and-a-deflationary-area-over-radius-coefficient-reading-are-both-available-and-the-comparison-does-not-verify-that-the-continuation-between-the-lorentzian-spacelike-correlation-decay-and-the-euclidean-derivation-of-the-horizon-entropy-is-performed-consistently"

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Curvature.OneBitMassPrescriptionGap

end
