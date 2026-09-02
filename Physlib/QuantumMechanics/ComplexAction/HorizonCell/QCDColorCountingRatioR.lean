/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom
meta import Zil

/-!
# The ratio `R = N_c Σ e_q²` counts the colors, with the QCD correction `1 + α_s/π` (PDG 2026 §9.2.1)

The simplest fully-inclusive QCD observable (PDG 2026 §9.2.1, Eq. 9.7–9.9) is the ratio
`R(Q) = σ(e⁺e⁻ → hadrons)/σ(e⁺e⁻ → μ⁺μ⁻) = R_EW(1 + δ_QCD)`, with the parton-model value `R_EW = N_c Σ_q e_q²`
(number of colors times the sum of squared quark electric charges) and the leading QCD correction
`δ_QCD = c₁(α_s/π) + … , c₁ = 1`.

Historically `R` is *the* measurement of the number of colors: the parton-model plateau is `N_c` times the
charge sum, so measuring `R` reads off `N_c = 3`. This closes the QCD-Lagrangian arc back onto the electron cell —
the quark charges `e_u = 2/3`, `e_d = −1/3` are the same fractional charges the `SU(5)` charge-chirality modules
carry, and the leading QCD correction is the running coupling `α_s` of `QCDBetaFunctionAsymptoticFreedom`.

* the **light-quark charge sum** `Σ_{u,d,s} e_q² = (2/3)² + (−1/3)² + (−1/3)² = 2/3` (`lightQuark_chargeSqSum`);
* the **`u,d,s` plateau** `R = N_c · 2/3 = 2` (`ratioR_uds`) — the parton-model prediction, `= 2` for `N_c = 3`;
* **`R` counts the colors** `R / Σe_q² = N_c` (`ratioR_counts_colors`) — the ratio *is* the color multiplicity;
* the **QCD-corrected ratio** `R(1 + α_s/π)` recovers the parton value as `α_s → 0` (`ratioR_qcd_leading`,
  `ratioR_asymptotic_free_limit`) — the `c₁ = 1` leading correction, small in the UV (asymptotic freedom).

* **§A — the parton-model ratio `R = N_c Σe_q²`** (`ratioR`, `ratioR_counts_colors`).
* **§B — the light-quark plateau** (`lightQuark_chargeSqSum`, `ratioR_uds`).
* **§C — the leading QCD correction `1 + α_s/π`** (`ratioRQCD`, `ratioR_qcd_leading`).
* **§D — assembled** (`colorCounting_ratioR`).

**Honest layering.** `R_EW = N_c Σe_q²` and the charge sums are exact algebra/`norm_num`; `ratioR_counts_colors`
is the exact division identity. The leading QCD correction `c₁ = 1` is recorded exactly (`R_EW(1 + α_s/π)`); the
higher `cₙ(n_f)` and the full cross-section derivation are not formalized. ## References

* Particle Data Group, PDG 2026 Review, §9.2.1, Eqs. 9.7–9.9 (`R = N_c Σe_q²`, `δ_QCD = Σ cₙ(α_s/π)ⁿ`, `c₁ = 1`).
  Repo carrier: `HorizonCell.QCDBetaFunctionAsymptoticFreedom`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR


/-- **The parton-model ratio** `R_EW = N_c · Σ_q e_q²` (PDG Eq. 9.7–9.8) — the number of colors `N_c` times the
sum of squared quark electric charges. -/
def ratioR (N_c chargeSqSum : ℝ) : ℝ := N_c * chargeSqSum

/-- **[The ratio `R` counts the colors] `R / Σe_q² = N_c`.** Dividing the plateau by the charge sum returns the
number of colors: `R` is the historical measurement of `N_c = 3`. -/
lemma ratioR_counts_colors (N_c chargeSqSum : ℝ) (h : chargeSqSum ≠ 0) :
    ratioR N_c chargeSqSum / chargeSqSum = N_c := by
  unfold ratioR; field_simp


/-- **[The light-quark charge sum] `(2/3)² + (−1/3)² + (−1/3)² = 2/3`.** The sum of squared electric charges of
the `u`, `d`, `s` quarks (`e_u = 2/3`, `e_d = e_s = −1/3`). -/
lemma lightQuark_chargeSqSum : (2 / 3 : ℝ) ^ 2 + (-1 / 3 : ℝ) ^ 2 + (-1 / 3 : ℝ) ^ 2 = 2 / 3 := by
  norm_num

/-- **[The `u,d,s` plateau is `R = 2`] `N_c · 2/3 = 2` for `N_c = 3`.** With three colors and the light-quark
charge sum `2/3`, the parton-model ratio is `R = 3 · 2/3 = 2` — the measured plateau below charm threshold, the
evidence for three colors. -/
lemma ratioR_uds :
    ratioR 3 ((2 / 3 : ℝ) ^ 2 + (-1 / 3 : ℝ) ^ 2 + (-1 / 3 : ℝ) ^ 2) = 2 := by
  unfold ratioR; norm_num


/-- **The QCD-corrected ratio** `R = R_EW(1 + α_s/π)` (PDG Eq. 9.8–9.9 with `δ_QCD = c₁ α_s/π`, `c₁ = 1`) — the
parton-model plateau times the leading perturbative QCD correction. -/
noncomputable def ratioRQCD (N_c chargeSqSum αs : ℝ) : ℝ :=
  ratioR N_c chargeSqSum * (1 + αs / Real.pi)

/-- **[The leading QCD correction has `c₁ = 1`] `R_QCD = R_EW(1 + α_s/π)`.** The corrected ratio is the parton
value times `(1 + α_s/π)`: the leading coefficient of the perturbative series is exactly `c₁ = 1`. -/
lemma ratioR_qcd_leading (N_c chargeSqSum αs : ℝ) :
    ratioRQCD N_c chargeSqSum αs = ratioR N_c chargeSqSum * (1 + αs / Real.pi) := rfl

/-- **[The parton value is the asymptotically-free limit] `R_QCD → R_EW` as `α_s → 0`.** At `α_s = 0` (the
ultraviolet limit of asymptotic freedom, `QCDBetaFunctionAsymptoticFreedom`) the QCD correction switches off and
the ratio returns to the parton-model plateau `R_EW = N_c Σe_q²`. -/
lemma ratioR_asymptotic_free_limit (N_c chargeSqSum : ℝ) :
    ratioRQCD N_c chargeSqSum 0 = ratioR N_c chargeSqSum := by
  unfold ratioRQCD; simp


/-- **[The color-counting ratio `R`, assembled].**

* the parton-model ratio `R = N_c Σe_q²` counts the colors (`R/Σe_q² = N_c`);
* the light-quark plateau is `R = 2` for `N_c = 3`;
* the QCD correction is `R_EW(1 + α_s/π)` with `c₁ = 1`, returning the parton value as `α_s → 0`.

The inclusive ratio `R` reads off `N_c = 3` and carries the running coupling `α_s` as its leading correction —
the QCD-Lagrangian arc closed back onto the fractional quark charges and asymptotic freedom. -/
lemma colorCounting_ratioR (N_c chargeSqSum : ℝ) (h : chargeSqSum ≠ 0) :
    ratioR N_c chargeSqSum / chargeSqSum = N_c
      ∧ ratioR 3 ((2 / 3 : ℝ) ^ 2 + (-1 / 3 : ℝ) ^ 2 + (-1 / 3 : ℝ) ^ 2) = 2
      ∧ ratioRQCD N_c chargeSqSum 0 = ratioR N_c chargeSqSum :=
  ⟨ratioR_counts_colors N_c chargeSqSum h, ratioR_uds,
    ratioR_asymptotic_free_limit N_c chargeSqSum⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR.ratioR_counts_colors where
  formalizes @ "claim:the-e-plus-e-minus-to-hadrons-ratio-r-divided-by-the-sum-of-squared-quark-charges-equals-the-number-of-colors-so-measuring-r-reads-off-n-c",
  supported_by @ "paper:pdg-2026-review-section-9-2-1-ratio-r-color-counting"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR.ratioR_uds where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-light-quark-u-d-s-plateau-of-the-ratio-r-is-n-c-times-two-thirds-equal-to-two-for-three-colors-the-parton-model-prediction",
  requires @ "claim:the-e-plus-e-minus-to-hadrons-ratio-r-divided-by-the-sum-of-squared-quark-charges-equals-the-number-of-colors-so-measuring-r-reads-off-n-c"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR.ratioR_asymptotic_free_limit where
  formalizes @ "claim:the-qcd-corrected-ratio-r-times-one-plus-alpha-s-over-pi-recovers-the-parton-model-value-as-alpha-s-goes-to-zero-the-asymptotic-freedom-limit",
  supported_by @ "paper:pdg-2026-review-section-9-2-1-ratio-r-color-counting"

zil_file_contract physlib.qcdColorCountingRatioR where
  promises "The e+e- to hadrons ratio R = N_c sum_q e_q^2 counts the colors, with the leading QCD correction 1 + alpha_s/pi (PDG 2026 section 9.2.1, Eqs 9.7-9.9). The parton-model value is the number of colors times the sum of squared quark electric charges, so R is historically THE measurement of N_c: the plateau is N_c times the charge sum, so measuring R reads off N_c = 3. Proven as exact algebra/norm_num: the light-quark charge sum (2/3)^2 + (-1/3)^2 + (-1/3)^2 = 2/3, the u,d,s plateau R = N_c*2/3 = 2 for three colors, the exact division identity R/sum = N_c, and the QCD-corrected ratio R(1 + alpha_s/pi) recovering the parton value as alpha_s -> 0 (the c_1 = 1 leading correction, small in the UV by asymptotic freedom). The leading coefficient c_1 = 1 is recorded exactly; the higher c_n(n_f) and the full cross-section derivation are not formalized."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR.ratioR",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR.ratioRQCD"]
  forbids_substitutes ["a colorless N_c = 1 parton model, which would predict R = 2/3 for u,d,s instead of the measured 2",
    "an uncorrected parton ratio, omitting the leading 1 + alpha_s/pi QCD correction that vanishes only as alpha_s -> 0"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR.ratioR_counts_colors,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR.lightQuark_chargeSqSum,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR.ratioR_uds,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR.ratioR_asymptotic_free_limit,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDColorCountingRatioR.colorCounting_ratioR]

/- ZIL-END -/
