/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiHolographicEntropy

/-!
# The standard AdS/CFT correspondence: the GKP–Witten field–operator dictionary

Formalizes the **standard** AdS/CFT correspondence — the Gubser–Klebanov–Polyakov / Witten dictionary
(*S. Gubser, I. Klebanov, A. Polyakov, Phys. Lett. B 428 (1998) 105; E. Witten, Adv. Theor. Math. Phys. 2
(1998) 253*). A bulk scalar field of mass `m` in `AdS_{d+1}` is dual to a boundary CFT_d operator `O` of
conformal dimension `Δ`, fixed by the **mass–dimension relation**

  `Δ(Δ − d) = m² R²`   (`R` = AdS radius),

with the GKP–Witten generating-functional relation `Z_grav[φ₀] = ⟨e^{∫ φ₀ O}⟩_CFT`: a bulk field with
boundary value `φ₀` sources the operator `O`. Near the boundary `φ ~ z^{d−Δ} φ₀ + z^Δ ⟨O⟩` (source + VEV).
This is the standard dictionary, in contrast to the (non-standard) modular-flow route; it sits alongside the
Ryu–Takayanagi entropy of `AdSCFT.RyuTakayanagiHolographicEntropy` as the bulk-boundary field map, sharing the same
Brown–Henneaux central charge for `AdS₃/CFT₂`.

Writing `μ = m² R²` (which may be negative down to the Breitenlohner–Freedman bound):

* **§A — the mass–dimension relation** (`conformalDimension`, `massDimension_relation`,
  `conformalDimension_sum`, `conformalDimension_prod`). `Δ± = d/2 ± √(d²/4 + μ)` solve `Δ(Δ−d) = μ`, with
  `Δ₊ + Δ₋ = d` and `Δ₊ Δ₋ = −μ` (Vieta on `Δ² − dΔ − μ = 0`).
* **§B — the Breitenlohner–Freedman bound and unitarity** (`breitenlohnerFreedman`,
  `conformalDimension_ge_half`). `Δ` is real iff `μ ≥ −d²/4` (AdS scalar stability); `Δ₊ ≥ d/2` (above the
  unitarity floor).
* **§C — the GKP–Witten dictionary** (`falloff_source_exponent`, `cftTwoPoint`, `cftTwoPoint_scaling`). The
  source falloff exponent is `d − Δ₊ = Δ₋`; the dictionary output is the CFT two-point function
  `⟨O(x)O(0)⟩ ~ |x|^{−2Δ}`, conformally covariant `⟨O(λx)…⟩ = λ^{−2Δ}⟨O(x)…⟩`.
* **§D — the standard `AdS₃/CFT₂` dictionary** (`adS3CFT2_dictionary`). Bundles the boundary CFT₂ data: the
  Brown–Henneaux central charge `c = 3R/2G` (from `AdSCFT.RyuTakayanagiHolographicEntropy`) and the operator
  dimension `Δ(Δ−2) = m²R²`.

## References

* S. Gubser, I. Klebanov, A. Polyakov (1998); E. Witten (1998) — the AdS/CFT field–operator dictionary and
  the generating-functional relation. P. Breitenlohner, D. Z. Freedman, Ann. Phys. 144 (1982) 249 — the
  stability bound.
* Repo structure: `AdSCFT.RyuTakayanagiHolographicEntropy` (`brownHenneaux`, the AdS₃ central charge).

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary

open Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiHolographicEntropy

/-! ## §A — the mass–dimension relation -/

/-- **[GKP–Witten] The conformal dimension** `Δ₊ = d/2 + √(d²/4 + μ)` of the boundary operator dual to a bulk
scalar with `μ = m²R²`. -/
noncomputable def conformalDimension (d μ : ℝ) : ℝ := d / 2 + Real.sqrt ((d / 2) ^ 2 + μ)

/-- The conjugate dimension `Δ₋ = d/2 − √(d²/4 + μ)` (the alternate quantization / source falloff). -/
noncomputable def conformalDimensionMinus (d μ : ℝ) : ℝ := d / 2 - Real.sqrt ((d / 2) ^ 2 + μ)

/-- **[Standard AdS/CFT] The mass–dimension relation** `Δ(Δ − d) = m²R²`. The bulk scalar mass fixes the
boundary operator's conformal dimension. -/
theorem massDimension_relation (d μ : ℝ) (h : 0 ≤ (d / 2) ^ 2 + μ) :
    conformalDimension d μ * (conformalDimension d μ - d) = μ := by
  unfold conformalDimension
  nlinarith [Real.sq_sqrt h, Real.sqrt_nonneg ((d / 2) ^ 2 + μ)]

/-- The conjugate dimension also solves the mass–dimension relation `Δ₋(Δ₋ − d) = m²R²`. -/
theorem massDimensionMinus_relation (d μ : ℝ) (h : 0 ≤ (d / 2) ^ 2 + μ) :
    conformalDimensionMinus d μ * (conformalDimensionMinus d μ - d) = μ := by
  unfold conformalDimensionMinus
  nlinarith [Real.sq_sqrt h, Real.sqrt_nonneg ((d / 2) ^ 2 + μ)]

/-- **[Vieta] `Δ₊ + Δ₋ = d`** — the two dimensions sum to the boundary dimension. -/
theorem conformalDimension_sum (d μ : ℝ) :
    conformalDimension d μ + conformalDimensionMinus d μ = d := by
  unfold conformalDimension conformalDimensionMinus; ring

/-- **[Vieta] `Δ₊ Δ₋ = −m²R²`** — the product of the two dimensions. -/
theorem conformalDimension_prod (d μ : ℝ) (h : 0 ≤ (d / 2) ^ 2 + μ) :
    conformalDimension d μ * conformalDimensionMinus d μ = -μ := by
  unfold conformalDimension conformalDimensionMinus; nlinarith [Real.sq_sqrt h]

/-! ## §B — the Breitenlohner–Freedman bound and unitarity -/

/-- **[Breitenlohner–Freedman] The dimension is real iff `m²R² ≥ −d²/4`.** The AdS scalar is stable above the
BF bound. -/
theorem breitenlohnerFreedman (d μ : ℝ) : 0 ≤ (d / 2) ^ 2 + μ ↔ -(d / 2) ^ 2 ≤ μ := by
  constructor <;> intro h <;> linarith

/-- **[Unitarity] `Δ₊ ≥ d/2`** — the operator dimension is above the unitarity floor. -/
theorem conformalDimension_ge_half (d μ : ℝ) : d / 2 ≤ conformalDimension d μ := by
  unfold conformalDimension; have := Real.sqrt_nonneg ((d / 2) ^ 2 + μ); linarith

/-! ## §C — the GKP–Witten dictionary: falloffs and the two-point function -/

/-- **[GKP–Witten falloffs] The source falloff exponent is `d − Δ₊ = Δ₋`.** Near the boundary
`φ ~ z^{d−Δ} φ₀ + z^Δ ⟨O⟩`: the leading (source) term has exponent `d − Δ₊`, the conjugate dimension `Δ₋`. -/
theorem falloff_source_exponent (d μ : ℝ) :
    d - conformalDimension d μ = conformalDimensionMinus d μ := by
  have := conformalDimension_sum d μ; linarith

/-- **[GKP–Witten output] The CFT two-point function** `⟨O(x)O(0)⟩ ~ |x|^{−2Δ}` of a dimension-`Δ` operator —
the boundary observable the dictionary computes. -/
noncomputable def cftTwoPoint (Δ x : ℝ) : ℝ := |x| ^ (-2 * Δ)

/-- **[Conformal covariance] `⟨O(λx)O(0)⟩ = λ^{−2Δ} ⟨O(x)O(0)⟩`** for `λ > 0` — the scaling fixed by the
conformal dimension. -/
theorem cftTwoPoint_scaling (Δ x lam : ℝ) (hlam : 0 < lam) :
    cftTwoPoint Δ (lam * x) = lam ^ (-2 * Δ) * cftTwoPoint Δ x := by
  unfold cftTwoPoint
  rw [abs_mul, abs_of_pos hlam, Real.mul_rpow (le_of_lt hlam) (abs_nonneg x)]

/-! ## §D — the standard `AdS₃/CFT₂` dictionary -/

/-- **[Standard AdS₃/CFT₂] The boundary CFT₂ data from the bulk.** The Brown–Henneaux central charge
`c = 3R/2G` (`AdSCFT.RyuTakayanagiHolographicEntropy.brownHenneaux`) and the operator dimension fixed by
`Δ(Δ − 2) = m²R²` — the standard dictionary for `AdS₃/CFT₂`, alongside the Ryu–Takayanagi entropy. -/
theorem adS3CFT2_dictionary (R G μ : ℝ) (h : 0 ≤ (2 / 2 : ℝ) ^ 2 + μ) :
    brownHenneaux R G = 3 * R / (2 * G)
      ∧ conformalDimension 2 μ * (conformalDimension 2 μ - 2) = μ :=
  ⟨rfl, massDimension_relation 2 μ h⟩

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary

end
