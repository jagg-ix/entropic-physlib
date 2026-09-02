/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.TimeLike
public import Physlib.Relativity.LorentzGroup.ToVector
public import Physlib.Relativity.LorentzGroup.Orthochronous.Basic
meta import Zil

/-!
# Boost-invariance of the future light cone and causal reconstruction of the metric

Two structural facts about how the causal structure relates to the Lorentzian metric,
completing the "spacetime reconstructed from causal data" programme (gu.md Axiom 5 /
Prop 3):

**Full boost-invariance of the interior future light cone.**  The set
`interiorFutureLightCone p` is preserved by every *orthochronous* Lorentz
transformation: `Λ • q ∈ interiorFutureLightCone (Λ • p) ↔ q ∈ interiorFutureLightCone p`.
The `causalCharacter` half is `causalCharacter_invariant`; the time-ordering half needs
that an orthochronous boost sends a future-directed timelike vector to a future-directed
one, which reduces (via `smul_timeComponent_eq_toVector_minkowskiProduct`) to the
**reverse Cauchy–Schwarz inequality** `0 < ⟪u, v⟫ₘ` for two future-directed timelike
vectors — proved here as `minkowskiProduct_pos_of_futureTimelike`.  The symmetric
spacelike relation `causallyUnrelated` is invariant under the *full* Lorentz group.

**Malament reconstruction, up to a conformal factor.**  Rescaling the Minkowski form by
any positive conformal factor `Ω²` leaves `causalCharacter` — hence the light cones and
the whole causal order — unchanged (`conformalFactor_causalCharacter_invariant`).  So the
causal structure determines the metric only up to a positive conformal factor: this is
the (easy, sufficiency) direction of Malament's theorem.  The deep converse — that
*every* causal automorphism is a conformal Poincaré transformation (Alexandrov–Zeeman) —
is not formalized here.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Lorentz.Vector

open realLorentzTensor InnerProductSpace LorentzGroup

variable {d : ℕ}

/-! ## Reverse Cauchy–Schwarz for future-directed timelike vectors -/

/-- **Reverse Cauchy–Schwarz.**  The Minkowski inner product of two future-directed
timelike vectors is strictly positive.  With `⟪u,v⟫ₘ = u⁰v⁰ − ⟪ū, v̄⟫`, Cauchy–Schwarz
bounds the spatial term `⟪ū, v̄⟫ ≤ ‖ū‖‖v̄‖`, and timelikeness gives `‖ū‖ < u⁰`,
`‖v̄‖ < v⁰`, so `⟪ū, v̄⟫ < u⁰v⁰`. -/
@[zil_level physical_theorem]
theorem minkowskiProduct_pos_of_futureTimelike {u v : Vector d}
    (hu : causalCharacter u = .timeLike) (hv : causalCharacter v = .timeLike)
    (hu0 : 0 < timeComponent u) (hv0 : 0 < timeComponent v) :
    0 < ⟪u, v⟫ₘ := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  have hCS : ⟪u.spatialPart, v.spatialPart⟫_ℝ ≤ ‖u.spatialPart‖ * ‖v.spatialPart‖ :=
    real_inner_le_norm _ _
  have hnu : ‖u.spatialPart‖ < timeComponent u := by
    have h1 : ‖u.spatialPart‖ ^ 2 < (timeComponent u) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]; exact timelike_spatial_lt_time_squared hu
    nlinarith [h1, hu0, norm_nonneg u.spatialPart]
  have hnv : ‖v.spatialPart‖ < timeComponent v := by
    have h1 : ‖v.spatialPart‖ ^ 2 < (timeComponent v) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]; exact timelike_spatial_lt_time_squared hv
    nlinarith [h1, hv0, norm_nonneg v.spatialPart]
  have hprod : ‖u.spatialPart‖ * ‖v.spatialPart‖ < timeComponent u * timeComponent v :=
    mul_lt_mul'' hnu hnv (norm_nonneg _) (norm_nonneg _)
  linarith [hCS, hprod]

/-! ## Full boost-invariance of the interior future light cone -/

/-- **The `toVector` of an orthochronous transformation is future-directed timelike.** -/
theorem toVector_futureTimelike_of_orthochronous {Λ : LorentzGroup d} (hΛ : IsOrthochronous Λ) :
    causalCharacter (toVector Λ) = .timeLike ∧ 0 < timeComponent (toVector Λ) := by
  refine ⟨?_, ?_⟩
  · rw [timeLike_iff_norm_sq_pos, toVector_minkowskiProduct_self]; exact one_pos
  · rw [toVector_timeComponent]; linarith [(isOrthochronous_iff_ge_one Λ).mp hΛ]

/-- **An orthochronous boost maps the interior future light cone into itself.**  The
`causalCharacter` is Lorentz-invariant, and the future time-ordering is preserved because
`(Λ • (q−p)).timeComponent = ⟪toVector Λ⁻¹, q−p⟫ₘ > 0` by reverse Cauchy–Schwarz
(`toVector Λ⁻¹` and `q−p` are both future-directed timelike). -/
@[zil_level bridge_theorem]
theorem interiorFutureLightCone_smul_of_orthochronous {Λ : LorentzGroup d}
    (hΛ : IsOrthochronous Λ) {p q : Vector d} (h : q ∈ interiorFutureLightCone p) :
    Λ • q ∈ interiorFutureLightCone (Λ • p) := by
  obtain ⟨hc, ht⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← smul_sub, causalCharacter_invariant]; exact hc
  · rw [← smul_sub]
    show 0 < (Λ • (q - p)).timeComponent
    rw [smul_timeComponent_eq_toVector_minkowskiProduct]
    obtain ⟨hcΛ, htΛ⟩ := toVector_futureTimelike_of_orthochronous (isOrthochronous_inv_iff.mpr hΛ)
    exact minkowskiProduct_pos_of_futureTimelike hcΛ hc htΛ ht

/-- **Full orthochronous boost-invariance of the interior future light cone.** -/
@[zil_level bridge_theorem]
theorem interiorFutureLightCone_smul_iff_of_orthochronous {Λ : LorentzGroup d}
    (hΛ : IsOrthochronous Λ) (p q : Vector d) :
    Λ • q ∈ interiorFutureLightCone (Λ • p) ↔ q ∈ interiorFutureLightCone p := by
  refine ⟨fun h => ?_, interiorFutureLightCone_smul_of_orthochronous hΛ⟩
  have h2 := interiorFutureLightCone_smul_of_orthochronous
    (isOrthochronous_inv_iff.mpr hΛ) h
  rwa [inv_smul_smul, inv_smul_smul] at h2

/-- **Spacelike separation is invariant under the full Lorentz group** (no orthochronicity
needed — it is symmetric in future/past). -/
@[zil_level physical_theorem]
theorem causallyUnrelated_smul (Λ : LorentzGroup d) (p q : Vector d) :
    causallyUnrelated (Λ • p) (Λ • q) ↔ causallyUnrelated p q := by
  unfold causallyUnrelated
  rw [← smul_sub, causalCharacter_invariant]

/-! ## Malament reconstruction: the metric up to a conformal factor -/

/-- The causal character read off a raw Minkowski-form value `s = ⟪v,v⟫ₘ`. -/
def causalCharacterOfForm (s : ℝ) : CausalCharacter :=
  if s = 0 then .lightLike else if 0 < s then .timeLike else .spaceLike

/-- `causalCharacter` is exactly the classification of `⟪v,v⟫ₘ`. -/
theorem causalCharacter_eq_ofForm (v : Vector d) :
    causalCharacter v = causalCharacterOfForm ⟪v, v⟫ₘ := rfl

/-- Scaling the form by a positive factor leaves its classification unchanged. -/
theorem causalCharacterOfForm_smul_pos {Ω : ℝ} (hΩ : 0 < Ω) (s : ℝ) :
    causalCharacterOfForm (Ω * s) = causalCharacterOfForm s := by
  unfold causalCharacterOfForm
  rcases lt_trichotomy s 0 with hs | hs | hs
  · rw [if_neg (by nlinarith), if_neg (by nlinarith), if_neg hs.ne, if_neg (by linarith)]
  · rw [hs, mul_zero]
  · rw [if_neg (by positivity), if_pos (by positivity), if_neg hs.ne', if_pos hs]

/-- **Malament reconstruction, up to a conformal factor.**  Rescaling the Minkowski form
by any positive conformal factor `Ω²` leaves the causal character — hence the light cones
and the entire causal order — unchanged.  The causal structure therefore determines the
metric only up to a positive conformal factor. -/
@[zil_level bridge_theorem]
theorem conformalFactor_causalCharacter_invariant {Ω : ℝ} (hΩ : 0 < Ω) (v : Vector d) :
    causalCharacterOfForm (Ω ^ 2 * ⟪v, v⟫ₘ) = causalCharacter v := by
  rw [causalCharacter_eq_ofForm]
  exact causalCharacterOfForm_smul_pos (pow_pos hΩ 2) _

end Lorentz.Vector

/- ZIL-BEGIN -/

open Zil
open Lorentz.Vector

zil attach interiorFutureLightCone_smul_iff_of_orthochronous where
  formalizes @ "claim:the-interior-future-light-cone-is-invariant-under-every-orthochronous-lorentz-transformation-so-the-future-causal-cone-is-a-frame-independent-structure",
  supported_by @ "lean:Lorentz.Vector.causalCharacter_invariant",
  supported_by @ "lean:Lorentz.Vector.minkowskiProduct_pos_of_futureTimelike"

zil attach minkowskiProduct_pos_of_futureTimelike where
  supported_by @ "lean:Vector.minkowskiProduct_eq_timeComponent_spatialPart",
  supported_by @ "lean:Vector.timelike_spatial_lt_time_squared",
  formalizes @ "claim:the-minkowski-inner-product-of-two-future-directed-timelike-vectors-is-strictly-positive-the-reverse-cauchy-schwarz-inequality"

zil attach conformalFactor_causalCharacter_invariant where
  supported_by @ "lean:Lorentz.Vector.causalCharacterOfForm_smul_pos",
  supported_by @ "lean:Lorentz.Vector.causalCharacter_eq_ofForm",
  formalizes @ "claim:rescaling-the-minkowski-form-by-a-positive-conformal-factor-leaves-the-causal-character-and-causal-order-unchanged-so-the-causal-structure-determines-the-metric-only-up-to-a-conformal-factor",
  caveat @ "claim:this-is-the-sufficiency-direction-of-malament-reconstruction-not-the-alexandrov-zeeman-converse-that-every-causal-automorphism-is-a-conformal-poincare-transformation"

zil attach causallyUnrelated_smul where
  supported_by @ "lean:Vector.causalCharacter_invariant",
  formalizes @ "claim:spacelike-separation-is-invariant-under-the-full-lorentz-group-with-no-orthochronicity-required"

zil_file_contract physlib.causalConeLorentzReconstruction where
  promises "The interior future light cone is invariant under every orthochronous Lorentz transformation - the future causal cone is a frame-independent structure. Its time-ordering half rests on the reverse Cauchy-Schwarz inequality that the Minkowski inner product of two future-directed timelike vectors is strictly positive, via the identity that the boosted time component equals the Minkowski product with the transform's own future-timelike vector. Spacelike separation is invariant under the full Lorentz group. And rescaling the Minkowski form by a positive conformal factor leaves the causal character unchanged, so the causal structure determines the metric only up to a positive conformal factor - the sufficiency direction of Malament reconstruction."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Lorentz.Vector.interiorFutureLightCone",
    "lean:Lorentz.Vector.causalCharacter",
    "lean:Lorentz.Vector.causalCharacter_invariant"
  ]
  forbids_substitutes [
    "claiming interior-future-cone invariance for non-orthochronous transformations that reverse time",
    "reading the conformal-factor invariance as the full Alexandrov-Zeeman converse of Malament's theorem"
  ]
  witnessed_by [
    minkowskiProduct_pos_of_futureTimelike,
    interiorFutureLightCone_smul_of_orthochronous,
    interiorFutureLightCone_smul_iff_of_orthochronous,
    causallyUnrelated_smul,
    conformalFactor_causalCharacter_invariant
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.causalConeLorentzReconstruction
