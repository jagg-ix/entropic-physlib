/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalConeLorentzReconstruction
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.LightLike
meta import Zil

/-!
# The Minkowski causal order is a preorder, and its intervals are the Alexandrov intervals

The Alexandrov-interval / order-isomorphism story of the Alexandrov–Zeeman correspondence
rests on the causal relation being a genuine order.  This module supplies the missing
foundation: `causallyFollows` on `Lorentz.Vector d` is reflexive and **transitive**, so it
is a `Preorder` (`causalPreorder`).

Transitivity is the substantive part.  It reduces to the future causal cone being closed
under addition (`isFutureCausal_add`), which in turn rests on the closed-cone reverse
Cauchy–Schwarz inequality `0 ≤ ⟪u, v⟫ₘ` for two future-directed causal vectors
(`minkowskiProduct_nonneg_of_futureCausal`) — the non-strict companion of
`minkowskiProduct_pos_of_futureTimelike`.

With the preorder in hand, the causal diamond is exactly the order interval:
`causalDiamond p q = Set.Icc p q` (`causalDiamond_eq_Icc`), identifying the spacetime
Alexandrov interval with the order-theoretic one — the identification Malament's theorem
turns on.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Lorentz.Vector

open realLorentzTensor InnerProductSpace

variable {d : ℕ}

/-! ## Closed-cone reverse Cauchy–Schwarz -/

/-- **Closed-cone reverse Cauchy–Schwarz.**  The Minkowski inner product of two
future-directed causal vectors (`0 ≤ ⟪·,·⟫ₘ`, `0 ≤` time component) is non-negative. -/
@[zil_level physical_theorem]
theorem minkowskiProduct_nonneg_of_futureCausal {u v : Vector d}
    (hu : 0 ≤ ⟪u, u⟫ₘ) (hv : 0 ≤ ⟪v, v⟫ₘ)
    (hu0 : 0 ≤ timeComponent u) (hv0 : 0 ≤ timeComponent v) :
    0 ≤ ⟪u, v⟫ₘ := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart]
  have hCS : ⟪u.spatialPart, v.spatialPart⟫_ℝ ≤ ‖u.spatialPart‖ * ‖v.spatialPart‖ :=
    real_inner_le_norm _ _
  have hnu : ‖u.spatialPart‖ ≤ timeComponent u := by
    have hself : ⟪u, u⟫ₘ = (timeComponent u) ^ 2 - ‖u.spatialPart‖ ^ 2 := by
      rw [minkowskiProduct_self_eq_timeComponent_spatialPart, Real.norm_eq_abs, sq_abs]
    nlinarith [hself ▸ hu, hu0, norm_nonneg u.spatialPart]
  have hnv : ‖v.spatialPart‖ ≤ timeComponent v := by
    have hself : ⟪v, v⟫ₘ = (timeComponent v) ^ 2 - ‖v.spatialPart‖ ^ 2 := by
      rw [minkowskiProduct_self_eq_timeComponent_spatialPart, Real.norm_eq_abs, sq_abs]
    nlinarith [hself ▸ hv, hv0, norm_nonneg v.spatialPart]
  have hprod : ‖u.spatialPart‖ * ‖v.spatialPart‖ ≤ timeComponent u * timeComponent v :=
    mul_le_mul hnu hnv (norm_nonneg _) hu0
  linarith [hCS, hprod]

/-! ## The future causal cone and its closure under addition -/

/-- **The future causal cone**: causal (`0 ≤ ⟪v,v⟫ₘ`) and future-directed
(`0 ≤ timeComponent v`). -/
def IsFutureCausal (v : Vector d) : Prop := 0 ≤ ⟪v, v⟫ₘ ∧ 0 ≤ timeComponent v

/-- `causallyFollows p q` holds exactly when `q − p` lies in the future causal cone. -/
@[zil_level structural]
theorem causallyFollows_iff_isFutureCausal (p q : Vector d) :
    causallyFollows p q ↔ IsFutureCausal (q - p) := by
  simp only [causallyFollows, interiorFutureLightCone, futureLightConeBoundary,
    Set.mem_setOf_eq, IsFutureCausal]
  constructor
  · rintro (⟨hc, ht⟩ | ⟨hc, ht⟩)
    · exact ⟨le_of_lt ((timeLike_iff_norm_sq_pos _).mp hc), le_of_lt ht⟩
    · exact ⟨le_of_eq ((lightLike_iff_norm_sq_zero _).mp hc).symm, ht⟩
  · rintro ⟨hnn, ht⟩
    rcases eq_or_lt_of_le hnn with h0 | hpos
    · exact Or.inr ⟨(lightLike_iff_norm_sq_zero _).mpr h0.symm, ht⟩
    · have hc' : causalCharacter (q - p) = .timeLike := (timeLike_iff_norm_sq_pos _).mpr hpos
      exact Or.inl ⟨hc', lt_of_le_of_ne ht (time_component_ne_zero_of_timelike hc').symm⟩

/-- **The future causal cone is closed under addition.** -/
@[zil_level physical_theorem]
theorem isFutureCausal_add {u v : Vector d} (hu : IsFutureCausal u) (hv : IsFutureCausal v) :
    IsFutureCausal (u + v) := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨?_, ?_⟩
  · have hexp : ⟪u + v, u + v⟫ₘ = ⟪u, u⟫ₘ + 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by
      simp only [map_add, ContinuousLinearMap.add_apply]
      rw [minkowskiProduct_symm v u]; ring
    rw [hexp]
    have huv : 0 ≤ ⟪u, v⟫ₘ := minkowskiProduct_nonneg_of_futureCausal hu1 hv1 hu2 hv2
    linarith
  · have h1 : (0 : ℝ) ≤ u (Sum.inl 0) := hu2
    have h2 : (0 : ℝ) ≤ v (Sum.inl 0) := hv2
    show 0 ≤ (u + v) (Sum.inl 0)
    rw [apply_add]; linarith

/-! ## The causal preorder and the Alexandrov interval -/

/-- **Reflexivity**: every event causally follows itself (it lies on its own light cone). -/
@[zil_level physical_theorem]
theorem causallyFollows_refl (p : Vector d) : causallyFollows p p := by
  rw [causallyFollows_iff_isFutureCausal, sub_self]
  exact ⟨by simp, by simp⟩

/-- **Transitivity** of the causal order, from closure of the future cone under addition. -/
@[zil_level bridge_theorem]
theorem causallyFollows_trans {p q r : Vector d} (h1 : causallyFollows p q)
    (h2 : causallyFollows q r) : causallyFollows p r := by
  rw [causallyFollows_iff_isFutureCausal] at h1 h2 ⊢
  have hsum : r - p = (q - p) + (r - q) := by abel
  rw [hsum]
  exact isFutureCausal_add h1 h2

/-- **The Minkowski causal relation is a preorder** (`≤ := causallyFollows`).  Provided as a
`def`, not an instance, to avoid clashing with the pointwise `Pi` order on `Vector d`. -/
def causalPreorder : Preorder (Vector d) where
  le := causallyFollows
  le_refl := causallyFollows_refl
  le_trans := fun _ _ _ hab hbc => causallyFollows_trans hab hbc

/-- **The causal diamond is the order interval** of the causal preorder:
`causalDiamond p q = Set.Icc p q`.  This is the identification of the spacetime Alexandrov
interval with the order-theoretic one that Malament's theorem turns on. -/
@[zil_level bridge_theorem]
theorem causalDiamond_eq_Icc (p q : Vector d) :
    causalDiamond p q = @Set.Icc (Vector d) causalPreorder p q := rfl

end Lorentz.Vector

/- ZIL-BEGIN -/

open Zil
open Lorentz.Vector

zil attach causallyFollows_trans where
  formalizes @ "claim:the-minkowski-causal-order-is-transitive-because-the-future-causal-cone-is-closed-under-addition",
  supported_by @ "lean:Lorentz.Vector.isFutureCausal_add",
  supported_by @ "lean:Lorentz.Vector.minkowskiProduct_nonneg_of_futureCausal"

zil attach minkowskiProduct_nonneg_of_futureCausal where
  supported_by @ "lean:Vector.minkowskiProduct_eq_timeComponent_spatialPart",
  supported_by @ "lean:Vector.minkowskiProduct_self_eq_timeComponent_spatialPart",
  formalizes @ "claim:the-minkowski-inner-product-of-two-future-directed-causal-vectors-is-nonnegative-the-closed-cone-reverse-cauchy-schwarz"

zil attach causalDiamond_eq_Icc where
  formalizes @ "claim:the-causal-diamond-equals-the-order-interval-of-the-causal-preorder-identifying-the-spacetime-alexandrov-interval-with-the-order-theoretic-one"

zil_file_contract physlib.causalPreorder where
  promises "The Minkowski causal relation causallyFollows on Lorentz vectors is a genuine preorder: reflexive because every event lies on its own light cone, and transitive because the future causal cone is closed under addition. Closure under addition rests on the closed-cone reverse Cauchy-Schwarz inequality that the Minkowski inner product of two future-directed causal vectors is nonnegative. The causal order is packaged as a Preorder, and the causal diamond is shown to equal the order interval Set.Icc of that preorder - identifying the spacetime Alexandrov interval with the order-theoretic one on which Malament's theorem turns."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Lorentz.Vector.causallyFollows",
    "lean:Lorentz.Vector.IsFutureCausal",
    "lean:Lorentz.Vector.causalDiamond"
  ]
  forbids_substitutes [
    "using the pointwise Pi order on Vector d in place of the causal order",
    "claiming antisymmetry or a partial-order structure not established here"
  ]
  witnessed_by [
    minkowskiProduct_nonneg_of_futureCausal,
    isFutureCausal_add,
    causallyFollows_refl,
    causallyFollows_trans,
    causalDiamond_eq_Icc
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.causalPreorder
