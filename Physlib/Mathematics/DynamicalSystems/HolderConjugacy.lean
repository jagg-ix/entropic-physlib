/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Tactic
meta import Zil

/-!
# Quantitative Hölder conjugacy and the Fisher--Anosov threshold

This module extracts the native metric content used by A. Gogolev,
*Diffeomorphisms Hölder Conjugate to Anosov Diffeomorphisms*.  It builds on Mathlib's
`HolderWith` rather than introducing a parallel continuity notion.

* `BiHolderConjugacy` records a topological conjugacy, its inverse, and the two Hölder estimates.
* `conjugates_iterate` transports every finite orbit through the conjugacy.
* `holder_roundtrip` proves that composing the two estimates multiplies their exponents.
* `orbit_distance_transfer` transfers quantitative orbit separation through the Hölder map.
* `fisherThreshold_iff_shadowingExponent_lt_one` identifies the paper's condition
  `αβ > 1/2` with the strict shadowing exponent `1/(2αβ) < 1`.
* the Gogolev tangency exponents are proved to lie below that threshold in the `C¹⁺Lip`
  counterexample, while the general tangency formula records exactly when the exponent product
  would exceed it.

## Honest scope

This module proves the Hölder, orbit, and threshold mechanism used in Fisher's theorem.  The
companion module `DerivativeCocycleHyperbolicity` now supplies the intrinsic manifold derivative
cocycle and continuous stable/unstable tangent-bundle geometry, while `MatherSpectrum` supplies
the compact Banach carrier and genuine complex spectrum under explicit global-frame and
complexification data.  These modules do not yet prove that a particular Hölder-conjugate system
satisfies the hyperbolicity data or the full Mather criterion `1 ∉ σ ↔ Anosov`.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Mathematics.DynamicalSystems.HolderConjugacy

variable {X : Type*} [PseudoMetricSpace X]

/-! ## A. Native bi-Hölder conjugacy -/

/-- A conjugacy `h ∘ f = g ∘ h` whose forward and inverse maps carry explicit Mathlib
Hölder constants and exponents. -/
structure BiHolderConjugacy (f g : X → X) (Ch α Ci β : NNReal) where
  /-- The conjugating homeomorphism as a function. -/
  h : X → X
  /-- Its inverse. -/
  hInv : X → X
  /-- `hInv` is a left inverse of `h`. -/
  left_inv : Function.LeftInverse hInv h
  /-- `hInv` is a right inverse of `h`. -/
  right_inv : Function.RightInverse hInv h
  /-- The dynamical conjugacy equation. -/
  conjugates : ∀ x, h (f x) = g (h x)
  /-- The forward Hölder estimate. -/
  holder : HolderWith Ch α h
  /-- The inverse Hölder estimate. -/
  holderInv : HolderWith Ci β hInv

namespace BiHolderConjugacy

variable {f g : X → X} {Ch α Ci β : NNReal}

/-- A conjugacy transports every finite iterate: `h(fⁿx)=gⁿ(hx)`. -/
lemma conjugates_iterate (H : BiHolderConjugacy f g Ch α Ci β) (n : ℕ) (x : X) :
    H.h (f^[n] x) = g^[n] (H.h x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', H.conjugates, ih]

/-- Forward followed by inverse Hölder transport multiplies the exponents to `βα` and gives an
explicit Hölder estimate for the identity. -/
lemma holder_roundtrip (H : BiHolderConjugacy f g Ch α Ci β) :
    HolderWith (Ci * Ch ^ (β : ℝ)) (β * α) (id : X → X) := by
  have hc := H.holderInv.comp H.holder
  convert hc using 1
  funext x
  exact (H.left_inv x).symm

/-- Inverse followed by forward transport gives the symmetric exponent product `αβ`. -/
lemma holder_inverse_roundtrip (H : BiHolderConjugacy f g Ch α Ci β) :
    HolderWith (Ch * Ci ^ (α : ℝ)) (α * β) (id : X → X) := by
  have hc := H.holder.comp H.holderInv
  convert hc using 1
  funext x
  exact (H.right_inv x).symm

/-- Orbit separation in the conjugate dynamics is bounded by the original orbit separation raised
to the forward Hölder exponent. -/
lemma orbit_distance_transfer (H : BiHolderConjugacy f g Ch α Ci β)
    (n : ℕ) (x y : X) :
    dist (g^[n] (H.h x)) (g^[n] (H.h y)) ≤
      Ch * dist (f^[n] x) (f^[n] y) ^ (α : ℝ) := by
  rw [← H.conjugates_iterate n x, ← H.conjugates_iterate n y]
  exact H.holder.dist_le _ _

end BiHolderConjugacy

/-! ## B. Fisher's exponent threshold -/

/-- The quantitative exponent hypothesis in Fisher's positive theorem: `αβ > 1/2`. -/
def FisherThreshold (α β : NNReal) : Prop := 1 / 2 < α * β

/-- Fisher's threshold is symmetric in the conjugacy and inverse exponents. -/
lemma fisherThreshold_comm (α β : NNReal) :
    FisherThreshold α β ↔ FisherThreshold β α := by
  simp [FisherThreshold, mul_comm]

/-- The shadowing exponent `κ=1/(2αβ)` appearing in the proof of Fisher's theorem. -/
noncomputable def shadowingExponent (α β : ℝ) : ℝ := (2 * α * β)⁻¹

/-- For positive exponents, Fisher's hypothesis `αβ>1/2` is exactly the strict inequality
`κ=1/(2αβ)<1` needed to contradict linear Anosov shadowing. -/
lemma fisherThreshold_iff_shadowingExponent_lt_one (α β : ℝ)
    (hα : 0 < α) (hβ : 0 < β) :
    (1 / 2 < α * β) ↔ shadowingExponent α β < 1 := by
  have hp : 0 < 2 * α * β := by positivity
  change (1 / 2 : ℝ) < α * β ↔ (2 * α * β)⁻¹ < 1
  rw [inv_lt_one₀ hp]
  constructor <;> intro h <;> nlinarith

/-! ## C. Gogolev tangency diagnostics -/

/-- Forward Hölder exponent `1/2-δ` of the `C¹⁺Lip` tangency counterexample. -/
noncomputable def gogolevForwardExponent (δ : ℝ) : ℝ := 1 / 2 - δ

/-- Inverse Hölder exponent `1/4-δ` of the `C¹⁺Lip` tangency counterexample. -/
noncomputable def gogolevInverseExponent (δ : ℝ) : ℝ := 1 / 4 - δ

/-- At `δ=0`, the limiting product of the displayed counterexample exponents is `1/8`. -/
lemma gogolev_endpoint_product :
    gogolevForwardExponent 0 * gogolevInverseExponent 0 = 1 / 8 := by
  norm_num [gogolevForwardExponent, gogolevInverseExponent]

/-- For the paper's range `0≤δ<1/4`, the counterexample's exponent product stays below Fisher's
`1/2` threshold, so the negative and positive results do not conflict. -/
lemma gogolev_tangency_below_fisher_threshold (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ4 : δ < 1 / 4) :
    gogolevForwardExponent δ * gogolevInverseExponent δ < 1 / 2 := by
  unfold gogolevForwardExponent gogolevInverseExponent
  nlinarith [mul_pos (by linarith : 0 < 1 / 2 - δ) (by linarith : 0 < 1 / 4 - δ)]

/-- Forward exponent `1/(1+a)` for a tangency of order `1+a`. -/
noncomputable def tangencyForwardExponent (a : ℝ) : ℝ := (1 + a)⁻¹

/-- Inverse exponent `(2-a)/(2(1+a))` for a tangency of order `1+a`. -/
noncomputable def tangencyInverseExponent (a : ℝ) : ℝ := (2 - a) / (2 * (1 + a))

/-- The product of the two general tangency exponents is
`(2-a)/(2(1+a)²)`. -/
lemma tangency_exponent_product (a : ℝ) :
    tangencyForwardExponent a * tangencyInverseExponent a =
      (2 - a) / (2 * (1 + a) ^ 2) := by
  unfold tangencyForwardExponent tangencyInverseExponent
  field_simp

/-- For `a>0`, the general tangency exponents cross Fisher's numerical threshold precisely when
`a²+3a<1`.  In that small-`a` regime Gogolev's examples lack the `C¹⁺Lip` regularity required by
Fisher's theorem, another necessary hypothesis that exponent arithmetic alone cannot replace. -/
lemma tangency_fisher_threshold_iff (a : ℝ) (ha0 : 0 < a) :
    1 / 2 < tangencyForwardExponent a * tangencyInverseExponent a ↔
      a ^ 2 + 3 * a < 1 := by
  rw [tangency_exponent_product]
  have hden : 0 < 2 * (1 + a) ^ 2 := by positivity
  rw [lt_div_iff₀ hden]
  ring_nf
  constructor <;> intro h <;> nlinarith

end Physlib.Mathematics.DynamicalSystems.HolderConjugacy

end

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.DynamicalSystems.HolderConjugacy.BiHolderConjugacy.conjugates_iterate where
  formalizes @ "claim:a-bi-holder-conjugacy-transports-every-finite-dynamical-orbit",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:diffeomorphisms-holder-conjugate-to-anosov-diffeomorphisms"

zil attach Physlib.Mathematics.DynamicalSystems.HolderConjugacy.BiHolderConjugacy.holder_roundtrip where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:forward-and-inverse-holder-transport-multiplies-the-two-exponents",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:this-is-the-native-holder-mechanism-not-the-full-differential-geometric-anosov-theorem"

zil attach Physlib.Mathematics.DynamicalSystems.HolderConjugacy.fisherThreshold_iff_shadowingExponent_lt_one where
  formalizes @ "claim:fisher-alpha-beta-greater-than-one-half-is-equivalent-to-shadowing-exponent-kappa-less-than-one",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:diffeomorphisms-holder-conjugate-to-anosov-diffeomorphisms",
  caveat @ "claim:the-lean-result-formalizes-the-quantitative-threshold-step-not-quasi-anosov-or-stable-bundle-geometry"

zil attach Physlib.Mathematics.DynamicalSystems.HolderConjugacy.gogolev_tangency_below_fisher_threshold where
  formalizes @ "claim:gogolev-C1-plus-Lipschitz-tangency-counterexample-exponents-lie-below-the-fisher-threshold",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:diffeomorphisms-holder-conjugate-to-anosov-diffeomorphisms"

zil attach Physlib.Mathematics.DynamicalSystems.HolderConjugacy.tangency_fisher_threshold_iff where
  formalizes @ "claim:general-order-tangency-holder-exponents-cross-one-half-exactly-when-a-squared-plus-three-a-is-less-than-one",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:small-order-tangencies-crossing-the-numerical-threshold-do-not-have-the-C1-plus-Lipschitz-regularity-assumed-by-fisher"

zil_file_contract physlib.holderConjugacyHyperbolicity where
  promises "The native Holder calculus behind the Gogolev-Fisher Anosov discussion: iterate transport, exponent multiplication, orbit-distance transfer, the alpha-beta > 1/2 shadowing threshold, and exact diagnostics for the tangency counterexample exponents."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:HolderWith"]
  forbids_substitutes ["an abstract predicate relabeled as an Anosov diffeomorphism",
    "claiming stable-bundle or Mather-spectrum results without derivative-cocycle infrastructure"]
  witnessed_by [Physlib.Mathematics.DynamicalSystems.HolderConjugacy.BiHolderConjugacy.conjugates_iterate,
    Physlib.Mathematics.DynamicalSystems.HolderConjugacy.BiHolderConjugacy.holder_roundtrip,
    Physlib.Mathematics.DynamicalSystems.HolderConjugacy.fisherThreshold_iff_shadowingExponent_lt_one,
    Physlib.Mathematics.DynamicalSystems.HolderConjugacy.gogolev_tangency_below_fisher_threshold,
    Physlib.Mathematics.DynamicalSystems.HolderConjugacy.tangency_fisher_threshold_iff]

/- ZIL-END -/
