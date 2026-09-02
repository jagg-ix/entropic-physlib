/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausalPreorder
meta import Zil

/-!
# Zeeman's light-ray preservation

The Alexandrov–Zeeman converse turns on the fact that a causal automorphism carries null
rays to null rays.  There are now two proved order descriptions of the null boundary.
The elementary one uses causal and chronological reachability:

`q ∈ futureLightConeBoundary p ↔ causallyFollows p q ∧ q ∉ interiorFutureLightCone p`

(`futureLightConeBoundary_iff`), because the timelike (interior) and lightlike (boundary)
characters are exclusive.

The deeper 3+1-dimensional description eliminates chronology as an extra primitive:
a future-null Alexandrov interval is exactly a causal interval that is a **chain**
(`futureLightConeBoundary_iff_causalDiamond_isChain`).  Null intervals are chains by the
equality case of the closed-cone reverse Cauchy–Schwarz inequality; timelike intervals are
not chains because they contain an explicitly constructed spacelike-incomparable pair.
Since both causality and the chain property are order invariant, every bare causal
automorphism preserves light rays
(`futureLightConeBoundary_image_of_causalAutomorphism`)—with no continuity or
chronological-preservation premise.  The earlier dimension-polymorphic chrono-causal
theorems remain as useful weaker adapters.  The incidence layer is completed by exact
image theorems for both individual future rays (`futureNullRay_image_of_causalAutomorphism`)
and complete null affine lines (`nullAffineLine_image_of_causalAutomorphism`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Lorentz.Vector

open realLorentzTensor InnerProductSpace

variable {d : ℕ}

/-- **The null future cone is order-definable.**  A point lies on the future light-cone
boundary exactly when it is causally, but not chronologically, reachable — the timelike
(interior) and lightlike (boundary) characters being exclusive. -/
@[zil_level bridge_theorem]
theorem futureLightConeBoundary_iff (p q : Vector d) :
    q ∈ futureLightConeBoundary p ↔ causallyFollows p q ∧ q ∉ interiorFutureLightCone p := by
  constructor
  · intro hq
    refine ⟨Or.inr hq, ?_⟩
    intro hIFLC
    have h1 : causalCharacter (q - p) = CausalCharacter.lightLike := hq.1
    have h2 : causalCharacter (q - p) = CausalCharacter.timeLike := hIFLC.1
    rw [h1] at h2
    exact absurd h2 (by decide)
  · rintro ⟨hcf, hni⟩
    rcases hcf with hi | hb
    · exact absurd hi hni
    · exact hb

/-- **A causal automorphism** of Minkowski space: a bijection preserving the causal
"follows" relation in both directions. -/
def IsCausalAutomorphism (φ : Vector d → Vector d) : Prop :=
  Function.Bijective φ ∧ ∀ p q, causallyFollows (φ p) (φ q) ↔ causallyFollows p q

/-! ## Null intervals are exactly the chain intervals in 3+1 dimensions -/

private lemma futureCausal_null_norm_eq_time {v : Vector 3}
    (hv : IsFutureCausal v) (hq : ⟪v, v⟫ₘ = 0) :
    ‖spatialPart v‖ = timeComponent v := by
  rw [minkowskiProduct_self_eq_timeComponent_spatialPart] at hq
  rw [Real.norm_eq_abs, sq_abs] at hq
  have hs : ‖spatialPart v‖ ^ 2 = (timeComponent v) ^ 2 := by linarith
  nlinarith [norm_nonneg (spatialPart v), hv.2]

/-- Two future-directed null vectors with zero Minkowski product lie on the same ray. -/
lemma futureCausal_null_sameRay_of_mink_zero {u v : Vector 3}
    (hu : IsFutureCausal u) (hv : IsFutureCausal v)
    (huq : ⟪u, u⟫ₘ = 0) (hvq : ⟪v, v⟫ₘ = 0)
    (huv : ⟪u, v⟫ₘ = 0) : SameRay ℝ u v := by
  rcases eq_or_ne u 0 with rfl | hu0
  · exact SameRay.zero_left _
  rcases eq_or_ne v 0 with rfl | hv0
  · exact SameRay.zero_right _
  have htu : 0 < timeComponent u := by
    apply lt_of_le_of_ne hu.2
    intro ht
    have hsp : spatialPart u = 0 := by
      apply norm_eq_zero.mp
      rw [futureCausal_null_norm_eq_time hu huq, ht]
    apply hu0
    apply eq_of_apply_eq
    intro i
    rcases i with i | i
    · fin_cases i
      exact ht.symm
    · simpa [spatialPart] using congrArg (fun w => w i) hsp
  have htv : 0 < timeComponent v := by
    apply lt_of_le_of_ne hv.2
    intro ht
    have hsp : spatialPart v = 0 := by
      apply norm_eq_zero.mp
      rw [futureCausal_null_norm_eq_time hv hvq, ht]
    apply hv0
    apply eq_of_apply_eq
    intro i
    rcases i with i | i
    · fin_cases i
      exact ht.symm
    · simpa [spatialPart] using congrArg (fun w => w i) hsp
  have hinner : ⟪u.spatialPart, v.spatialPart⟫_ℝ =
      ‖u.spatialPart‖ * ‖v.spatialPart‖ := by
    rw [minkowskiProduct_eq_timeComponent_spatialPart] at huv
    rw [futureCausal_null_norm_eq_time hu huq,
      futureCausal_null_norm_eq_time hv hvq]
    linarith
  have hspScaled : ‖v.spatialPart‖ • u.spatialPart =
      ‖u.spatialPart‖ • v.spatialPart :=
    (inner_eq_norm_mul_iff_real).mp hinner
  refine Or.inr (Or.inr ⟨timeComponent v, timeComponent u, htv, htu, ?_⟩)
  apply eq_of_apply_eq
  intro i
  rcases i with i | i
  · fin_cases i
    change timeComponent v * timeComponent u = timeComponent u * timeComponent v
    exact mul_comm _ _
  · simpa [futureCausal_null_norm_eq_time hu huq,
      futureCausal_null_norm_eq_time hv hvq, spatialPart] using
      congrArg (fun w => w i) hspScaled

private lemma futureCausal_add_null_sameRay {u v : Vector 3}
    (hu : IsFutureCausal u) (hv : IsFutureCausal v)
    (hsum : ⟪u + v, u + v⟫ₘ = 0) : SameRay ℝ u v := by
  have huv : 0 ≤ ⟪u, v⟫ₘ :=
    minkowskiProduct_nonneg_of_futureCausal hu.1 hv.1 hu.2 hv.2
  have hexp : ⟪u + v, u + v⟫ₘ =
      ⟪u, u⟫ₘ + 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by
    simp only [map_add, add_apply]
    rw [minkowskiProduct_symm v u]
    ring
  have huq : ⟪u, u⟫ₘ = 0 := by nlinarith [hu.1, hv.1, huv, hexp]
  have hvq : ⟪v, v⟫ₘ = 0 := by nlinarith [hu.1, hv.1, huv, hexp]
  have huvq : ⟪u, v⟫ₘ = 0 := by nlinarith [hu.1, hv.1, huv, hexp]
  exact futureCausal_null_sameRay_of_mink_zero hu hv huq hvq huvq

private lemma isFutureCausal_smul_nonneg {v : Vector 3} (hv : IsFutureCausal v)
    {a : ℝ} (ha : 0 ≤ a) : IsFutureCausal (a • v) := by
  constructor
  · simp only [map_smul, smul_apply, smul_eq_mul]
    nlinarith [hv.1, sq_nonneg a]
  · change 0 ≤ a * timeComponent v
    exact mul_nonneg ha hv.2

private lemma minkowskiProduct_smul_self (a : ℝ) (v : Vector 3) :
    ⟪a • v, a • v⟫ₘ = a ^ 2 * ⟪v, v⟫ₘ := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- A causal diamond is a **chain** when any two events in it are causally related.
This predicate uses only the causal order and is therefore invariant under causal-order
automorphisms. -/
def CausalDiamondIsChain (p q : Vector 3) : Prop :=
  ∀ r, r ∈ causalDiamond p q → ∀ s, s ∈ causalDiamond p q → causallyRelated r s

/-- A future-null Alexandrov interval is a causal chain: all its points lie on the same
null segment.  The proof derives the same-ray property from equality in the closed-cone
reverse Cauchy–Schwarz inequality. -/
@[zil_level physical_theorem]
theorem causalDiamond_isChain_of_futureNull {p q : Vector 3}
    (hq : q ∈ futureLightConeBoundary p) : CausalDiamondIsChain p q := by
  have hnC : IsFutureCausal (q - p) :=
    (causallyFollows_iff_isFutureCausal p q).mp (Or.inr hq)
  have hnQ : ⟪q - p, q - p⟫ₘ = 0 :=
    (lightLike_iff_norm_sq_zero _).mp hq.1
  intro r hr s hs
  have hur : IsFutureCausal (r - p) :=
    (causallyFollows_iff_isFutureCausal p r).mp hr.1
  have hvr : IsFutureCausal (q - r) :=
    (causallyFollows_iff_isFutureCausal r q).mp hr.2
  have hsumr : (r - p) + (q - r) = q - p := by abel
  have hrRay : SameRay ℝ (r - p) (q - r) :=
    futureCausal_add_null_sameRay hur hvr (by rw [hsumr, hnQ])
  obtain ⟨ar, br, har, hbr, habr, hru, _⟩ := hrRay.exists_eq_smul_add
  have hrparam : r - p = ar • (q - p) := by rw [hru, hsumr]
  have hus : IsFutureCausal (s - p) :=
    (causallyFollows_iff_isFutureCausal p s).mp hs.1
  have hvs : IsFutureCausal (q - s) :=
    (causallyFollows_iff_isFutureCausal s q).mp hs.2
  have hsums : (s - p) + (q - s) = q - p := by abel
  have hsRay : SameRay ℝ (s - p) (q - s) :=
    futureCausal_add_null_sameRay hus hvs (by rw [hsums, hnQ])
  obtain ⟨as, bs, has, hbs, habs, hsu, _⟩ := hsRay.exists_eq_smul_add
  have hsparam : s - p = as • (q - p) := by rw [hsu, hsums]
  rcases le_total ar as with hars | hasr
  · apply Or.inl
    rw [causallyFollows_iff_isFutureCausal]
    have hdiff : s - r = (as - ar) • (q - p) := by
      rw [← sub_add_cancel r p, ← sub_add_cancel s p, hrparam, hsparam]
      module
    rw [hdiff]
    exact isFutureCausal_smul_nonneg hnC (sub_nonneg.mpr hars)
  · apply Or.inr
    rw [causallyFollows_iff_isFutureCausal]
    have hdiff : r - s = (ar - as) • (q - p) := by
      rw [← sub_add_cancel r p, ← sub_add_cancel s p, hrparam, hsparam]
      module
    rw [hdiff]
    exact isFutureCausal_smul_nonneg hnC (sub_nonneg.mpr hasr)

private def lightRayFutureTimelikeCone3 : Set (Vector 3) :=
  {v | 0 < ⟪v, v⟫ₘ ∧ 0 < timeComponent v}

private lemma isOpen_lightRayFutureTimelikeCone3 : IsOpen lightRayFutureTimelikeCone3 := by
  have hQ : Continuous (fun v : Vector 3 => ⟪v, v⟫ₘ) := by
    conv =>
      enter [1, v]
      rw [minkowskiProduct_toCoord]
    fun_prop
  exact (isOpen_lt continuous_const hQ).inter
    (isOpen_lt continuous_const (coord_continuous (Sum.inl 0)))

private def lightRaySpatialBasis0 : Vector 3 := basis (Sum.inr 0)

private lemma lightRaySpatialBasis0_norm : ‖lightRaySpatialBasis0‖ = 1 := by
  rw [norm_eq_equivEuclid]
  simp [lightRaySpatialBasis0, basis_apply, PiLp.norm_eq_of_L2]

/-- A future-timelike Alexandrov interval is **not** a chain.  Around its midpoint the
proof constructs two events separated by a nonzero spatial vector; both stay inside the
timelike diamond, but they are spacelike-incomparable. -/
@[zil_level physical_theorem]
theorem causalDiamond_not_isChain_of_futureTimelike {p q : Vector 3}
    (hq : q ∈ interiorFutureLightCone p) : ¬ CausalDiamondIsChain p q := by
  let n := q - p
  let m := (1 / 2 : ℝ) • n
  have hnQ : 0 < ⟪n, n⟫ₘ := (timeLike_iff_norm_sq_pos n).mp hq.1
  have hnT : 0 < timeComponent n := hq.2
  have hmT : m ∈ lightRayFutureTimelikeCone3 := by
    constructor
    · dsimp [m]
      simp only [map_smul, smul_apply, smul_eq_mul]
      norm_num
      nlinarith
    · change 0 < (1 / 2 : ℝ) * timeComponent n
      positivity
  have hmN := isOpen_lightRayFutureTimelikeCone3.mem_nhds hmT
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmN
  let a := ε / 2
  let w := a • lightRaySpatialBasis0
  have ha : 0 < a := half_pos hε
  have hwNorm : ‖w‖ = a := by
    dsimp [w]
    rw [norm_smul, lightRaySpatialBasis0_norm, mul_one, Real.norm_eq_abs, abs_of_pos ha]
  have hplusBall : m + w ∈ Metric.ball m ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiffPlus : m + w - m = w := by abel
    rw [hdiffPlus, hwNorm]
    dsimp [a]
    linarith
  have hminusBall : m - w ∈ Metric.ball m ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiffMinus : m - w - m = -w := by abel
    rw [hdiffMinus, norm_neg, hwNorm]
    dsimp [a]
    linarith
  have hplusT := hball hplusBall
  have hminusT := hball hminusBall
  let r := p + (m + w)
  let s := p + (m - w)
  have hnm : n = m + m := by
    dsimp [m]
    module
  have hqp : q - p = m + m := by simpa [n] using hnm
  have hr : r ∈ causalDiamond p q := by
    constructor
    · rw [causallyFollows_iff_isFutureCausal]
      have hrDiff : r - p = m + w := by dsimp [r]; abel
      rw [hrDiff]
      exact ⟨hplusT.1.le, hplusT.2.le⟩
    · rw [causallyFollows_iff_isFutureCausal]
      have hqrDiff : q - r = m - w := by
        calc
          q - r = (q - p) - (m + w) := by dsimp [r]; abel
          _ = (m + m) - (m + w) := by rw [hqp]
          _ = m - w := by abel
      rw [hqrDiff]
      exact ⟨hminusT.1.le, hminusT.2.le⟩
  have hs : s ∈ causalDiamond p q := by
    constructor
    · rw [causallyFollows_iff_isFutureCausal]
      have hsDiff : s - p = m - w := by dsimp [s]; abel
      rw [hsDiff]
      exact ⟨hminusT.1.le, hminusT.2.le⟩
    · rw [causallyFollows_iff_isFutureCausal]
      have hqsDiff : q - s = m + w := by
        calc
          q - s = (q - p) - (m - w) := by dsimp [s]; abel
          _ = (m + m) - (m - w) := by rw [hqp]
          _ = m + w := by abel
      rw [hqsDiff]
      exact ⟨hplusT.1.le, hplusT.2.le⟩
  intro hchain
  have hrs := hchain r hr s hs
  have hwQ : ⟪w, w⟫ₘ < 0 := by
    dsimp [w, lightRaySpatialBasis0]
    rw [minkowskiProduct_toCoord]
    simp [basis_apply]
    positivity
  rcases hrs with hrs | hsr
  · have hC := (causallyFollows_iff_isFutureCausal r s).mp hrs
    have hdiff : s - r = -(2 : ℝ) • w := by dsimp [r, s]; module
    rw [hdiff] at hC
    have hCq := hC.1
    rw [minkowskiProduct_smul_self] at hCq
    norm_num at hCq
    nlinarith
  · have hC := (causallyFollows_iff_isFutureCausal s r).mp hsr
    have hdiff : r - s = (2 : ℝ) • w := by dsimp [r, s]; module
    rw [hdiff] at hC
    have hCq := hC.1
    rw [minkowskiProduct_smul_self] at hCq
    norm_num at hCq
    nlinarith

/-- **Pure causal-order definition of future null separation in 3+1 dimensions.**
`q` is future-null from `p` exactly when `p ≤ q` and their Alexandrov interval is a
chain.  Thus chronology is not needed as an additional primitive for detecting the null
boundary. -/
@[zil_level bridge_theorem]
theorem futureLightConeBoundary_iff_causalDiamond_isChain (p q : Vector 3) :
    q ∈ futureLightConeBoundary p ↔
      causallyFollows p q ∧ CausalDiamondIsChain p q := by
  constructor
  · intro hq
    exact ⟨Or.inr hq, causalDiamond_isChain_of_futureNull hq⟩
  · rintro ⟨hpq, hchain⟩
    rcases hpq with htime | hnull
    · exact False.elim (causalDiamond_not_isChain_of_futureTimelike htime hchain)
    · exact hnull

/-- **Pure causal-order definition of chronological separation in 3+1 dimensions.**
`q` is timelike-future from `p` exactly when it is causally reachable and their causal
diamond is not a chain.  This is the complementary half of
`futureLightConeBoundary_iff_causalDiamond_isChain`. -/
@[zil_level bridge_theorem]
theorem interiorFutureLightCone_iff_causalDiamond_not_isChain (p q : Vector 3) :
    q ∈ interiorFutureLightCone p ↔
      causallyFollows p q ∧ ¬ CausalDiamondIsChain p q := by
  constructor
  · intro hq
    exact ⟨Or.inl hq, causalDiamond_not_isChain_of_futureTimelike hq⟩
  · rintro ⟨hpq, hnchain⟩
    rcases hpq with htime | hnull
    · exact htime
    · exact False.elim (hnchain (causalDiamond_isChain_of_futureNull hnull))

/-- Causal-chain interval structure is invariant under every causal automorphism. -/
@[zil_level bridge_theorem]
theorem causalDiamondIsChain_iff_of_causalAutomorphism {φ : Vector 3 → Vector 3}
    (hφ : IsCausalAutomorphism φ) (p q : Vector 3) :
    CausalDiamondIsChain (φ p) (φ q) ↔ CausalDiamondIsChain p q := by
  constructor
  · intro hchain r hr s hs
    have hφr : φ r ∈ causalDiamond (φ p) (φ q) :=
      ⟨(hφ.2 p r).mpr hr.1, (hφ.2 r q).mpr hr.2⟩
    have hφs : φ s ∈ causalDiamond (φ p) (φ q) :=
      ⟨(hφ.2 p s).mpr hs.1, (hφ.2 s q).mpr hs.2⟩
    rcases hchain (φ r) hφr (φ s) hφs with hrs | hsr
    · exact Or.inl ((hφ.2 r s).mp hrs)
    · exact Or.inr ((hφ.2 s r).mp hsr)
  · intro hchain r hr s hs
    obtain ⟨r₀, rfl⟩ := hφ.1.surjective r
    obtain ⟨s₀, rfl⟩ := hφ.1.surjective s
    have hr₀ : r₀ ∈ causalDiamond p q :=
      ⟨(hφ.2 p r₀).mp hr.1, (hφ.2 r₀ q).mp hr.2⟩
    have hs₀ : s₀ ∈ causalDiamond p q :=
      ⟨(hφ.2 p s₀).mp hs.1, (hφ.2 s₀ q).mp hs.2⟩
    rcases hchain r₀ hr₀ s₀ hs₀ with hrs | hsr
    · exact Or.inl ((hφ.2 r₀ s₀).mpr hrs)
    · exact Or.inr ((hφ.2 s₀ r₀).mpr hsr)

/-- **Zeeman light-ray preservation from the causal order alone.**  Every causal
automorphism of 3+1 Minkowski space preserves future-null separation pointwise; no
separate chronological-preservation or continuity premise is required. -/
@[zil_level physical_theorem]
theorem futureLightConeBoundary_mem_iff_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ) (p q : Vector 3) :
    φ q ∈ futureLightConeBoundary (φ p) ↔ q ∈ futureLightConeBoundary p := by
  rw [futureLightConeBoundary_iff_causalDiamond_isChain,
    futureLightConeBoundary_iff_causalDiamond_isChain,
    hφ.2 p q, causalDiamondIsChain_iff_of_causalAutomorphism hφ p q]

/-- A bare causal automorphism of 3+1 Minkowski space also preserves chronological
(timelike) reachability; no independent chronology premise is necessary. -/
@[zil_level physical_theorem]
theorem interiorFutureLightCone_mem_iff_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ) (p q : Vector 3) :
    φ q ∈ interiorFutureLightCone (φ p) ↔ q ∈ interiorFutureLightCone p := by
  rw [interiorFutureLightCone_iff_causalDiamond_not_isChain,
    interiorFutureLightCone_iff_causalDiamond_not_isChain,
    hφ.2 p q, causalDiamondIsChain_iff_of_causalAutomorphism hφ p q]

/-! ## Open chronological diamonds -/

/-- The open chronological Alexandrov interval between two events in physical 3+1
Minkowski space. -/
def chronologicalDiamond3 (p q : Vector 3) : Set (Vector 3) :=
  {r | r ∈ interiorFutureLightCone p ∧ q ∈ interiorFutureLightCone r}

/-- Future timelike cones are Euclidean-open in physical 3+1 Minkowski space. -/
@[zil_level bridge_theorem]
theorem isOpen_interiorFutureLightCone3 (p : Vector 3) :
    IsOpen (interiorFutureLightCone p) := by
  have heq : interiorFutureLightCone p =
      (fun q : Vector 3 => q - p) ⁻¹' lightRayFutureTimelikeCone3 := by
    ext q
    simp only [interiorFutureLightCone, lightRayFutureTimelikeCone3,
      Set.mem_setOf_eq, Set.mem_preimage]
    rw [timeLike_iff_norm_sq_pos]
  rw [heq]
  exact isOpen_lightRayFutureTimelikeCone3.preimage (continuous_id.sub continuous_const)

/-- Open chronological diamonds are Euclidean-open. -/
@[zil_level bridge_theorem]
theorem isOpen_chronologicalDiamond3 (p q : Vector 3) :
    IsOpen (chronologicalDiamond3 p q) := by
  have hp : IsOpen {r : Vector 3 | r ∈ interiorFutureLightCone p} :=
    isOpen_interiorFutureLightCone3 p
  have hqeq : {r : Vector 3 | q ∈ interiorFutureLightCone r} =
      (fun r : Vector 3 => q - r) ⁻¹' lightRayFutureTimelikeCone3 := by
    ext r
    simp only [interiorFutureLightCone, lightRayFutureTimelikeCone3,
      Set.mem_setOf_eq, Set.mem_preimage]
    rw [timeLike_iff_norm_sq_pos]
  have hq : IsOpen {r : Vector 3 | q ∈ interiorFutureLightCone r} := by
    rw [hqeq]
    exact isOpen_lightRayFutureTimelikeCone3.preimage (continuous_const.sub continuous_id)
  exact hp.inter hq

/-- A causal automorphism maps each open chronological diamond exactly onto the
chronological diamond between the image endpoints. -/
@[zil_level physical_theorem]
theorem chronologicalDiamond3_image_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ) (p q : Vector 3) :
    φ '' chronologicalDiamond3 p q = chronologicalDiamond3 (φ p) (φ q) := by
  ext s
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(interiorFutureLightCone_mem_iff_of_causalAutomorphism hφ p r).mpr hr.1,
      (interiorFutureLightCone_mem_iff_of_causalAutomorphism hφ r q).mpr hr.2⟩
  · intro hs
    obtain ⟨r, rfl⟩ := hφ.1.surjective s
    exact ⟨r,
      ⟨(interiorFutureLightCone_mem_iff_of_causalAutomorphism hφ p r).mp hs.1,
        (interiorFutureLightCone_mem_iff_of_causalAutomorphism hφ r q).mp hs.2⟩,
      rfl⟩

/-- A causal automorphism of 3+1 Minkowski space maps the complete future null cone of
each event onto the future null cone of its image. -/
@[zil_level bridge_theorem]
theorem futureLightConeBoundary_image_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ) (p : Vector 3) :
    φ '' futureLightConeBoundary p = futureLightConeBoundary (φ p) := by
  ext s
  simp only [Set.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p q).mpr hq
  · intro hs
    obtain ⟨q, rfl⟩ := hφ.1.surjective s
    exact ⟨q, (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p q).mp hs, rfl⟩

/-! ## Individual future null rays are preserved -/

/-- The future affine ray based at `p` with direction `n`.  The geometric light-ray
theorems below assume separately that `n` is a nonzero future-null vector. -/
def futureNullRay (p n : Vector 3) : Set (Vector 3) :=
  {q | ∃ a : ℝ, 0 ≤ a ∧ q = p + a • n}

private lemma add_smul_mem_futureLightConeBoundary {p n : Vector 3}
    (hnQ : ⟪n, n⟫ₘ = 0) (hnT : 0 ≤ timeComponent n)
    {a : ℝ} (ha : 0 ≤ a) : p + a • n ∈ futureLightConeBoundary p := by
  have hdiff : p + a • n - p = a • n := by abel
  constructor
  · rw [lightLike_iff_norm_sq_zero, hdiff, minkowskiProduct_smul_self, hnQ, mul_zero]
  · rw [hdiff]
    change 0 ≤ a * timeComponent n
    exact mul_nonneg ha hnT

private lemma points_on_futureNullRay_are_nullComparable {p n : Vector 3}
    (hnQ : ⟪n, n⟫ₘ = 0) (hnT : 0 ≤ timeComponent n)
    (a b : ℝ) :
    p + a • n ∈ futureLightConeBoundary (p + b • n) ∨
      p + b • n ∈ futureLightConeBoundary (p + a • n) := by
  rcases le_total b a with hba | hab
  · left
    have hdiff : p + a • n - (p + b • n) = (a - b) • n := by module
    constructor
    · rw [lightLike_iff_norm_sq_zero, hdiff, minkowskiProduct_smul_self, hnQ, mul_zero]
    · rw [hdiff]
      change 0 ≤ (a - b) * timeComponent n
      exact mul_nonneg (sub_nonneg.mpr hba) hnT
  · right
    have hdiff : p + b • n - (p + a • n) = (b - a) • n := by module
    constructor
    · rw [lightLike_iff_norm_sq_zero, hdiff, minkowskiProduct_smul_self, hnQ, mul_zero]
    · rw [hdiff]
      change 0 ≤ (b - a) * timeComponent n
      exact mul_nonneg (sub_nonneg.mpr hab) hnT

private lemma futureCausal_null_sameRay_of_null_sub {u v : Vector 3}
    (hu : IsFutureCausal u) (hv : IsFutureCausal v)
    (huQ : ⟪u, u⟫ₘ = 0) (hvQ : ⟪v, v⟫ₘ = 0)
    (hsubQ : ⟪u - v, u - v⟫ₘ = 0) : SameRay ℝ u v := by
  have hexp : ⟪u - v, u - v⟫ₘ =
      ⟪u, u⟫ₘ - 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by
    simp only [map_sub, sub_apply]
    rw [minkowskiProduct_symm v u]
    ring
  have huv : ⟪u, v⟫ₘ = 0 := by nlinarith
  exact futureCausal_null_sameRay_of_mink_zero hu hv huQ hvQ huv

private lemma sameRay_vsub_of_futureNullComparable {p q r : Vector 3}
    (hq : q ∈ futureLightConeBoundary p)
    (hr : r ∈ futureLightConeBoundary p)
    (hqr : q ∈ futureLightConeBoundary r ∨ r ∈ futureLightConeBoundary q) :
    SameRay ℝ (q - p) (r - p) := by
  have hqC : IsFutureCausal (q - p) :=
    (causallyFollows_iff_isFutureCausal p q).mp (Or.inr hq)
  have hrC : IsFutureCausal (r - p) :=
    (causallyFollows_iff_isFutureCausal p r).mp (Or.inr hr)
  have hqQ : ⟪q - p, q - p⟫ₘ = 0 := (lightLike_iff_norm_sq_zero _).mp hq.1
  have hrQ : ⟪r - p, r - p⟫ₘ = 0 := (lightLike_iff_norm_sq_zero _).mp hr.1
  have hsubQ : ⟪(q - p) - (r - p), (q - p) - (r - p)⟫ₘ = 0 := by
    rcases hqr with hqr | hrq
    · have h := (lightLike_iff_norm_sq_zero _).mp hqr.1
      have heq : (q - p) - (r - p) = q - r := by abel
      simpa only [heq] using h
    · have h := (lightLike_iff_norm_sq_zero _).mp hrq.1
      have heq : (q - p) - (r - p) = -(r - q) := by abel
      rw [heq]
      have hneg : ⟪-(r - q), -(r - q)⟫ₘ = ⟪r - q, r - q⟫ₘ := by
        simp only [map_neg]
        change -(-⟪r - q, r - q⟫ₘ) = ⟪r - q, r - q⟫ₘ
        exact neg_neg _
      rw [hneg]
      exact h
  exact futureCausal_null_sameRay_of_null_sub hqC hrC hqQ hrQ hsubQ

/-- **Individual light-ray preservation.**  A causal automorphism maps every nondegenerate
future null ray *onto* the future null ray based at the image event and directed through
the image of one point on the original ray.  This strengthens whole-cone preservation to
the actual incidence statement needed by the affine-geometry reduction. -/
@[zil_level physical_theorem]
theorem futureNullRay_image_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p n : Vector 3} (hnQ : ⟪n, n⟫ₘ = 0)
    (hnT : 0 ≤ timeComponent n) (hn0 : n ≠ 0) :
    φ '' futureNullRay p n = futureNullRay (φ p) (φ (p + n) - φ p) := by
  have hnBoundary : p + n ∈ futureLightConeBoundary p := by
    simpa only [one_smul] using
      add_smul_mem_futureLightConeBoundary hnQ hnT (a := (1 : ℝ)) zero_le_one
  have hφnBoundary : φ (p + n) ∈ futureLightConeBoundary (φ p) :=
    (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p (p + n)).mpr hnBoundary
  have hdir0 : φ (p + n) - φ p ≠ 0 := by
    intro hzero
    have heq : φ (p + n) = φ p := sub_eq_zero.mp hzero
    have heq' := hφ.1.injective heq
    apply hn0
    simpa only [add_eq_left] using heq'
  ext s
  constructor
  · rintro ⟨q, ⟨a, ha, rfl⟩, rfl⟩
    have hqBoundary : p + a • n ∈ futureLightConeBoundary p :=
      add_smul_mem_futureLightConeBoundary hnQ hnT ha
    have hφqBoundary : φ (p + a • n) ∈ futureLightConeBoundary (φ p) :=
      (futureLightConeBoundary_mem_iff_of_causalAutomorphism
        hφ p (p + a • n)).mpr hqBoundary
    have hsep := points_on_futureNullRay_are_nullComparable
      (p := p) (n := n) hnQ hnT a 1
    have hφsep :
        φ (p + a • n) ∈ futureLightConeBoundary (φ (p + n)) ∨
          φ (p + n) ∈ futureLightConeBoundary (φ (p + a • n)) := by
      rcases hsep with hsep | hsep
      · exact Or.inl ((futureLightConeBoundary_mem_iff_of_causalAutomorphism
          hφ (p + n) (p + a • n)).mpr (by simpa only [one_smul] using hsep))
      · exact Or.inr ((futureLightConeBoundary_mem_iff_of_causalAutomorphism
          hφ (p + a • n) (p + n)).mpr (by simpa only [one_smul] using hsep))
    have hray := sameRay_vsub_of_futureNullComparable hφqBoundary hφnBoundary hφsep
    obtain ⟨b, hb, hbeq⟩ := hray.exists_nonneg_right hdir0
    refine ⟨b, hb, ?_⟩
    calc
      φ (p + a • n) = (φ (p + a • n) - φ p) + φ p := by abel
      _ = b • (φ (p + n) - φ p) + φ p := by rw [hbeq]
      _ = φ p + b • (φ (p + n) - φ p) := add_comm _ _
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨q, hq⟩ := hφ.1.surjective
      (φ p + b • (φ (p + n) - φ p))
    have hφdirQ : ⟪φ (p + n) - φ p, φ (p + n) - φ p⟫ₘ = 0 :=
      (lightLike_iff_norm_sq_zero _).mp hφnBoundary.1
    have hφdirT : 0 ≤ timeComponent (φ (p + n) - φ p) := hφnBoundary.2
    have hsBoundary : φ q ∈ futureLightConeBoundary (φ p) := by
      rw [hq]
      exact add_smul_mem_futureLightConeBoundary hφdirQ hφdirT hb
    have hqBoundary : q ∈ futureLightConeBoundary p :=
      (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p q).mp hsBoundary
    have hφsep := points_on_futureNullRay_are_nullComparable
      (p := φ p) (n := φ (p + n) - φ p) hφdirQ hφdirT b 1
    have hendpoint : φ p + (1 : ℝ) • (φ (p + n) - φ p) = φ (p + n) := by
      rw [one_smul]
      abel
    rw [hendpoint] at hφsep
    have hsep : q ∈ futureLightConeBoundary (p + n) ∨
        p + n ∈ futureLightConeBoundary q := by
      rw [← hq] at hφsep
      rcases hφsep with hφsep | hφsep
      · exact Or.inl ((futureLightConeBoundary_mem_iff_of_causalAutomorphism
          hφ (p + n) q).mp hφsep)
      · exact Or.inr ((futureLightConeBoundary_mem_iff_of_causalAutomorphism
          hφ q (p + n)).mp hφsep)
    have hray := sameRay_vsub_of_futureNullComparable hqBoundary hnBoundary hsep
    have hndir : p + n - p = n := by abel
    rw [hndir] at hray
    obtain ⟨a, ha, haeq⟩ := hray.exists_nonneg_right hn0
    refine ⟨q, ⟨a, ha, ?_⟩, hq⟩
    calc
      q = (q - p) + p := by abel
      _ = a • n + p := by rw [haeq]
      _ = p + a • n := add_comm _ _

/-! ## Complete null affine lines -/

/-- The complete affine line through `p` with direction `n`.  As for `futureNullRay`,
nullness and nondegeneracy of the direction are hypotheses of the geometric theorems. -/
def nullAffineLine (p n : Vector 3) : Set (Vector 3) :=
  {q | ∃ a : ℝ, q = p + a • n}

private lemma point_eq_base_add_smul_direction_of_sameRay
    {V : Type} [AddCommGroup V] [Module ℝ V]
    {P E Q : V} (hE : E - Q ≠ 0)
    (hray : SameRay ℝ (P - Q) (E - Q)) (hPE : P ≠ E) :
    ∃ t : ℝ, Q = P + t • (E - P) := by
  obtain ⟨c, _, hrel⟩ := hray.exists_nonneg_right hE
  have hc : c ≠ 1 := by
    intro hc
    have hdiff : P - Q = E - Q := by simpa only [hc, one_smul] using hrel
    exact hPE (sub_left_inj.mp hdiff)
  refine ⟨c / (c - 1), ?_⟩
  have hc' : c - 1 ≠ 0 := sub_ne_zero.mpr hc
  have h' := congrArg (fun z : V => z + (c • Q - P)) hrel
  have hcore : (c - 1) • Q = c • E - P := by
    calc
      (c - 1) • Q = (P - Q) + (c • Q - P) := by module
      _ = (c • (E - Q)) + (c • Q - P) := h'
      _ = c • E - P := by module
  apply smul_right_injective V hc'
  change (c - 1) • Q = (c - 1) • (P + (c / (c - 1)) • (E - P))
  rw [hcore]
  rw [_root_.smul_add (c - 1) P ((c / (c - 1)) • (E - P))]
  rw [_root_.smul_smul (c - 1) (c / (c - 1)) (E - P)]
  have hcoef : (c - 1) * (c / (c - 1)) = c := by field_simp
  rw [hcoef]
  module

private theorem mapsTo_nullAffineLine_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p n : Vector 3} (hnQ : ⟪n, n⟫ₘ = 0)
    (hnT : 0 ≤ timeComponent n) (hn0 : n ≠ 0) :
    Set.MapsTo φ (nullAffineLine p n)
      (nullAffineLine (φ p) (φ (p + n) - φ p)) := by
  intro q hq
  rcases hq with ⟨a, rfl⟩
  by_cases ha : 0 ≤ a
  · have hsource : p + a • n ∈ futureNullRay p n := ⟨a, ha, rfl⟩
    have himage : φ (p + a • n) ∈ φ '' futureNullRay p n :=
      ⟨p + a • n, hsource, rfl⟩
    rw [futureNullRay_image_of_causalAutomorphism hφ hnQ hnT hn0] at himage
    rcases himage with ⟨b, _, hb⟩
    exact ⟨b, hb⟩
  · have hna : 0 ≤ -a := by linarith
    have h1a : 0 ≤ 1 - a := by linarith
    have hpBoundary : p ∈ futureLightConeBoundary (p + a • n) := by
      have h := add_smul_mem_futureLightConeBoundary
        (p := p + a • n) hnQ hnT hna
      have heq : (p + a • n) + (-a) • n = p := by module
      simpa only [heq] using h
    have hendBoundary : p + n ∈ futureLightConeBoundary (p + a • n) := by
      have h := add_smul_mem_futureLightConeBoundary
        (p := p + a • n) hnQ hnT h1a
      have heq : (p + a • n) + (1 - a) • n = p + n := by module
      simpa only [heq] using h
    have hφpBoundary : φ p ∈ futureLightConeBoundary (φ (p + a • n)) :=
      (futureLightConeBoundary_mem_iff_of_causalAutomorphism
        hφ (p + a • n) p).mpr hpBoundary
    have hφendBoundary : φ (p + n) ∈ futureLightConeBoundary (φ (p + a • n)) :=
      (futureLightConeBoundary_mem_iff_of_causalAutomorphism
        hφ (p + a • n) (p + n)).mpr hendBoundary
    have hnBoundary : p + n ∈ futureLightConeBoundary p := by
      simpa only [one_smul] using
        add_smul_mem_futureLightConeBoundary hnQ hnT (a := (1 : ℝ)) zero_le_one
    have hφComparable : φ (p + n) ∈ futureLightConeBoundary (φ p) :=
      (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p (p + n)).mpr hnBoundary
    have hray := sameRay_vsub_of_futureNullComparable
      hφpBoundary hφendBoundary (Or.inr hφComparable)
    have hsourceEndNe : p + n ≠ p + a • n := by
      intro heq
      have hz : (1 - a) • n = 0 := by
        have hnaeq : n = a • n := add_left_cancel heq
        calc
          (1 - a) • n = n - a • n := by module
          _ = 0 := sub_eq_zero.mpr hnaeq
      rcases (smul_eq_zero.mp hz) with hc | hn
      · linarith
      · exact hn0 hn
    have himageEndNe : φ (p + n) - φ (p + a • n) ≠ 0 :=
      sub_ne_zero.mpr (hφ.1.injective.ne hsourceEndNe)
    have hpEndNe : φ p ≠ φ (p + n) :=
      hφ.1.injective.ne (by
        intro heq
        apply hn0
        calc
          n = (p + n) - p := by abel
          _ = p - p := by rw [← heq]
          _ = 0 := sub_self p)
    obtain ⟨t, ht⟩ := point_eq_base_add_smul_direction_of_sameRay
      himageEndNe hray hpEndNe
    exact ⟨t, ht⟩

/-- **Complete null-line preservation.**  A causal automorphism maps every nondegenerate
future-directed null affine line onto the affine line through the corresponding image
points.  This is the complete-line collineation datum required by the next, purely affine,
fundamental-theorem step. -/
@[zil_level physical_theorem]
theorem nullAffineLine_image_of_causalAutomorphism
    {φ : Vector 3 → Vector 3} (hφ : IsCausalAutomorphism φ)
    {p n : Vector 3} (hnQ : ⟪n, n⟫ₘ = 0)
    (hnT : 0 ≤ timeComponent n) (hn0 : n ≠ 0) :
    φ '' nullAffineLine p n = nullAffineLine (φ p) (φ (p + n) - φ p) := by
  apply Set.Subset.antisymm
  · rintro s ⟨q, hq, rfl⟩
    exact mapsTo_nullAffineLine_of_causalAutomorphism hφ hnQ hnT hn0 hq
  · intro s hs
    let e : Vector 3 ≃ Vector 3 := Equiv.ofBijective φ hφ.1
    have he_apply (x : Vector 3) : e x = φ x := rfl
    have hinv : IsCausalAutomorphism e.symm := by
      refine ⟨e.symm.bijective, ?_⟩
      intro x y
      calc
        causallyFollows (e.symm x) (e.symm y) ↔
            causallyFollows (φ (e.symm x)) (φ (e.symm y)) :=
          (hφ.2 (e.symm x) (e.symm y)).symm
        _ ↔ causallyFollows x y := by
          rw [← he_apply, ← he_apply, e.apply_symm_apply, e.apply_symm_apply]
    have hnBoundary : p + n ∈ futureLightConeBoundary p := by
      simpa only [one_smul] using
        add_smul_mem_futureLightConeBoundary hnQ hnT (a := (1 : ℝ)) zero_le_one
    have hφnBoundary : e (p + n) ∈ futureLightConeBoundary (e p) := by
      simpa only [he_apply] using
        (futureLightConeBoundary_mem_iff_of_causalAutomorphism hφ p (p + n)).mpr hnBoundary
    have hmQ : ⟪e (p + n) - e p, e (p + n) - e p⟫ₘ = 0 :=
      (lightLike_iff_norm_sq_zero _).mp hφnBoundary.1
    have hmT : 0 ≤ timeComponent (e (p + n) - e p) := hφnBoundary.2
    have hm0 : e (p + n) - e p ≠ 0 := by
      apply sub_ne_zero.mpr
      exact e.injective.ne (by
        intro heq
        apply hn0
        calc
          n = (p + n) - p := by abel
          _ = p - p := by rw [heq]
          _ = 0 := sub_self p)
    have hs' : s ∈ nullAffineLine (e p) (e (p + n) - e p) := by
      simpa only [he_apply] using hs
    have hback := mapsTo_nullAffineLine_of_causalAutomorphism
      hinv hmQ hmT hm0 hs'
    have hendpoint : e p + (e (p + n) - e p) = e (p + n) := by abel
    have hdirBack :
        e.symm (e p + (e (p + n) - e p)) - e.symm (e p) = n := by
      rw [hendpoint, e.symm_apply_apply, e.symm_apply_apply]
      abel
    have hsource : e.symm s ∈ nullAffineLine p n := by
      rw [hdirBack] at hback
      simpa only [e.symm_apply_apply] using hback
    refine ⟨e.symm s, hsource, ?_⟩
    change e (e.symm s) = s
    exact e.apply_symm_apply s

/-- **A chrono-causal automorphism** of Minkowski space: a bijection preserving both the
causal "follows" relation and the chronological (interior-cone) relation. -/
def IsChronoCausalAutomorphism (φ : Vector d → Vector d) : Prop :=
  Function.Bijective φ
    ∧ (∀ p q, causallyFollows (φ p) (φ q) ↔ causallyFollows p q)
    ∧ (∀ p q, φ q ∈ interiorFutureLightCone (φ p) ↔ q ∈ interiorFutureLightCone p)

/-- In physical 3+1 dimensions every causal automorphism is automatically chrono-causal.
This packages the chronology-from-order theorem for compatibility with the older API. -/
@[zil_level bridge_theorem]
theorem IsCausalAutomorphism.toChronoCausalAutomorphism {φ : Vector 3 → Vector 3}
    (hφ : IsCausalAutomorphism φ) : IsChronoCausalAutomorphism φ :=
  ⟨hφ.1, hφ.2, interiorFutureLightCone_mem_iff_of_causalAutomorphism hφ⟩

/-- **Spatial translations are chrono-causal automorphisms** — both the causal and the
chronological relations depend only on the difference `q − p`.  (Non-vacuity witness.) -/
@[zil_level physical_theorem]
theorem translation_isChronoCausalAutomorphism (t : Vector d) :
    IsChronoCausalAutomorphism (fun v => v + t) := by
  refine ⟨(Equiv.addRight t).bijective, ?_, ?_⟩
  · intro p q
    have h : (q + t) - (p + t) = q - p := by abel
    simp only [causallyFollows, interiorFutureLightCone, futureLightConeBoundary,
      Set.mem_setOf_eq, h]
  · intro p q
    have h : (q + t) - (p + t) = q - p := by abel
    simp only [interiorFutureLightCone, Set.mem_setOf_eq, h]

/-- **A chrono-causal automorphism preserves null-cone membership** — the pointwise form of
light-ray preservation, from the order-definability of the null cone. -/
@[zil_level physical_theorem]
theorem futureLightConeBoundary_mem_iff_of_chronoCausalAut {φ : Vector d → Vector d}
    (hφ : IsChronoCausalAutomorphism φ) (p q : Vector d) :
    φ q ∈ futureLightConeBoundary (φ p) ↔ q ∈ futureLightConeBoundary p := by
  rw [futureLightConeBoundary_iff, futureLightConeBoundary_iff, hφ.2.1 p q, hφ.2.2 p q]

/-- **Light-ray preservation (Zeeman).**  A chrono-causal automorphism carries the future
light cone of `p` onto the future light cone of `φ p` — it maps null rays to null rays. -/
@[zil_level bridge_theorem]
theorem futureLightConeBoundary_image_of_chronoCausalAut {φ : Vector d → Vector d}
    (hφ : IsChronoCausalAutomorphism φ) (p : Vector d) :
    φ '' futureLightConeBoundary p = futureLightConeBoundary (φ p) := by
  ext s
  simp only [Set.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (futureLightConeBoundary_mem_iff_of_chronoCausalAut hφ p q).mpr hq
  · intro hs
    obtain ⟨q, rfl⟩ := hφ.1.surjective s
    exact ⟨q, (futureLightConeBoundary_mem_iff_of_chronoCausalAut hφ p q).mp hs, rfl⟩

end Lorentz.Vector

/- ZIL-BEGIN -/

open Zil
open Lorentz.Vector

zil attach futureLightConeBoundary_iff where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-null-future-cone-is-order-definable-a-point-is-on-the-future-\
light-cone-boundary-iff-it-is-causally-but-not-chronologically-reachable"

zil attach futureLightConeBoundary_image_of_chronoCausalAut where
  supported_by @ "lean:Lorentz.Vector.futureLightConeBoundary_mem_iff_of_chronoCausalAut",
  formalizes @ "claim:a-chrono-causal-automorphism-preserves-the-null-cone-mapping-light-\
rays-to-light-rays-zeemans-light-ray-preservation",
  supported_by @ "lean:Lorentz.Vector.futureLightConeBoundary_iff"

zil attach futureLightConeBoundary_iff_causalDiamond_isChain where
  supported_by @ "lean:Lorentz.Vector.causalDiamond_isChain_of_futureNull",
  supported_by @ "lean:Lorentz.Vector.causalDiamond_not_isChain_of_futureTimelike",
  formalizes @ "claim:in-three-plus-one-minkowski-space-future-null-separation-is-definable-\
from-the-causal-order-alone-as-causal-reachability-with-a-chain-alexandrov-interval",
  supported_by @ "lean:Lorentz.Vector.causalDiamond_isChain_of_futureNull",
  supported_by @ "lean:Lorentz.Vector.causalDiamond_not_isChain_of_futureTimelike"

zil attach interiorFutureLightCone_iff_causalDiamond_not_isChain where
  supported_by @ "lean:Lorentz.Vector.causalDiamond_isChain_of_futureNull",
  supported_by @ "lean:Lorentz.Vector.causalDiamond_not_isChain_of_futureTimelike",
  formalizes @ "claim:in-three-plus-one-minkowski-space-chronological-timelike-reachability-\
is-definable-from-causal-order-alone-as-causal-reachability-with-a-non-chain-alexandrov-\
interval",
  supported_by @ "lean:Lorentz.Vector.futureLightConeBoundary_iff_causalDiamond_isChain"

zil attach interiorFutureLightCone_mem_iff_of_causalAutomorphism where
  supported_by @ "lean:interiorFutureLightCone_iff_causalDiamond_not_isChain",
  supported_by @ "lean:Lorentz.Vector.IsCausalAutomorphism",
  formalizes @ "claim:every-bare-causal-automorphism-of-three-plus-one-minkowski-space-\
preserves-chronological-timelike-reachability-without-an-extra-chronology-or-continuity-\
premise",
  supported_by @ "lean:Lorentz.Vector.interiorFutureLightCone_iff_causalDiamond_not_isChain"

zil attach isOpen_chronologicalDiamond3 where
  supported_by @ "lean:Lorentz.Vector.isOpen_interiorFutureLightCone3",
  formalizes @ "claim:open-chronological-alexandrov-diamonds-are-open-in-the-euclidean-\
topology-of-three-plus-one-minkowski-space",
  supported_by @ "lean:Lorentz.Vector.isOpen_interiorFutureLightCone3"

zil attach chronologicalDiamond3_image_of_causalAutomorphism where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete",
  supported_by @ "lean:interiorFutureLightCone_mem_iff_of_causalAutomorphism",
  formalizes @ "claim:every-causal-automorphism-of-three-plus-one-minkowski-space-maps-each-\
open-chronological-diamond-exactly-onto-the-diamond-between-the-image-endpoints",
  supported_by @ "lean:Lorentz.Vector.interiorFutureLightCone_mem_iff_of_causalAutomorphism",
  caveat @ "claim:the-separate-proof-that-chronological-diamonds-form-a-basis-for-the-\
entire-euclidean-topology-is-not-asserted-by-this-image-theorem"

zil attach futureLightConeBoundary_image_of_causalAutomorphism where
  supported_by @ "lean:Lorentz.Vector.IsCausalAutomorphism",
  formalizes @ "claim:every-causal-automorphism-of-three-plus-one-minkowski-space-preserves-\
complete-future-null-cones-and-therefore-light-rays-without-a-chronological-or-continuity-\
premise",
  supported_by @ "lean:Lorentz.Vector.futureLightConeBoundary_iff_causalDiamond_isChain",
  supported_by @ "lean:Lorentz.Vector.causalDiamondIsChain_iff_of_causalAutomorphism",
  caveat @ "claim:light-ray-preservation-is-not-by-itself-the-fundamental-affine-geometry-\
collineation-theorem"

zil attach futureNullRay_image_of_causalAutomorphism where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CompleteComplexEinsteinFieldEquations.CompleteComplexEinsteinFieldEquation.complete",
  supported_by @ "lean:Lorentz.Vector.IsCausalAutomorphism",
  formalizes @ "claim:every-causal-automorphism-of-three-plus-one-minkowski-space-maps-each-\
individual-nondegenerate-future-null-affine-ray-onto-the-null-ray-through-the-corresponding-\
image-points",
  supported_by @ "lean:Lorentz.Vector.futureLightConeBoundary_mem_iff_of_causalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.futureNullRay",
  caveat @ "claim:this-is-the-null-line-incidence-input-to-the-affine-geometry-reduction-\
not-the-collineation-to-affine-equivalence-theorem-itself"

zil attach nullAffineLine_image_of_causalAutomorphism where
  formalizes @ "claim:every-causal-automorphism-of-three-plus-one-minkowski-space-maps-each-\
complete-nondegenerate-null-affine-line-onto-the-affine-line-through-the-corresponding-\
image-points",
  supported_by @ "lean:Lorentz.Vector.futureNullRay_image_of_causalAutomorphism",
  supported_by @ "lean:Lorentz.Vector.futureLightConeBoundary_mem_iff_of_causalAutomorphism",
  caveat @ "claim:this-proves-the-null-line-collineation-datum-but-the-separate-fundamental-\
theorem-must-still-promote-the-induced-affine-incidence-map-to-an-affine-equivalence"

zil attach translation_isChronoCausalAutomorphism where
  formalizes @ "claim:spatial-translations-are-chrono-causal-automorphisms-since-both-the-\
causal-and-chronological-relations-depend-only-on-the-event-difference"

zil attach IsCausalAutomorphism.toChronoCausalAutomorphism where
  formalizes @ "claim:in-physical-three-plus-one-dimensions-every-causal-automorphism-is-\
automatically-a-chrono-causal-automorphism"

zil_file_contract physlib.causalConeLightRayPreservation where
  promises "Zeeman light-ray preservation is proved from the causal order alone in physical \
3+1 Minkowski space. A future-null Alexandrov interval is exactly a causally reachable \
interval that is a chain: null intervals are chains by the equality case of closed-cone \
reverse Cauchy-Schwarz, while every timelike interval contains an explicitly constructed \
spacelike-incomparable pair. Its complement inside the causal order gives chronological \
timelike reachability, proving that every bare causal automorphism is automatically \
chrono-causal in 3+1 dimensions. Open chronological diamonds are proved Euclidean-open and \
are mapped exactly to image diamonds. The chain property is invariant under causal \
automorphisms, so every bare causal automorphism preserves the complete future null cone, \
without continuity assumptions. This is strengthened first to exact setwise preservation \
of each individual nondegenerate future null affine ray and then to exact preservation of \
every complete null affine line, providing the null-line collineation datum for the \
fundamental affine-geometry step. The dimension-polymorphic chrono-causal description and \
translation witness are retained as complementary adapters."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Lorentz.Vector.futureLightConeBoundary",
    "lean:Lorentz.Vector.interiorFutureLightCone",
    "lean:Lorentz.Vector.causallyFollows",
    "lean:Lorentz.Vector.causalDiamond",
    "lean:Lorentz.Vector.IsFutureCausal"
  ]
  forbids_substitutes [
    "reading the proved 3+1 causal-chain characterization as a dimension-polymorphic result",
    "reading light-ray preservation as the fundamental affine-geometry collineation theorem"
  ]
  witnessed_by [
    futureLightConeBoundary_iff,
    causalDiamond_isChain_of_futureNull,
    causalDiamond_not_isChain_of_futureTimelike,
    futureLightConeBoundary_iff_causalDiamond_isChain,
    interiorFutureLightCone_iff_causalDiamond_not_isChain,
    causalDiamondIsChain_iff_of_causalAutomorphism,
    futureLightConeBoundary_mem_iff_of_causalAutomorphism,
    interiorFutureLightCone_mem_iff_of_causalAutomorphism,
    isOpen_interiorFutureLightCone3,
    isOpen_chronologicalDiamond3,
    chronologicalDiamond3_image_of_causalAutomorphism,
    futureLightConeBoundary_image_of_causalAutomorphism,
    futureNullRay_image_of_causalAutomorphism,
    nullAffineLine_image_of_causalAutomorphism,
    IsCausalAutomorphism.toChronoCausalAutomorphism,
    translation_isChronoCausalAutomorphism,
    futureLightConeBoundary_mem_iff_of_chronoCausalAut,
    futureLightConeBoundary_image_of_chronoCausalAut
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.causalConeLightRayPreservation
