/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Physlib.Mathematics.DimensionalScalingFunctorTower
public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussHolographicReduction
public import Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere

/-!
# The vector Banach–Stone theorem at critical distortion `√2`

Formalizes the geometric mechanism of E. M. Galego, A. L. Porto da Silva, *A vector-valued
Banach–Stone theorem with distortion `√2`* (Pacific J. Math. 290, 2017): if `T` is an
isomorphism of `C₀(K,H)` onto `C₀(S,H)` — `H` a real Hilbert space of finite dimension
`≥ 2` — with `‖f‖/M ≤ ‖Tf‖ ≤ M‖f‖` at `M = 2^{1/4}` (distortion `‖T‖‖T⁻¹‖ = √2`), then
`K` and `S` are homeomorphic.  The exact steps:

* `omega_scaling` — the homogeneity of the modulus `ω(k,f,v) = max{‖f‖, ‖f(k)−v‖}` under
  simultaneous scaling (the engine of Proposition 2.1 (2), `Γ_w(k,v) = Γ_{tw}(k,tv)`).
* `inner_ge_of_dist_le`, `orthogonal_of_critical_distortion` — **Proposition 2.1 (3)**, the
  heart of the paper: two witness vectors of norm `1/M` whose difference *and* sum both stay
  within `M` are **orthogonal**, by the law of cosines — and the bound
  `⟨w,w'⟩ ≥ ½(2/M² − M²)` closes to `0` exactly when `M⁴ = 2`.
* `critical_distortion_iff` — the threshold characterization: `2/M² = M²` **iff** `M⁴ = 2`
  — why `√2` is the largest distortion the method reaches (and, per the paper's
  introduction, the largest for which any vector-valued Banach–Stone theorem is known).
* `quarticRootTwo_pow_four` — `M = 2^{1/4}` realizes the threshold.

**The holographic/fiber-sphere links** (mechanical, on the existing carriers):

* `critical_distortion_eq_scalingFactor_two` — the critical distortion is the `D = 2` rung
  of the dimensional-scaling tower: `M² = √2 = scalingFactor 2`
  (`Mathematics.DimensionalScaling`) — the two-dimensionality of the law-of-cosines plane
  spanned by the witness pair appears as the scaling factor of the two-dimensional mapping.
* `banachStone_sandwich_JLBound` — the Banach–Stone norm sandwich at critical distortion
  *is* a Johnson–Lindenstrauss distortion bound with `ε = √2 − 1`
  (`AdSCFT.JohnsonLindenstraussHolographicReduction.JLBound`): the isomorphism distorts
  norms exactly as a holographic dimensional reduction distorts distances.
* `dualSphere_orthogonal_chord`, `dualSphere_basis_chord` — the threshold configuration —
  orthogonal unit vectors at chord `√2` — realized on the dual-sphere carrier
  (`Hopf.DualSphereFiberDecomposition.sphereInner`): the chord-squared between orthogonal
  fiber directions is `2 = (scalingFactor 2)²`, exhibited concretely on the first two
  coordinate directions.

**Honest layering.**  Exact inner-product, `max`, and power algebra.  The `C₀(K,H)` spaces,
Urysohn functions, the `Γ`-set combinatorics (Proposition 2.1 (1), (4)), the construction
of the homeomorphism from the orthogonality dichotomy (§§3–5 there), and the
counterexample showing the theorem fails for infinite-dimensional `H` (an isometry pair
with `‖ΥTΘ‖ = √2`, `‖(ΥTΘ)⁻¹‖ = 1` between non-homeomorphic discrete spaces) are
recorded, not re-derived.

## References

* E. M. Galego, A. L. Porto da Silva, Pacific J. Math. **290** (2017) 321–332; M. Cambern
  (1976); H. B. Cohen (1975).  Carriers: `Mathematics.DimensionalScaling`,
  `Hopf.DualSphereFiberDecomposition`, `AdSCFT.JohnsonLindenstraussHolographicReduction`.
-/

set_option autoImplicit false

open Physlib.Mathematics.DimensionalScaling
open Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereFiberDecomposition
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussHolographicReduction

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.VectorBanachStoneDistortion

/-! ## §A — the Galego–Porto da Silva mechanism -/

/-- **The modulus is homogeneous** (the engine of Proposition 2.1 (2)): the quantity
`ω(k,f,v) = max{‖f‖, ‖f(k)−v‖}` scales by `|t|` when the function and the witness vector
scale by `t` — so the witness sets satisfy `Γ_w(k,v) = Γ_{tw}(k,tv)`. -/
theorem omega_scaling (a b t : ℝ) :
    max (|t| * a) (|t| * b) = |t| * max a b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h (abs_nonneg t))]
  · rw [max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h (abs_nonneg t))]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The law-of-cosines bound** (Proposition 2.1 (3), first half): witness vectors of norm
`1/M` whose difference stays within `M` have inner product at least `½(2/M² − M²)`. -/
theorem inner_ge_of_dist_le (w w' : H) (M : ℝ) (hM : 0 < M)
    (hw : ‖w‖ = 1/M) (hw' : ‖w'‖ = 1/M) (hsub : ‖w - w'‖ ≤ M) :
    (1/2) * (2/M^2 - M^2) ≤ inner ℝ w w' := by
  have hexp : ‖w - w'‖^2 = ‖w‖^2 - 2 * inner ℝ w w' + ‖w'‖^2 :=
    norm_sub_sq_real w w'
  have hsq : ‖w - w'‖^2 ≤ M^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsub 2
  rw [hw, hw'] at hexp
  have h1M : (1/M)^2 = 1/M^2 := by
    field_simp
  rw [h1M] at hexp
  have h2M : 2/M^2 = 1/M^2 + 1/M^2 := by ring
  linarith [hexp, hsq]

/-- **Orthogonality at the critical distortion** (Proposition 2.1 (3)): at `M⁴ = 2` two
witness vectors of norm `1/M` whose difference and sum both stay within `M` are orthogonal
— the law-of-cosines bound closes to zero from both sides exactly at the threshold. -/
theorem orthogonal_of_critical_distortion (w w' : H) (M : ℝ) (hM : 0 < M)
    (hM4 : M^4 = 2) (hw : ‖w‖ = 1/M) (hw' : ‖w'‖ = 1/M)
    (hsub : ‖w - w'‖ ≤ M) (hadd : ‖w + w'‖ ≤ M) :
    inner ℝ w w' = 0 := by
  have hcrit : 2/M^2 - M^2 = 0 := by
    field_simp
    linarith
  have hge : (0:ℝ) ≤ inner ℝ w w' := by
    have hinner := inner_ge_of_dist_le w w' M hM hw hw' hsub
    rw [hcrit] at hinner
    linarith
  have hle : inner ℝ w w' ≤ 0 := by
    have hw'' : ‖-w'‖ = 1/M := by rwa [norm_neg]
    have hsub' : ‖w - (-w')‖ ≤ M := by rwa [sub_neg_eq_add]
    have hinner := inner_ge_of_dist_le w (-w') M hM hw hw'' hsub'
    rw [hcrit, inner_neg_right] at hinner
    linarith
  linarith

/-- **The threshold characterization**: the law-of-cosines bound closes to zero, `2/M² = M²`,
exactly when `M⁴ = 2` — the reason `√2 = M²` is the critical distortion. -/
theorem critical_distortion_iff (M : ℝ) (hM : 0 < M) :
    2/M^2 = M^2 ↔ M^4 = 2 := by
  rw [div_eq_iff (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- `M = 2^{1/4}` realizes the critical distortion: `(2^{1/4})⁴ = 2`. -/
theorem quarticRootTwo_pow_four : ((2:ℝ) ^ ((1:ℝ)/4))^4 = 2 := by
  rw [← Real.rpow_natCast ((2:ℝ) ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-! ## §B — the holographic and fiber-sphere links -/

/-- **The critical distortion is the `D = 2` scaling factor**: `M² = √2 = scalingFactor 2` —
the two-dimensional rung of the dimensional-scaling tower, matching the two-dimensionality
of the law-of-cosines plane spanned by the witness pair. -/
theorem critical_distortion_eq_scalingFactor_two (M : ℝ) (hM : 0 < M) (hM4 : M^4 = 2) :
    M^2 = scalingFactor 2 := by
  have hs := scalingFactor_sq 2
  have hfac : (M^2 - scalingFactor 2) * (M^2 + scalingFactor 2) = 0 := by
    linear_combination hM4 - hs
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · exfalso
    have h1 : 0 < M^2 := by positivity
    have h2 : 0 < scalingFactor 2 := scalingFactor_pos (by norm_num)
    linarith

/-- **The Banach–Stone sandwich is a Johnson–Lindenstrauss bound**: at the critical
distortion `M⁴ = 2`, the two-sided norm estimate `d/M ≤ d' ≤ M·d` of the isomorphism is
exactly a `JLBound` with distortion parameter `ε = √2 − 1` — the Banach–Stone isomorphism
distorts norms as a holographic dimensional reduction distorts distances. -/
theorem banachStone_sandwich_JLBound (M d dk : ℝ) (hM : 0 < M) (hM4 : M^4 = 2)
    (hd : 0 ≤ d) (hdk : 0 ≤ dk) (hlow : d/M ≤ dk) (hup : dk ≤ M * d) :
    JLBound (Real.sqrt 2 - 1) d dk := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hM2 : M^2 = Real.sqrt 2 := by
    have hcritical := critical_distortion_eq_scalingFactor_two M hM hM4
    rwa [scalingFactor, Nat.cast_ofNat] at hcritical
  have h1 : (d/M)^2 ≤ dk^2 := pow_le_pow_left₀ (by positivity) hlow 2
  have h2 : dk^2 ≤ (M*d)^2 := pow_le_pow_left₀ hdk hup 2
  have hdM : (d/M)^2 = d^2/M^2 := by
    field_simp
  constructor
  · -- (1 − (√2 − 1))·d² = (2 − √2)·d² ≤ d²/√2 ≤ dk², since (2−√2)·√2 = 2√2 − 2 ≤ 1·…
    rw [hdM, hM2] at h1
    have hkey : (2 - Real.sqrt 2) * Real.sqrt 2 ≤ 1 := by nlinarith
    have hd2 : (0:ℝ) ≤ d^2 := sq_nonneg d
    have hs2pos : 0 < Real.sqrt 2 := by nlinarith
    rw [div_le_iff₀ hs2pos] at h1
    nlinarith [h1, hd2]
  · rw [mul_pow, hM2] at h2
    nlinarith [h2, sq_nonneg d]

/-- **The threshold chord on the dual sphere**: orthogonal unit vectors of the dual-sphere
carrier are at chord-squared `2 = (scalingFactor 2)²` — the critical-distortion
configuration realized on the fiber-sphere geometry. -/
theorem dualSphere_orthogonal_chord (ξ η : Fin 3 → ℝ)
    (hξ : sphereNormSq ξ = 1) (hη : sphereNormSq η = 1) (hor : sphereInner ξ η = 0) :
    sphereNormSq (fun i => ξ i - η i) = scalingFactor 2 ^ 2 := by
  rw [scalingFactor_sq]
  unfold sphereNormSq sphereInner at *
  push_cast
  nlinarith [hξ, hη, hor]

/-- The threshold pair exhibited concretely: the first two coordinate directions of the
dual sphere are orthogonal unit vectors, hence sit at the critical chord. -/
theorem dualSphere_basis_chord :
    sphereNormSq (fun i => (if i = 0 then (1:ℝ) else 0) - (if i = 1 then 1 else 0))
      = scalingFactor 2 ^ 2 := by
  apply dualSphere_orthogonal_chord
  · simp [sphereNormSq, sphereInner]
  · simp [sphereNormSq, sphereInner]
  · simp [sphereInner]

/-! ## §C — the Tsirelson bound and the Coxeter ladder -/

/-- **The CHSH correlation value in vector form**: for measurement directions
`a₀, a₁, b₀, b₁`, the combination `⟨a₀,b₀⟩ + ⟨a₁,b₀⟩ + ⟨a₀,b₁⟩ − ⟨a₁,b₁⟩`. -/
noncomputable def chshVector (a₀ a₁ b₀ b₁ : H) : ℝ :=
  inner ℝ a₀ b₀ + inner ℝ a₁ b₀ + inner ℝ a₀ b₁ - inner ℝ a₁ b₁

/-- **The Tsirelson bound, vector form**: for unit vectors the CHSH value is at most
`2√2` — Cauchy–Schwarz after regrouping `⟨a₀+a₁,b₀⟩ + ⟨a₀−a₁,b₁⟩`, then the
parallelogram law `‖a₀+a₁‖² + ‖a₀−a₁‖² = 4`. -/
theorem chshVector_le_tsirelson (a₀ a₁ b₀ b₁ : H)
    (ha₀ : ‖a₀‖ = 1) (ha₁ : ‖a₁‖ = 1) (hb₀ : ‖b₀‖ = 1) (hb₁ : ‖b₁‖ = 1) :
    chshVector a₀ a₁ b₀ b₁ ≤ 2 * Real.sqrt 2 := by
  have hregroup : chshVector a₀ a₁ b₀ b₁
      = inner ℝ (a₀ + a₁) b₀ + inner ℝ (a₀ - a₁) b₁ := by
    unfold chshVector
    rw [inner_add_left, inner_sub_left]
    ring
  have hcs₀ : inner ℝ (a₀ + a₁) b₀ ≤ ‖a₀ + a₁‖ := by
    calc inner ℝ (a₀ + a₁) b₀ ≤ ‖a₀ + a₁‖ * ‖b₀‖ := real_inner_le_norm _ _
      _ = ‖a₀ + a₁‖ := by rw [hb₀, mul_one]
  have hcs₁ : inner ℝ (a₀ - a₁) b₁ ≤ ‖a₀ - a₁‖ := by
    calc inner ℝ (a₀ - a₁) b₁ ≤ ‖a₀ - a₁‖ * ‖b₁‖ := real_inner_le_norm _ _
      _ = ‖a₀ - a₁‖ := by rw [hb₁, mul_one]
  have hpar : ‖a₀ + a₁‖^2 + ‖a₀ - a₁‖^2 = 4 := by
    rw [norm_add_sq_real, norm_sub_sq_real, ha₀, ha₁]
    ring
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsum : ‖a₀ + a₁‖ + ‖a₀ - a₁‖ ≤ 2 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (‖a₀ + a₁‖ - ‖a₀ - a₁‖), norm_nonneg (a₀ + a₁),
      norm_nonneg (a₀ - a₁), sq_nonneg (‖a₀ + a₁‖ + ‖a₀ - a₁‖ - 2*Real.sqrt 2)]
  rw [hregroup]
  linarith

/-- **Saturating the Tsirelson bound forces orthogonal measurement pairs** — the same
orthogonality dichotomy as the critical Banach–Stone distortion: if unit vectors attain
`chshVector = 2√2`, then `a₀ ⊥ a₁`.  Equality in the quadratic-mean step forces
`‖a₀+a₁‖ = ‖a₀−a₁‖`, and the polarization identity turns that into `⟨a₀,a₁⟩ = 0`. -/
theorem chshVector_saturation_orthogonal (a₀ a₁ b₀ b₁ : H)
    (ha₀ : ‖a₀‖ = 1) (ha₁ : ‖a₁‖ = 1) (hb₀ : ‖b₀‖ = 1) (hb₁ : ‖b₁‖ = 1)
    (hmax : chshVector a₀ a₁ b₀ b₁ = 2 * Real.sqrt 2) :
    inner ℝ a₀ a₁ = 0 := by
  have hregroup : chshVector a₀ a₁ b₀ b₁
      = inner ℝ (a₀ + a₁) b₀ + inner ℝ (a₀ - a₁) b₁ := by
    unfold chshVector
    rw [inner_add_left, inner_sub_left]
    ring
  have hcs₀ : inner ℝ (a₀ + a₁) b₀ ≤ ‖a₀ + a₁‖ := by
    calc inner ℝ (a₀ + a₁) b₀ ≤ ‖a₀ + a₁‖ * ‖b₀‖ := real_inner_le_norm _ _
      _ = ‖a₀ + a₁‖ := by rw [hb₀, mul_one]
  have hcs₁ : inner ℝ (a₀ - a₁) b₁ ≤ ‖a₀ - a₁‖ := by
    calc inner ℝ (a₀ - a₁) b₁ ≤ ‖a₀ - a₁‖ * ‖b₁‖ := real_inner_le_norm _ _
      _ = ‖a₀ - a₁‖ := by rw [hb₁, mul_one]
  have hpar : ‖a₀ + a₁‖^2 + ‖a₀ - a₁‖^2 = 4 := by
    rw [norm_add_sq_real, norm_sub_sq_real, ha₀, ha₁]
    ring
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hge : 2 * Real.sqrt 2 ≤ ‖a₀ + a₁‖ + ‖a₀ - a₁‖ := by
    rw [hregroup] at hmax
    linarith
  have h8 : 8 ≤ (‖a₀ + a₁‖ + ‖a₀ - a₁‖)^2 := by
    have h2s : (0:ℝ) ≤ 2*Real.sqrt 2 := by positivity
    have hmul := mul_le_mul hge hge h2s (le_trans h2s hge)
    nlinarith [hmul, hs2]
  have heq : ‖a₀ + a₁‖ = ‖a₀ - a₁‖ := by
    nlinarith [h8, hpar, sq_nonneg (‖a₀ + a₁‖ - ‖a₀ - a₁‖)]
  have heqnorm : ‖a₀ + a₁‖^2 = ‖a₀ - a₁‖^2 := by
    rw [heq]
  have hpolar : ‖a₀ + a₁‖^2 - ‖a₀ - a₁‖^2 = 4 * inner ℝ a₀ a₁ := by
    rw [norm_add_sq_real, norm_sub_sq_real]
    ring
  rw [heqnorm] at hpolar
  linarith

/-- **The Tsirelson bound is twice the critical Banach–Stone distortion**:
`2√2 = 2·M²` at `M⁴ = 2` — the two inner-product extremal problems share their threshold
constant, and both are saturated exactly on orthogonal pairs. -/
theorem tsirelson_eq_two_mul_critical_distortion (M : ℝ) (hM : 0 < M) (hM4 : M^4 = 2) :
    2 * Real.sqrt 2 = 2 * M^2 := by
  have h := critical_distortion_eq_scalingFactor_two M hM hM4
  rw [h, scalingFactor, Nat.cast_ofNat]

/-- **The critical distortion is the `n = 4` rung of the Coxeter ladder** `2cos(π/n)`:
`M² = √2 = 2cos(π/4)`. -/
theorem critical_distortion_eq_two_cos_pi_div_four (M : ℝ) (hM : 0 < M) (hM4 : M^4 = 2) :
    M^2 = 2 * Real.cos (Real.pi/4) := by
  rw [Real.cos_pi_div_four, critical_distortion_eq_scalingFactor_two M hM hM4,
    scalingFactor, Nat.cast_ofNat]
  ring

/-- **The critical distortion sits one rung below the icosahedral golden rung** on the
Coxeter ladder `2cos(π/n)`: `M² = 2cos(π/4) < 2cos(π/5) = φ`
(`IcosahedralPoincareSphere.two_cos_pi_div_five_eq_goldenRatio`) — the `n = 4`
(square) and `n = 5` (pentagon/icosahedral, the Poincaré-sphere symmetry) rungs of the
same algebraic-angle ladder, strictly ordered by the monotonicity of the cosine. -/
theorem critical_distortion_lt_goldenRatio (M : ℝ) (hM : 0 < M) (hM4 : M^4 = 2) :
    M^2 < Real.goldenRatio := by
  rw [← IcosahedralPoincareSphere.two_cos_pi_div_five_eq_goldenRatio,
    critical_distortion_eq_two_cos_pi_div_four M hM hM4]
  have hcos : Real.cos (Real.pi/4) < Real.cos (Real.pi/5) := by
    apply Real.strictAntiOn_cos
    · constructor
      · positivity
      · linarith [Real.pi_pos]
    · constructor
      · positivity
      · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  linarith

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.VectorBanachStoneDistortion

end
