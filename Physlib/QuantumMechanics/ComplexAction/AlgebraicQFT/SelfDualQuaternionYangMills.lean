/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator
public import Mathlib.Algebra.Quaternion

/-!
# Self-dual/anti-self-dual splitting and the quaternionic `SU(2)`

Connects the configuration-space Dirac arc (Aastrup–Grimstrup arXiv:2501.00005,
`ConfigurationSpaceDiracFluctuation`/`GaugeGeometry`/`DiracOperator`) to the 4D
Yang–Mills structure trio: the Hodge decomposition `∧²ℝ⁴ = ∧²₊ ⊕ ∧²₋`, the
quaternionic `S³ ≅ SU(2)`, and the non-abelian three-vertex. The paper's own §4.1
notes that the *untwisted* Chern–Simons fluctuation squares to the **self-dual and
anti-self-dual sectors** of Yang–Mills (its refs [15,16]); this module proves the
algebra those sectors rest on.

## §A — the Hodge `±` split and the instanton criterion

For an involutive self-adjoint operator `★` (the Hodge star on `∧²ℝ⁴`, where
`★² = 1` and the eigenspaces `∧²₊, ∧²₋` are 3-dimensional):

* `projSelfDual`/`projAntiSelfDual` — `P± = ½(1 ± ★)`, with `P₊ + P₋ = 1`
  (`proj_add_eq`) and eigenvector property `★P±ω = ±P±ω` (`hodgeStar_projSelfDual`,
  `hodgeStar_projAntiSelfDual`).
* `proj_inner_zero`, `crossTerm_split` — the **4D cross-term split**:
  `⟪P₊ω, P₋ω⟫ = 0` and `‖ω‖² = ‖P₊ω‖² + ‖P₋ω‖²` — the `|ξ∧η|² = |·|₊² + |·|₋²`
  decomposition of the 4D defect functional.
* `antiSelfDual_iff_sdProj_zero`, `antiSelfDual_iff_norm_concentrates` — **the
  instanton criterion**: `★F = −F ⟺ P₊F = 0 ⟺ ‖F‖² = ‖P₋F‖²` — the curvature
  is an anti-self-dual instanton exactly when the self-dual defect term vanishes
  and the norm concentrates in the ASD sector (the `F_ASD = 0 ⟺` defect-term`= 0`
  line; Donaldson's classification of the resulting moduli is the analytic layer).
* `inner_hodgeStar_eq_selfDual_sub_antiSelfDual`, `abs_inner_hodgeStar_le_norm_sq`,
  `abs_inner_hodgeStar_eq_norm_sq_iff_selfDual_or_antiSelfDual` — **the topological
  energy bound**: the pairing `⟪ω, ★ω⟫` (the curvature integral reading off a
  characteristic number) satisfies `⟪ω, ★ω⟫ = ‖P₊ω‖² − ‖P₋ω‖²` and hence
  `|⟪ω, ★ω⟫| ≤ ‖ω‖²`, with equality iff `ω` is self-dual or anti-self-dual. This is
  Donaldson's statement (1985 §Introduction, p. 4) that the absolute minimum of the
  Yang–Mills functional at fixed topological type is attained by an (anti-)self-dual
  connection.

## §B — the non-abelian three-vertex on the `𝔰𝔲(2)` carriers

* `leviCivita3_swap` — `ε^{bac} = −ε^{abc}`.
* `pauliVec_commutator` — `[σᵃ, σᵇ] = 2i·ε^{abc}σᶜ`: the `𝔰𝔲(2)` structure
  constants, i.e. **the three-vertex** — the trilinear coupling every non-abelian
  gauge boson shares (the same `ε` for the weak `SU(2)` as for the gluon's
  `𝔰𝔲(2) ⊂ 𝔰𝔲(3)` subalgebras) and the photon lacks.
* `threeVertex_trace` — `Tr([σᵃ,σᵇ]σᶜ) = 4i·ε^{abc}`: the vertex measured by the
  embedding trace form is the *same* `ε` as in the Eq. 9→10 conversion
  (`pauliVec_trace_triple`).

**The two "threes" are different structures** (and the formalization keeps them
apart): the vertex-three here is `dim 𝔰𝔲(2) = 3` — the adjoint/Lie-bracket three,
*additive* channel structure `ε^{abc}` — while a ℤ/3 (center/triality,
*multiplicative* `ω³ = 1`) three does not exist for `SU(2)`: its center is
`ℤ₂ = {±1}`, visible below as the central `−1 = rep(q)² ` for imaginary unit
quaternions (`quaternionRep_imaginaryUnit_sq`). The two threes coincide numerically
for color only because `N = 3` there.

## §C — the quaternionic `S³ ≅ SU(2)`

The box's fiber `ξ, η ∈ S³ ≅ SU(2) ≅ ℍ₁`, as the concrete representation
`ℍ → M₂(ℂ)`:

* `quaternionRep` — `q = a + bi + cj + dk ↦ a·1 + b(−iσ₁) + c(−iσ₂) + d(−iσ₃)`,
  multiplicative (`quaternionRep_mul`) and unital (`quaternionRep_one`) — an algebra
  representation.
* `quaternionRep_imaginaryUnits` — the imaginary units land exactly on the
  `𝔰𝔲(2)` Pauli generators `−iσᵃ` of the spin embedding
  (`su2Basis_embeddingMetric`), welding `ℍ` to the configuration-space carriers.
* `quaternionRep_star`, `quaternionRep_det` — `rep(q̄) = rep(q)ᴴ` and
  `det(rep q) = |q|²`.
* `unitQuaternion_mem_SU2` — **`S³ lands in `SU(2)`**: `|q|² = 1` gives
  `rep(q)ᴴ·rep(q) = 1` and `det = 1` — the `S³ ≅ SU(2)` of the fiber, and the
  gauge group of the configuration space `𝒜` whose Dirac operator the arc
  fluctuates.

## Honest scope

The Hodge star is treated as an abstract involutive self-adjoint operator (its
concrete realization on `∧²ℝ⁴` with `dim ∧²± = 3` is `HodgeStarBivector.hodgeStar2`; the
wedge `ξ∧η` of one-forms and the NS-defect functional `Ξ_ds⁴` with its `λ±` weights and
enstrophy scaling live in the Navier–Stokes repositories' analytic layer). At this
abstract level the **topological energy bound** of Donaldson's variational theory is
formalized (`abs_inner_hodgeStar_le_norm_sq`); the moduli-space and Hermitian–Einstein
existence theory that rests on it is cited, not formalized.

## References

* J. Aastrup, J. M. Grimstrup, arXiv:2501.00005 §4.1 ([15] arXiv:2410.07290,
  [16] arXiv:2410.03699 — the untwisted fluctuation's SD/ASD sectors);
  S. K. Donaldson, J. Diff. Geom. 18 (1983) 279; and *Anti self-dual Yang–Mills
  connections over complex algebraic surfaces and stable vector bundles*, Proc. London
  Math. Soc. (3) 50 (1985) 1–26 (p. 4, the SD/ASD decomposition of the Yang–Mills
  functional and its topological lower bound).
* Carriers: `AlgebraicQFT.ConfigurationSpaceGaugeGeometry` (`pauliVec`,
  `leviCivita3`, `pauliVec_trace_triple`), `Hopf.QuaternionIsoclinicHopfFibration`
  (the quaternionic Hopf layer this representation feeds).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceGaugeGeometry
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator
open Physlib.QuantumMechanics.SpinDensityFunctionalOperators
open Physlib.QuantumMechanics.ComplexAction.DissipativeNambuLorenz.LorenzLorentzSO3

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SelfDualQuaternionYangMills

/-! ## §A — the Hodge `±` split -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The self-dual projection `P₊ = ½(1 + ★)`. -/
noncomputable def projSelfDual (s : V →ₗ[ℝ] V) (ω : V) : V := (1/2 : ℝ) • (ω + s ω)

/-- The anti-self-dual projection `P₋ = ½(1 − ★)`. -/
noncomputable def projAntiSelfDual (s : V →ₗ[ℝ] V) (ω : V) : V := (1/2 : ℝ) • (ω - s ω)

/-- `P₊ + P₋ = 1` — every 2-form splits into its self-dual and anti-self-dual
parts. -/
theorem proj_add_eq (s : V →ₗ[ℝ] V) (ω : V) :
    projSelfDual s ω + projAntiSelfDual s ω = ω := by
  unfold projSelfDual projAntiSelfDual
  module

/-- `★P₊ω = P₊ω` — the self-dual part is the `+1` eigenvector of the Hodge star. -/
theorem hodgeStar_projSelfDual {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω) (ω : V) :
    s (projSelfDual s ω) = projSelfDual s ω := by
  unfold projSelfDual
  rw [map_smul, map_add, hinv, add_comm]

/-- `★P₋ω = −P₋ω` — the anti-self-dual part is the `−1` eigenvector. -/
theorem hodgeStar_projAntiSelfDual {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω) (ω : V) :
    s (projAntiSelfDual s ω) = -projAntiSelfDual s ω := by
  unfold projAntiSelfDual
  rw [map_smul, map_sub, hinv, ← smul_neg, neg_sub]

/-- The two sectors are orthogonal: `⟪P₊ω, P₋ω⟫ = 0` (for a self-adjoint star). -/
theorem proj_inner_zero {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω)
    (hsym : ∀ x y, inner ℝ (s x) y = inner ℝ x (s y)) (ω : V) :
    inner ℝ (projSelfDual s ω) (projAntiSelfDual s ω) = (0 : ℝ) := by
  have hss : inner ℝ (s ω) (s ω) = inner ℝ ω ω := by rw [hsym, hinv]
  have hc : inner ℝ (s ω) ω = inner ℝ ω (s ω) := real_inner_comm _ _
  unfold projSelfDual projAntiSelfDual
  rw [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_sub_right,
    inner_sub_right]
  rw [hss] at *
  linarith [hc]

/-- **The 4D cross-term split**: `‖ω‖² = ‖P₊ω‖² + ‖P₋ω‖²` — the
`|ξ∧η|² = |proj₊(ξ∧η)|² + |proj₋(ξ∧η)|²` decomposition entering the 4D defect
functional. -/
theorem crossTerm_split {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω)
    (hsym : ∀ x y, inner ℝ (s x) y = inner ℝ x (s y)) (ω : V) :
    ‖ω‖ ^ 2 = ‖projSelfDual s ω‖ ^ 2 + ‖projAntiSelfDual s ω‖ ^ 2 := by
  have h := norm_add_sq_real (projSelfDual s ω) (projAntiSelfDual s ω)
  rw [proj_add_eq] at h
  rw [h, proj_inner_zero hinv hsym]
  ring

/-- **The anti-self-dual criterion, projection form**: `★F = −F ⟺ P₊F = 0` — the
curvature is an ASD instanton exactly when its self-dual part vanishes. -/
theorem antiSelfDual_iff_sdProj_zero (s : V →ₗ[ℝ] V) (ω : V) :
    s ω = -ω ↔ projSelfDual s ω = 0 := by
  unfold projSelfDual
  rw [smul_eq_zero]
  constructor
  · intro h
    exact Or.inr (by rw [h, add_neg_cancel])
  · rintro (h | h)
    · norm_num at h
    · exact eq_neg_of_add_eq_zero_right h

/-- **The instanton criterion, defect form**: `★F = −F ⟺ ‖F‖² = ‖P₋F‖²` — the
field is an anti-self-dual instanton exactly when the self-dual defect term drops
out of the 4D functional and the curvature norm concentrates in the ASD sector
(`F_ASD = 0 ⟺ Ξ` curvature term `= 0`, in the SD/ASD-symmetric formulation). -/
theorem antiSelfDual_iff_norm_concentrates {s : V →ₗ[ℝ] V}
    (hinv : ∀ ω, s (s ω) = ω)
    (hsym : ∀ x y, inner ℝ (s x) y = inner ℝ x (s y)) (ω : V) :
    s ω = -ω ↔ ‖ω‖ ^ 2 = ‖projAntiSelfDual s ω‖ ^ 2 := by
  rw [antiSelfDual_iff_sdProj_zero]
  constructor
  · intro h
    rw [crossTerm_split hinv hsym, h, norm_zero]
    ring
  · intro h
    have hsplit := crossTerm_split hinv hsym ω
    have hzero : ‖projSelfDual s ω‖ ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
    exact norm_eq_zero.mp this

/-! ### The topological energy bound (Donaldson)

The self-dual/anti-self-dual split turns the topological pairing `⟪ω, ★ω⟫` (the curvature
integral `∫Tr(F∧F)` reading off a characteristic number) into a lower bound for the
Yang–Mills energy `‖ω‖²`, saturated exactly by (anti-)self-dual fields. This is the
differential-geometric content of Donaldson's remark that the absolute minimum of the
Yang–Mills functional at a fixed topological type is attained by an anti-self-dual (or
self-dual) connection. -/

/-- **Self-dual criterion, projection form**: `★F = F ⟺ P₋F = 0`. The mirror of
`antiSelfDual_iff_sdProj_zero`. -/
theorem selfDual_iff_asdProj_zero (s : V →ₗ[ℝ] V) (ω : V) :
    s ω = ω ↔ projAntiSelfDual s ω = 0 := by
  unfold projAntiSelfDual
  rw [smul_eq_zero]
  constructor
  · intro h; exact Or.inr (by rw [h, sub_self])
  · rintro (h | h)
    · norm_num at h
    · exact (sub_eq_zero.mp h).symm

/-- **Signed sector identity**: the topological pairing `⟪ω, ★ω⟫` equals the signed
difference of the sector energies, `⟪ω, ★ω⟫ = ‖P₊ω‖² − ‖P₋ω‖²`. This is Donaldson's
`(1/8π²)∫Tr(F⁰∧F⁰) = ⅛π⁻²(‖F⁰₊‖² − ‖F⁰₋‖²)` — the characteristic number reads off as the
imbalance between the self-dual and anti-self-dual curvature energies. Needs no hypothesis
on `★`: the `‖★ω‖²` terms cancel in the difference. -/
theorem inner_hodgeStar_eq_selfDual_sub_antiSelfDual (s : V →ₗ[ℝ] V) (ω : V) :
    inner ℝ ω (s ω) = ‖projSelfDual s ω‖ ^ 2 - ‖projAntiSelfDual s ω‖ ^ 2 := by
  unfold projSelfDual projAntiSelfDual
  rw [norm_smul, norm_smul, mul_pow, mul_pow, norm_add_sq_real, norm_sub_sq_real,
    Real.norm_eq_abs]
  norm_num
  ring

/-- **Anti-self-dual defect formula**: `‖ω‖² − ⟪ω,★ω⟫ = 2‖P₋ω‖²`. -/
theorem norm_sq_sub_inner_hodgeStar {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω)
    (hsym : ∀ x y, inner ℝ (s x) y = inner ℝ x (s y)) (ω : V) :
    ‖ω‖ ^ 2 - inner ℝ ω (s ω) = 2 * ‖projAntiSelfDual s ω‖ ^ 2 := by
  rw [crossTerm_split hinv hsym ω, inner_hodgeStar_eq_selfDual_sub_antiSelfDual]
  ring

/-- **Self-dual defect formula**: `‖ω‖² + ⟪ω,★ω⟫ = 2‖P₊ω‖²`. -/
theorem norm_sq_add_inner_hodgeStar {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω)
    (hsym : ∀ x y, inner ℝ (s x) y = inner ℝ x (s y)) (ω : V) :
    ‖ω‖ ^ 2 + inner ℝ ω (s ω) = 2 * ‖projSelfDual s ω‖ ^ 2 := by
  rw [crossTerm_split hinv hsym ω, inner_hodgeStar_eq_selfDual_sub_antiSelfDual]
  ring

/-- **Topological bound, self-dual direction**: `⟪ω,★ω⟫ ≤ ‖ω‖²`, saturated exactly when
`ω` is self-dual. The characteristic number is a lower bound for the Yang–Mills energy. -/
theorem inner_hodgeStar_le_norm_sq {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω)
    (hsym : ∀ x y, inner ℝ (s x) y = inner ℝ x (s y)) (ω : V) :
    inner ℝ ω (s ω) ≤ ‖ω‖ ^ 2 := by
  have h := norm_sq_sub_inner_hodgeStar hinv hsym ω
  nlinarith [sq_nonneg ‖projAntiSelfDual s ω‖]

/-- **Topological bound, anti-self-dual direction**: `−⟪ω,★ω⟫ ≤ ‖ω‖²`, saturated exactly
when `ω` is anti-self-dual. -/
theorem neg_inner_hodgeStar_le_norm_sq {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω)
    (hsym : ∀ x y, inner ℝ (s x) y = inner ℝ x (s y)) (ω : V) :
    -inner ℝ ω (s ω) ≤ ‖ω‖ ^ 2 := by
  have h := norm_sq_add_inner_hodgeStar hinv hsym ω
  nlinarith [sq_nonneg ‖projSelfDual s ω‖]

/-- **The topological (Bogomolny) bound**: `|⟪ω,★ω⟫| ≤ ‖ω‖²` — the absolute value of the
characteristic number bounds the Yang–Mills energy from below. -/
theorem abs_inner_hodgeStar_le_norm_sq {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω)
    (hsym : ∀ x y, inner ℝ (s x) y = inner ℝ x (s y)) (ω : V) :
    |inner ℝ ω (s ω)| ≤ ‖ω‖ ^ 2 :=
  abs_le.mpr ⟨by linarith [neg_inner_hodgeStar_le_norm_sq hinv hsym ω],
    inner_hodgeStar_le_norm_sq hinv hsym ω⟩

/-- **Saturation of the self-dual bound**: `⟪ω,★ω⟫ = ‖ω‖² ⟺ ★ω = ω`. -/
theorem inner_hodgeStar_eq_norm_sq_iff_selfDual {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω)
    (hsym : ∀ x y, inner ℝ (s x) y = inner ℝ x (s y)) (ω : V) :
    inner ℝ ω (s ω) = ‖ω‖ ^ 2 ↔ s ω = ω := by
  rw [selfDual_iff_asdProj_zero]
  have h := norm_sq_sub_inner_hodgeStar hinv hsym ω
  constructor
  · intro heq
    have hz : ‖projAntiSelfDual s ω‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hz)
  · intro h0
    rw [h0, norm_zero] at h
    linarith

/-- **Saturation of the topological bound**: the Yang–Mills energy equals `|⟪ω,★ω⟫|`
exactly when the field is self-dual or anti-self-dual — Donaldson's absolute minimizers of
the Yang–Mills functional at fixed topological type. -/
theorem abs_inner_hodgeStar_eq_norm_sq_iff_selfDual_or_antiSelfDual
    {s : V →ₗ[ℝ] V} (hinv : ∀ ω, s (s ω) = ω)
    (hsym : ∀ x y, inner ℝ (s x) y = inner ℝ x (s y)) (ω : V) :
    |inner ℝ ω (s ω)| = ‖ω‖ ^ 2 ↔ s ω = ω ∨ s ω = -ω := by
  have hsd := norm_sq_sub_inner_hodgeStar hinv hsym ω
  have hasd := norm_sq_add_inner_hodgeStar hinv hsym ω
  constructor
  · intro heq
    rcases abs_cases (inner ℝ ω (s ω)) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at heq
      exact Or.inl ((inner_hodgeStar_eq_norm_sq_iff_selfDual hinv hsym ω).mp heq)
    · right
      rw [he] at heq
      rw [antiSelfDual_iff_sdProj_zero]
      have hz : ‖projSelfDual s ω‖ ^ 2 = 0 := by linarith
      exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp hz)
  · rintro (h0 | h0)
    · rw [(inner_hodgeStar_eq_norm_sq_iff_selfDual hinv hsym ω).mpr h0, abs_of_nonneg]
      exact sq_nonneg _
    · rw [antiSelfDual_iff_sdProj_zero] at h0
      rw [h0, norm_zero] at hasd
      norm_num at hasd
      have hneg : inner ℝ ω (s ω) = -‖ω‖ ^ 2 := by linarith
      rw [hneg, abs_neg, abs_of_nonneg (sq_nonneg _)]

/-! ## §B — the non-abelian three-vertex -/

/-- The Levi-Civita symbol is antisymmetric in its first two slots:
`ε^{bac} = −ε^{abc}`. -/
theorem leviCivita3_swap (a b c : Fin 3) :
    leviCivita3 b a c = -leviCivita3 a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp +decide [leviCivita3]

set_option linter.unusedSimpArgs false in
/-- **The `𝔰𝔲(2)` three-vertex**: `[σᵃ, σᵇ] = 2i·Σ_c ε^{abc}σᶜ` — the non-abelian
structure constants, the trilinear gauge-boson coupling shared by every non-abelian
sector (weak `SU(2)`, the gluon's `𝔰𝔲(2)` subalgebras) and absent for the abelian
photon. -/
theorem pauliVec_commutator (a b : Fin 3) :
    pauliVec a * pauliVec b - pauliVec b * pauliVec a
      = (2 * Complex.I) • ∑ c, ((leviCivita3 a b c : ℝ) : ℂ) • pauliVec c := by
  fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliVec, leviCivita3, pauliX, pauliY, pauliZ, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.I_sq] <;>
    first
      | ring1
      | norm_num [mul_assoc, Complex.I_mul_I, Complex.I_sq]

/-- **The three-vertex measured by the embedding trace form**:
`Tr([σᵃ,σᵇ]σᶜ) = 4i·ε^{abc}` — the same `ε` as in the Eq. 9→10 conversion
(`pauliVec_trace_triple`): the Lie-bracket three of the vertex is the trace-form
three of the spatial Dirac reduction. -/
theorem threeVertex_trace (a b c : Fin 3) :
    ((pauliVec a * pauliVec b - pauliVec b * pauliVec a) * pauliVec c).trace
      = 4 * Complex.I * ((leviCivita3 a b c : ℝ) : ℂ) := by
  rw [Matrix.sub_mul, Matrix.trace_sub, pauliVec_trace_triple, pauliVec_trace_triple,
    leviCivita3_swap]
  push_cast
  ring

/-! ## §C — the quaternionic `S³ ≅ SU(2)` -/

/-- **The quaternion representation** `ℍ → M₂(ℂ)`:
`q = a + bi + cj + dk ↦ a·1 + b(−iσ₁) + c(−iσ₂) + d(−iσ₃)` — concretely
`[[a − di, −c − bi], [c − bi, a + di]]`. -/
def quaternionRep (q : Quaternion ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    if i = 0 then
      (if j = 0 then (q.re : ℂ) - q.imK * Complex.I
       else -(q.imJ : ℂ) - q.imI * Complex.I)
    else
      (if j = 0 then (q.imJ : ℂ) - q.imI * Complex.I
       else (q.re : ℂ) + q.imK * Complex.I)

/-- `rep 1 = 1`. -/
theorem quaternionRep_one : quaternionRep 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRep, Quaternion.re_one, Quaternion.imI_one,
      Quaternion.imJ_one, Quaternion.imK_one]

/-- **The representation is multiplicative** — `ℍ → M₂(ℂ)` is an algebra map, the
mechanism of `S³ ≅ SU(2)`. -/
theorem quaternionRep_mul (p q : Quaternion ℝ) :
    quaternionRep (p * q) = quaternionRep p * quaternionRep q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRep, Matrix.mul_apply, Fin.sum_univ_two, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.ext_iff] <;>
    constructor <;> ring

/-- **The imaginary units land on the `𝔰𝔲(2)` Pauli generators**:
`rep(i) = −iσ₁`, `rep(j) = −iσ₂`, `rep(k) = −iσ₃` — the quaternionic fiber and the
spin embedding of the configuration space run on the same three generators. -/
theorem quaternionRep_imaginaryUnits :
    quaternionRep ⟨0, 1, 0, 0⟩ = -Complex.I • pauliVec 0
    ∧ quaternionRep ⟨0, 0, 1, 0⟩ = -Complex.I • pauliVec 1
    ∧ quaternionRep ⟨0, 0, 0, 1⟩ = -Complex.I • pauliVec 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quaternionRep, pauliVec, pauliX, pauliY, pauliZ]

/-- **The center is `ℤ₂`, not `ℤ₃`**: each imaginary unit squares to the central
`−1` — `SU(2)`'s multiplicative center is `{±1}`, so the three-vertex `ε^{abc}` of
`pauliVec_commutator` is the *adjoint* (Lie-bracket, additive) three, not a
center/triality three. -/
theorem quaternionRep_imaginaryUnit_sq :
    quaternionRep ⟨0, 1, 0, 0⟩ * quaternionRep ⟨0, 1, 0, 0⟩ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRep, Matrix.mul_apply, Fin.sum_univ_two]

/-- `rep(q̄) = rep(q)ᴴ` — quaternionic conjugation is the matrix adjoint. -/
theorem quaternionRep_star (q : Quaternion ℝ) :
    quaternionRep (star q) = (quaternionRep q).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quaternionRep, Matrix.conjTranspose_apply]

/-- `det(rep q) = |q|²` — the determinant is the quaternionic norm. -/
theorem quaternionRep_det (q : Quaternion ℝ) :
    (quaternionRep q).det = (Quaternion.normSq q : ℝ) := by
  rw [Matrix.det_fin_two]
  simp [quaternionRep, Quaternion.normSq_def', Complex.ext_iff]
  constructor <;> simp [← Complex.ofReal_pow] <;> ring

/-- **`S³` lands in `SU(2)`**: a unit quaternion represents as a unitary matrix of
determinant one — the fiber `ξ, η ∈ S³ ≅ SU(2) ≅ ℍ₁`, and the gauge group of the
configuration space `𝒜` whose Dirac operator the arc fluctuates. -/
theorem unitQuaternion_mem_SU2 {q : Quaternion ℝ} (hq : Quaternion.normSq q = 1) :
    (quaternionRep q).conjTranspose * quaternionRep q = 1
      ∧ (quaternionRep q).det = 1 := by
  constructor
  · rw [← quaternionRep_star, ← quaternionRep_mul]
    have hs : star q * q = ((Quaternion.normSq q : ℝ) : Quaternion ℝ) :=
      Quaternion.star_mul_self q
    rw [hs, hq]
    simpa using quaternionRep_one
  · rw [quaternionRep_det, hq]
    norm_num

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SelfDualQuaternionYangMills

end
