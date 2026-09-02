/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic
meta import Zil
meta import Mathlib.Data.Fintype.Basic
meta import Mathlib.Data.Fintype.BigOperators
meta import Mathlib.Algebra.BigOperators.Fin

/-!
# From asymptotic freedom to confinement: β-function, Cornell potential, Migdal's area law

The QCD-dynamics layer in four namespaces (each formerly its own module):

* **Part I — `Su3AsymptoticFreedom`.** The one-loop `β`-coefficient
  `b₀ = (11/3)C₂(adj) − (2/3)n_f` written through the adjoint Casimir (`betaZero_gluon_term`):
  real-world QCD is asymptotically free (`qcd_asymptotically_free`, `b₀ = 7 > 0` at `N = 3`,
  `n_f = 6`), the flavour bound `0 < b₀ ⟺ n_f ≤ 16` (`asymptotic_freedom_bound`), freedom lost at
  `17` flavours, and the colour-Coulomb coefficient identified with the fundamental Casimir
  `C_F = 4/3 = casimir3 1 0` (`coulomb_casimir`).
* **Part II — `Su3ConfinementPotential`.** The infrared complement: the Cornell potential
  `V(r) = −C_F αₛ/r + σr`, the Wilson loop with the area law whose extracted static potential is
  linear (`wilson_area_law_potential`), the unboundedness of the linear term — confinement
  (`confining_unbounded`), and the Coulomb-coefficient Casimir (`cornell_coulomb_casimir`).
* **Part III — `MigdalPlanarLoopConfinement`.** Migdal's confining matrix surface
  (arXiv:2507.05096v3): the area law `|S| = s[c]·A` with a scale-invariant shape factor
  (`matrixArea_scale`), confinement via the unbounded area (`migdal_area_law_confines`, through
  Part II's `confining_unbounded`), the universal elliptic factor `1/√2` (`migdalFactor_sq`),
  Theorem 1's constrained-infimum inequality (`confinement_area_inequality`), Theorem 2's
  area-element triangle inequality (`area_element_norm_ineq`), and the self-dual chirality
  involution (`selfdual_chirality_sq`).
* **Part IV — `MigdalSelfDualLoopSolution`.** The algebraic core of the loop-equation solution: the
  4D Levi-Civita symbol and Hodge dual on 2-forms (`eps4`, `hodge2`), the ('t Hooft) self-dual and
  anti-self-dual sectors with their orthogonality (`tHooft3_selfDual`, `tHooftBar3_antiSelfDual`,
  `tHooft3_orthogonal_bar`), and the mechanism: a self-dual area derivative annihilates the
  classical Yang–Mills term `½(F − *F)` (`selfDual_nullifies_classical_term`,
  `tHooft3_classical_term_zero`).

**Honest layering.** Exact: the sign analysis of `b₀`, the Casimir identifications, the area-law ⇒
linear-potential extraction, the unboundedness, the scale invariance, the infimum and triangle
inequalities, the Hodge-star computations and the nullification. Stated as input: the one-loop
`β`-function formula (Gross–Wilczek–Politzer), the Cornell form and area-law ⇒ confinement reading,
the dynamical origin of `σ > 0` (the mass gap), and Migdal's functional loop-equation solution with
its `s = 1/√2` computation.

## References

* D. Gross, F. Wilczek; H. D. Politzer (1973), asymptotic freedom. K. Wilson (1974), confinement
  and the area law; the Cornell potential. A. Migdal, arXiv:2507.05096v3 (2025), §§2.3, 4.2,
  4.10–4.11, Theorems 1–2. Built on `Particles.Su3WeylDimensionCasimir` / `AdjointCasimir`; the
  't Hooft `Λ²₊ ⊕ Λ²₋` split connects to `Curvature.GaussBonnetPontryaginSelfDual`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.Su3AsymptoticFreedom

open Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir


/-- The **one-loop QCD `β`-function coefficient** `b₀ = (11/3) N − (2/3) n_f` for `SU(N)` with `n_f` flavours
(`= (11/3) C₂(adj) − (4/3) T_F n_f`, `T_F = 1/2`). -/
def betaZero (N nf : ℚ) : ℚ := (11 / 3) * N - (2 / 3) * nf

/-- **The gluon term is `11/3` times the adjoint Casimir** `b₀ = (11/3) C₂(adj) − (2/3) n_f`, with
`C₂(adj) = adjointCasimirN N = N` — the gluon antiscreening driven by the adjoint Casimir. -/
lemma betaZero_gluon_term (N nf : ℚ) :
    betaZero N nf = 11 / 3 * adjointCasimirN N - 2 / 3 * nf := rfl


/-- **Real-world QCD is asymptotically free** `0 < betaZero 3 6`: with `N = 3` colours and `n_f = 6` flavours,
`b₀ = 11 − 4 = 7 > 0`, so the coupling decreases at high energy. -/
lemma qcd_asymptotically_free : 0 < betaZero 3 6 := by norm_num [betaZero]

/-- **The asymptotic-freedom flavour bound** `0 < betaZero 3 n_f ⟺ n_f ≤ 16`: `SU(3)` gauge theory is
asymptotically free exactly when there are at most `16` quark flavours (`n_f < 33/2`), beyond which quark
screening overwhelms gluon antiscreening. -/
lemma asymptotic_freedom_bound (nf : ℕ) : 0 < betaZero 3 (nf : ℚ) ↔ nf ≤ 16 := by
  rw [betaZero]
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have h17 : (17 : ℚ) ≤ (nf : ℚ) := by exact_mod_cast hc
    nlinarith
  · intro h
    have h16 : (nf : ℚ) ≤ 16 := by exact_mod_cast h
    nlinarith

/-- **Beyond `16` flavours the theory is not asymptotically free** `betaZero 3 17 < 0`: quark screening wins,
the coupling grows at high energy (an infrared-free / Landau-pole theory). -/
lemma qcd_loses_freedom : betaZero 3 17 < 0 := by norm_num [betaZero]


/-- **The colour-Coulomb coefficient is the fundamental Casimir** `C_F = 4/3 = casimir3 1 0`: the
short-distance static quark–antiquark potential `V(r) ≈ −C_F αₛ/r` is governed by the fundamental quadratic
Casimir (`Su3WeylDimensionCasimir.casimir3_fundamental`). -/
lemma coulomb_casimir : (4 : ℚ) / 3 = casimir3 1 0 := casimir3_fundamental.symm

end Physlib.QuantumMechanics.ComplexAction.Particles.Su3AsymptoticFreedom

/-! ## Part II — confinement: the linear potential and the Wilson-loop area law -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential

open Physlib.QuantumMechanics.ComplexAction.Particles.Su3AsymptoticFreedom
open Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir


/-- The **Cornell static quark potential** `V(r) = −C_F αₛ/r + σ r`: the colour-Coulomb term (fundamental
Casimir `C_F`, coupling `αₛ`) plus the linear confining term (string tension `σ`). -/
noncomputable def cornellPotential (cf alpha sigma r : ℝ) : ℝ := -cf * alpha / r + sigma * r


/-- The **Wilson loop with the area law** `⟨W⟩ = e^{−σ · A}` (area `A`, string tension `σ`). -/
noncomputable def wilsonLoop (σ A : ℝ) : ℝ := Real.exp (-σ * A)

/-- **The area law gives a linear potential** `−(1/T) log⟨W(R×T)⟩ = σ R`: extracting the static potential from
an `R × T` Wilson loop of area `R·T` obeying the area law yields the **linear** confining potential `σ R`. -/
lemma wilson_area_law_potential (σ R T : ℝ) (hT : T ≠ 0) :
    -(Real.log (wilsonLoop σ (R * T))) / T = σ * R := by
  rw [wilsonLoop, Real.log_exp]; field_simp


/-- **The confining potential is unbounded** `σ > 0 ⇒ ∀ M, ∃ r, M < σ r`: the linear term grows without bound,
so it costs infinite energy to separate a quark pair — colour confinement. -/
lemma confining_unbounded (sigma : ℝ) (hσ : 0 < sigma) (M : ℝ) : ∃ r, M < sigma * r := by
  refine ⟨(M + 1) / sigma, ?_⟩
  rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hσ)]; linarith

/-- **The colour-Coulomb coefficient is the fundamental Casimir** `C_F = 4/3 = casimir3 1 0`: the short-distance
`−C_F αₛ/r` term of `cornellPotential` uses the same fundamental quadratic Casimir as
`Su3AsymptoticFreedom.coulomb_casimir`. -/
lemma cornell_coulomb_casimir : (4 : ℚ) / 3 = casimir3 1 0 := coulomb_casimir


/-- The **Coulomb–linear crossover radius** `r_c = √(C_F αₛ/σ)` — the separation at which the perturbative
colour-Coulomb term `C_F αₛ/r` and the confining linear term `σ r` of the `cornellPotential` have equal
magnitude: the length scale marking the crossover from the short-distance Coulomb regime to the
long-distance confining regime. -/
noncomputable def crossoverRadius (cf alpha sigma : ℝ) : ℝ := Real.sqrt (cf * alpha / sigma)

/-- **[The crossover radius is positive] `r_c > 0`** for positive colour factor, coupling and string
tension. -/
lemma crossoverRadius_pos (cf alpha sigma : ℝ) (hcf : 0 < cf) (ha : 0 < alpha) (hσ : 0 < sigma) :
    0 < crossoverRadius cf alpha sigma := by
  unfold crossoverRadius
  apply Real.sqrt_pos.mpr
  positivity

/-- **[The Cornell terms balance at the crossover radius] `C_F αₛ/r_c = σ r_c`.** At `r_c = √(C_F αₛ/σ)`
the magnitude of the colour-Coulomb term equals that of the linear confining term: the perturbative and
confining contributions to the static potential cross over. Equivalently `σ r_c² = C_F αₛ`, so `r_c` fixes
the confinement length from the coupling and the string tension. -/
lemma cornell_terms_balance_at_crossover (cf alpha sigma : ℝ) (hcf : 0 < cf) (ha : 0 < alpha)
    (hσ : 0 < sigma) :
    cf * alpha / crossoverRadius cf alpha sigma = sigma * crossoverRadius cf alpha sigma := by
  have hσ' : sigma ≠ 0 := hσ.ne'
  have hrc : 0 < crossoverRadius cf alpha sigma := crossoverRadius_pos cf alpha sigma hcf ha hσ
  have hrsq : sigma * crossoverRadius cf alpha sigma ^ 2 = cf * alpha := by
    unfold crossoverRadius
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  rw [div_eq_iff hrc.ne']
  linear_combination -hrsq

end Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential

end

/-! ## Part III — Migdal's confining matrix surface: the exact area law of the planar loop equation -/

open scoped BigOperators

namespace Physlib.QuantumMechanics.ComplexAction.Particles.MigdalPlanarLoopConfinement

open Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential


/-- **Migdal's area law** `|S| = s[c] · A_min` (Eq. 4.55): the matrix minimal-surface area equals the Euclidean
minimal area `A` times a shape factor `s[c]`. -/
def matrixArea (s A : ℝ) : ℝ := s * A

/-- **The shape factor is scale-invariant** `|S|(k²A) = k²|S|(A)`: rescaling the loop by `k` scales both `|S|`
and the Euclidean area `A` by `k²`, so `s[c] = |S|/A` depends only on the loop *shape*, not its size. -/
lemma matrixArea_scale (s A k : ℝ) : matrixArea s (k ^ 2 * A) = k ^ 2 * matrixArea s A := by
  unfold matrixArea; ring

/-- **The area law confines** — for a positive shape factor the matrix area grows without bound with the loop
(`∀ M, ∃ A, M < s·A`), so the Wilson loop `e^{−a|S|} → 0`: colour confinement, the matrix-surface form of
`Su3ConfinementPotential.confining_unbounded` (the Wilson-loop area law). -/
lemma migdal_area_law_confines (s : ℝ) (hs : 0 < s) (M : ℝ) : ∃ A, M < matrixArea s A :=
  confining_unbounded s hs M


/-- Migdal's **universal elliptic shape factor** `s = 1/√2` (Eq. 4.56 / A.30) — the same for all ellipses. -/
noncomputable def migdalFactor : ℝ := 1 / Real.sqrt 2

/-- **The universal factor squares to `1/2`** `(1/√2)² = 1/2` — the ellipse area law `|S| = (1/√2) A_min`. -/
lemma migdalFactor_sq : migdalFactor ^ 2 = 1 / 2 := by
  unfold migdalFactor; rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]


/-- **Theorem 1 (Eq. 4.58): the constrained self-dual area is not smaller than the unconstrained minimal area.**
The self-dual (duality-constrained) configurations form a subset of the unconstrained ones, so the infimum of
the area over the constrained set is at least the infimum over the unconstrained set — the basic inequality
behind quark confinement. -/
lemma confinement_area_inequality {X : Type*} (area : X → ℝ)
    (constrained unconstrained : Set X) (hsub : constrained ⊆ unconstrained)
    (hne : constrained.Nonempty) (hbdd : BddBelow (area '' unconstrained)) :
    sInf (area '' unconstrained) ≤ sInf (area '' constrained) :=
  csInf_le_csInf hbdd (hne.image area) (Set.image_mono hsub)


/-- **Theorem 2 (Eq. 4.59): the area-element triangle inequality** `‖∑ₐ xₐ‖² ≤ (∑ₐ ‖xₐ‖)²` — the square of the
sum of the matrix area-element contributions is at most the square of the sum of their norms (the "square of
the sum is less than the square of the sum of absolute values"), bounding the unconstrained matrix area by the
Euclidean minimal area. -/
lemma area_element_norm_ineq {ι : Type*} (s : Finset ι) {E : Type*} [NormedAddCommGroup E]
    (x : ι → E) : ‖∑ A ∈ s, x A‖ ^ 2 ≤ (∑ A ∈ s, ‖x A‖) ^ 2 := by
  gcongr
  exact norm_sum_le s x


/-- **The Hodge self-duality is an involution** `λ = ±1 ⇒ λ² = 1` (Eq. 4.57): each point of the matrix surface
carries a fixed local chirality `λ = ±1` under `σ = (λ/2) ε σ` — the self-dual / anti-self-dual sectors, the
two spheres of the oriented-2-plane Grassmannian `G⁺₂(ℝ⁴) ≅ S² × S²`. -/
lemma selfdual_chirality_sq (lam : ℝ) (h : lam = 1 ∨ lam = -1) : lam ^ 2 = 1 := by
  rcases h with h | h <;> rw [h] <;> norm_num

end Physlib.QuantumMechanics.ComplexAction.Particles.MigdalPlanarLoopConfinement

/-! ## Part IV — self-duality nullifies the classical Yang–Mills term -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.MigdalSelfDualLoopSolution


/-- The **inversion-count sign** of `(i,j,k,l)`: `(−1)^{#inversions}`, the sign of the permutation
`(0,1,2,3) ↦ (i,j,k,l)` for distinct indices. -/
def permSign4 (i j k l : Fin 4) : ℚ :=
  (if j.val < i.val then -1 else 1) * (if k.val < i.val then -1 else 1) *
    (if l.val < i.val then -1 else 1) * (if k.val < j.val then -1 else 1) *
    (if l.val < j.val then -1 else 1) * (if l.val < k.val then -1 else 1)

/-- The **four-dimensional Levi-Civita symbol** `ε_{ijkl}` — the sign for a permutation of `(0,1,2,3)`, and `0`
if any two indices coincide. -/
def eps4 (i j k l : Fin 4) : ℚ :=
  if i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l then 0 else permSign4 i j k l

/-- The **Hodge dual of a 2-form** `(*F)_{μν} = ½ ε_{μνλρ} F_{λρ}` in four dimensions. -/
def hodge2 (F : Fin 4 → Fin 4 → ℚ) (μ ν : Fin 4) : ℚ := (1 / 2) * ∑ l, ∑ r, eps4 μ ν l r * F l r


/-- A **self-dual 2-form** `η³` (a 't Hooft symbol): nonzero at `(0,1) = +1`, `(1,0) = −1`, `(2,3) = +1`,
`(3,2) = −1`. -/
def tHooft3 (μ ν : Fin 4) : ℚ :=
  if μ = 0 ∧ ν = 1 then 1 else if μ = 1 ∧ ν = 0 then -1
  else if μ = 2 ∧ ν = 3 then 1 else if μ = 3 ∧ ν = 2 then -1 else 0

/-- An **anti-self-dual 2-form** `η̄³`: nonzero at `(0,1) = +1`, `(1,0) = −1`, `(2,3) = −1`, `(3,2) = +1`. -/
def tHooftBar3 (μ ν : Fin 4) : ℚ :=
  if μ = 0 ∧ ν = 1 then 1 else if μ = 1 ∧ ν = 0 then -1
  else if μ = 2 ∧ ν = 3 then -1 else if μ = 3 ∧ ν = 2 then 1 else 0

/-- **`η³` is self-dual** `*η³ = η³` — a nonzero element of the self-dual sector `Λ²₊`. -/
lemma tHooft3_selfDual : ∀ μ ν, hodge2 tHooft3 μ ν = tHooft3 μ ν := by native_decide

/-- **`η̄³` is anti-self-dual** `*η̄³ = −η̄³` — a nonzero element of the anti-self-dual sector `Λ²₋`. -/
lemma tHooftBar3_antiSelfDual : ∀ μ ν, hodge2 tHooftBar3 μ ν = - tHooftBar3 μ ν := by native_decide

/-- The **Frobenius contraction** `⟨F, G⟩ = ∑_{μν} F_{μν} G_{μν}` of two 2-forms. -/
def contraction (F G : Fin 4 → Fin 4 → ℚ) : ℚ := ∑ μ, ∑ ν, F μ ν * G μ ν

/-- **Self-dual ⊥ anti-self-dual** `⟨η³, η̄³⟩ = 0` — the self-duality constraint `η̄·σ = 0` (Eq. 4.41): the
self-dual and anti-self-dual sectors are orthogonal. -/
lemma tHooft3_orthogonal_bar : contraction tHooft3 tHooftBar3 = 0 := by native_decide


/-- The **classical Yang–Mills / loop-equation term** `½(F − *F)` — the anti-self-dual projection of the area
derivative. In Migdal's loop equation this is the classical (LHS) term; the Bianchi identity is the
complementary self-dual projection. -/
def antiSelfDualPart (F : Fin 4 → Fin 4 → ℚ) (μ ν : Fin 4) : ℚ := (1 / 2) * (F μ ν - hodge2 F μ ν)

/-- **Self-duality nullifies the classical Yang–Mills term** (Eqs. 4.64–4.65): if the area derivative `F` is
self-dual (`*F = F`), the classical term `½(F − *F)` vanishes identically. This is the mechanism by which
Migdal's self-dual matrix surface satisfies the classical part of the planar QCD loop equation — leaving only
the contact terms, which the boundary constraints nullify. -/
lemma selfDual_nullifies_classical_term (F : Fin 4 → Fin 4 → ℚ)
    (h : ∀ μ ν, hodge2 F μ ν = F μ ν) : ∀ μ ν, antiSelfDualPart F μ ν = 0 := by
  intro μ ν; unfold antiSelfDualPart; rw [h]; ring

/-- **The self-dual 't Hooft form solves the classical loop equation** `½(η³ − *η³) = 0` — a concrete witness of
the nullification (`tHooft3_selfDual` applied). -/
lemma tHooft3_classical_term_zero : ∀ μ ν, antiSelfDualPart tHooft3 μ ν = 0 :=
  selfDual_nullifies_classical_term tHooft3 tHooft3_selfDual

end Physlib.QuantumMechanics.ComplexAction.Particles.MigdalSelfDualLoopSolution

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.Su3AsymptoticFreedom.asymptotic_freedom_bound where
  formalizes @ "claim:su3-is-asymptotically-free-iff-at-most-sixteen-quark-flavours",
  supported_by @ "paper:gross-wilczek-politzer-1973-asymptotic-freedom"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential.confining_unbounded where
  formalizes @ "claim:the-linear-confining-potential-is-unbounded-so-quarks-are-confined",
  supported_by @ "paper:wilson-1974-confinement-of-quarks",
  caveat @ "claim:the-dynamical-origin-of-a-positive-string-tension-the-mass-gap-is-not-derived"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential.cornell_terms_balance_at_crossover where
  formalizes @ "claim:the-cornell-coulomb-and-linear-terms-balance-at-the-crossover-radius-sqrt-cf-alpha-over-sigma-the-confinement-length",
  requires @ "claim:the-linear-confining-potential-is-unbounded-so-quarks-are-confined",
  supported_by @ "paper:eichten-1978-charmonium-cornell-potential"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.MigdalPlanarLoopConfinement.migdal_area_law_confines where
  formalizes @ "claim:migdal-matrix-surface-area-law-confines-via-the-same-wilson-area-law",
  requires @ "claim:the-linear-confining-potential-is-unbounded-so-quarks-are-confined",
  supported_by @ "paper:migdal-2025-planar-qcd-loop-equation"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.MigdalSelfDualLoopSolution.selfDual_nullifies_classical_term where
  formalizes @ "claim:self-duality-nullifies-the-classical-yang-mills-loop-equation-term",
  supported_by @ "paper:migdal-2025-planar-qcd-loop-equation",
  caveat @ "claim:the-functional-loop-equation-and-contact-term-nullification-are-analytic-inputs"

zil_file_contract physlib.su3ConfinementPotential where
  promises "From asymptotic freedom to confinement: SU(3) is asymptotically free iff at most sixteen flavours, the linear confining potential is unbounded so quarks are confined, the Cornell Coulomb and linear terms balance at the crossover radius sqrt(C_F alpha/sigma) which sets the confinement length, Migdal's matrix-surface area law confines through the same Wilson area law, and self-duality nullifies the classical Yang-Mills term of the planar loop equation."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.Su3AsymptoticFreedom.betaZero",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential.cornellPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.MigdalPlanarLoopConfinement.matrixArea"]
  forbids_substitutes ["a derivation of a positive string tension, the QCD mass gap, which is not derived",
    "the one-loop beta-function formula and Migdal's functional loop-equation solution, taken as inputs"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.Su3AsymptoticFreedom.asymptotic_freedom_bound,
    Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential.confining_unbounded,
    Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential.cornell_terms_balance_at_crossover,
    Physlib.QuantumMechanics.ComplexAction.Particles.MigdalPlanarLoopConfinement.migdal_area_law_confines,
    Physlib.QuantumMechanics.ComplexAction.Particles.MigdalSelfDualLoopSolution.selfDual_nullifies_classical_term]

/- ZIL-END -/
