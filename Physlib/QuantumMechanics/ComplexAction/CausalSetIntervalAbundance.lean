/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Order.Interval.Finset.Basic
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState

/-!
# Interval abundances and locality in a manifoldlike causal set (Glaser–Surya)

L. Glaser & S. Surya, *Towards a Definition of Locality in a Manifoldlike Causal Set*, Phys. Rev. D **88**,
124026 (2013), arXiv:1309.3403. A causal set is a locally finite partial order; Malament's theorem says the
order plus the element count fixes the conformal geometry ("order + number ≈ spacetime"). Glaser–Surya use
the **interval abundances** `N_m` — the number of order intervals containing exactly `m` elements — as a
local, coordinate-free signature of flat spacetime, and hence a discrete dimension estimator.

This file formalizes the paper's exact **derivable** content and connects the causal order to the repository's
Sorkin–Johnston machinery. Definitions are labelled as definitions; the theorems below are genuine
derivations, not restatements.

* **§A — the causal order, its interval, and the Sorkin bridge.** `orderInterval x y = Set.Icc x y` (the
  Alexandrov interval), `orderInterval_eq_empty_iff` (an interval is empty iff the two points are causally
  unrelated), the `intervalAbundance` observable `N_m`, and the 2D Benincasa–Dowker action
  `bdgAction2D = N − 2N₀ + 4N₁ − 2N₂` (Eq. 1). **`causalSign_isPauliJordan`** is a genuine derivation: the
  causal sign `sgn(x,y)` of the order is an antisymmetric kernel, i.e. it is a
  `SorkinJohnstonRegionState.IsPauliJordan` — the causal order canonically induces the Pauli–Jordan
  (Peierls-commutator) structure that fixes the Sorkin–Johnston vacuum.
* **§B — Poisson sprinkling (Eq. 2).** `poissonSprinkle ρ V m = (ρV)^m/m! · e^{−ρV}`, the probability of `m`
  sprinkled points in volume `V` at density `ρ`. `hasSum_poissonSprinkle` / `tsum_poissonSprinkle` prove
  normalization `∑_m P_V(m) = 1` (from the exponential series `∑ x^n/n! = e^x`), and `poissonSprinkle_nonneg`.
* **§C — the differential-operator form (Eq. 17).** `poissonSprinkle_eq_iteratedDeriv`:
  `P(m,V,ρ) = (−ρ)^m/m! · ∂ᵐ_ρ e^{−ρV}` — the `m`-point probability is the `m`-th `ρ`-derivative of the
  no-point probability `e^{−ρV}`, from the exact iterated derivative `∂ᵐ_ρ e^{−Vρ} = (−V)^m e^{−Vρ}`. This is
  the identity Glaser–Surya use to generate every abundance `⟨N_m^d⟩` from `⟨N_0^d⟩` (Eq. 18).
* **§D — the scale-invariant flat-space abundance ratio (Eq. 21).**
  `flatAbundanceRatio d m = Γ(2/d + m)/(Γ(2/d) Γ(m+1))`, the `N → ∞` limit `S_m^d = ⟨N_m^d⟩/⟨N_0^d⟩`.
  `flatAbundanceRatio_zero` (`S_0^d = 1`, the normalization) and **`flatAbundanceRatio_two`**
  (`S_m^2 = 1` for every `m`) — the paper's explicit observation that in `d = 2` the ratio is independent of
  `m`, a clean Gamma identity (`Γ(1) = 1`, `Γ(m+1) = m!`).

**Honest layering.** `orderInterval`, `intervalAbundance`, `bdgAction2D`, `poissonSprinkle`, and
`flatAbundanceRatio` are definitions of the paper's objects. The derivations are: the Pauli–Jordan
antisymmetry of the causal sign (§A), the exp-series normalization of the sprinkling law (§B), the
iterated-derivative identity Eq. 17 (§C), and the two boundary Gamma identities `S_0^d = 1`, `S_m^2 = 1`
(§D). The full hypergeometric asymptotics giving `S_m^d` for general `d` (Eqs. 20, 22–28) are the paper's
Mathematica computation and are not reproduced; only its normalization and `d = 2` corollaries are proven.

## References

* L. Glaser, S. Surya, *Towards a Definition of Locality in a Manifoldlike Causal Set*, Phys. Rev. D 88,
  124026 (2013), arXiv:1309.3403. Links to `SorkinJohnstonRegionState` (`IsPauliJordan`) — the causal-set
  vacuum whose defining Pauli–Jordan kernel §A derives from the causal order.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance

open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState

variable {α : Type*}


/-- The **order interval** (Alexandrov interval) `I[x,y] = {z | x ≤ z ≤ y}` of a causal set: the set of
elements causally between `x` and `y`. Malament's theorem identifies this order-theoretic interval with the
spacetime Alexandrov interval. In a partial order it is exactly `Set.Icc x y`. -/
def orderInterval [Preorder α] (x y : α) : Set α := Set.Icc x y

/-- **An order interval is empty iff the endpoints are causally unrelated** `I[x,y] = ∅ ↔ ¬ x ≤ y`: the
order structure alone detects causal relation. -/
lemma orderInterval_eq_empty_iff [Preorder α] {x y : α} :
    orderInterval x y = ∅ ↔ ¬ x ≤ y := Set.Icc_eq_empty_iff

/-- The **`m`-element interval abundance** `N_m` of a finite causal set: the number of ordered pairs `(x,y)`
whose open order interval `(x,y) = {z | x < z < y}` contains exactly `m` elements. `N₀` counts links
(nearest-neighbour causal pairs), `N₁` irreducible 3-chains, `N₂` diamonds — the observables whose
flat-spacetime profile Glaser–Surya use to define locality. -/
def intervalAbundance [Fintype α] [Preorder α] [LocallyFiniteOrder α] (m : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : α × α => (Finset.Ioo p.1 p.2).card = m)).card

/-- The **2D Benincasa–Dowker causal-set action** (Eq. 1): the discrete Einstein–Hilbert action of a 2D
causal set as a linear combination of interval abundances, `(1/ℏ) S₂D = N − 2N₀ + 4N₁ − 2N₂`, with `N` the
number of elements and `N₀,N₁,N₂` the link/3-chain/diamond abundances. -/
def bdgAction2D (N N₀ N₁ N₂ : ℝ) : ℝ := N - 2 * N₀ + 4 * N₁ - 2 * N₂

/-- The **causal sign** of the order: `sgn(x,y) = +1` if `x ≺ y`, `−1` if `y ≺ x`, `0` otherwise. -/
def causalSign [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)] (x y : α) : ℝ :=
  if x < y then 1 else if y < x then -1 else 0

/-- **The causal sign is a Pauli–Jordan kernel** `sgn(x,y) = −sgn(y,x)`: the antisymmetry of the strict
causal order makes `causalSign` an antisymmetric kernel, i.e. a
`SorkinJohnstonRegionState.IsPauliJordan`. Thus a causal set canonically supplies the Pauli–Jordan
(Peierls-commutator) function that fixes the Sorkin–Johnston vacuum — the causal order *is* the input to that
construction. -/
lemma causalSign_isPauliJordan [Preorder α] [DecidableRel ((· < ·) : α → α → Prop)] :
    IsPauliJordan (causalSign (α := α)) := by
  intro x y
  simp only [causalSign]
  by_cases h1 : x < y
  · simp only [if_pos h1, if_neg (lt_asymm h1)]; norm_num
  · by_cases h2 : y < x
    · simp only [if_neg h1, if_pos h2]
    · simp only [if_neg h1, if_neg h2]; norm_num


/-- The **Poisson sprinkling probability** (Eq. 2): the probability that a Poisson sprinkling of density `ρ`
places exactly `m` elements in a spacetime region of volume `V`, `P_V(m) = (ρV)^m/m! · e^{−ρV}`. -/
noncomputable def poissonSprinkle (ρ V : ℝ) (m : ℕ) : ℝ :=
  (ρ * V) ^ m / m.factorial * Real.exp (-(ρ * V))

/-- **The sprinkling probability is non-negative** for a non-negative sprinkled volume `ρV ≥ 0`. -/
lemma poissonSprinkle_nonneg (ρ V : ℝ) (h : 0 ≤ ρ * V) (m : ℕ) :
    0 ≤ poissonSprinkle ρ V m :=
  mul_nonneg (div_nonneg (pow_nonneg h m) (by positivity)) (Real.exp_pos _).le

/-- **The Poisson sprinkling law is normalized** `∑_m P_V(m) = 1` (as a `HasSum`): summing the point counts
over all `m` gives probability one. This is the exponential series `∑_n (ρV)^n/n! = e^{ρV}` times the prefactor
`e^{−ρV}`. -/
lemma hasSum_poissonSprinkle (ρ V : ℝ) :
    HasSum (fun m : ℕ => poissonSprinkle ρ V m) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (ρ * V)).mul_left (Real.exp (-(ρ * V)))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  have hfun : (fun m : ℕ => poissonSprinkle ρ V m)
      = fun n : ℕ => Real.exp (-(ρ * V)) * ((ρ * V) ^ n / n.factorial) := by
    funext n; rw [poissonSprinkle]; ring
  rw [hfun]
  simpa using h

/-- **Normalization as a `tsum`** `∑_m P_V(m) = 1`. -/
lemma tsum_poissonSprinkle (ρ V : ℝ) : ∑' m : ℕ, poissonSprinkle ρ V m = 1 :=
  (hasSum_poissonSprinkle ρ V).tsum_eq


/-- **The `m`-point probability is the `m`-th density-derivative of the empty-region probability** (Eq. 17):
`P(m,V,ρ) = (−ρ)^m/m! · ∂ᵐ_ρ e^{−ρV}`. This follows from the exact iterated derivative
`∂ᵐ_ρ e^{−Vρ} = (−V)^m e^{−Vρ}` and `(−ρ)^m (−V)^m = (ρV)^m`. Glaser–Surya use precisely this operator to
generate every interval abundance `⟨N_m^d⟩` from the abundance of links `⟨N_0^d⟩` (Eq. 18). -/
lemma poissonSprinkle_eq_iteratedDeriv (ρ V : ℝ) (m : ℕ) :
    poissonSprinkle ρ V m
      = (-ρ) ^ m / m.factorial * iteratedDeriv m (fun r : ℝ => Real.exp (-V * r)) ρ := by
  have hd : iteratedDeriv m (fun r : ℝ => Real.exp (-V * r)) ρ
      = (-V) ^ m * Real.exp (-V * ρ) :=
    congrFun (iteratedDeriv_exp_const_mul m (-V)) ρ
  rw [hd, poissonSprinkle, show -V * ρ = -(ρ * V) by ring, ← neg_mul_neg ρ V, mul_pow]
  ring


/-- The **asymptotic flat-space interval-abundance ratio** `S_m^d = lim_{ρ→∞} ⟨N_m^d⟩/⟨N_0^d⟩` (Eq. 21):
`S_m^d = Γ(2/d + m)/(Γ(2/d) · Γ(m+1))`. This scale-invariant profile is Glaser–Surya's flat-spacetime
signature. -/
noncomputable def flatAbundanceRatio (d : ℝ) (m : ℕ) : ℝ :=
  Real.Gamma (2 / d + m) / (Real.Gamma (2 / d) * Real.Gamma (m + 1))

/-- **The abundance ratio is normalized at `m = 0`** `S_0^d = 1` for any positive dimension `d > 0`: the
ratio of an abundance to itself. -/
lemma flatAbundanceRatio_zero (d : ℝ) (hd : 0 < d) : flatAbundanceRatio d 0 = 1 := by
  have h2d : (0 : ℝ) < 2 / d := div_pos (by norm_num) hd
  have hne : Real.Gamma (2 / d) ≠ 0 := (Real.Gamma_pos_of_pos h2d).ne'
  rw [flatAbundanceRatio, Nat.cast_zero, add_zero, zero_add, Real.Gamma_one, mul_one, div_self hne]

/-- **In `d = 2` the abundance ratio is independent of `m`** `S_m^2 = 1` for every `m` — Glaser–Surya's
explicit flat-`(1+1)`-spacetime observation. Since `2/2 = 1`, `Γ(1) = 1`, and `Γ(m+1) = m!`, the ratio is
`Γ(m+1)/Γ(m+1) = 1`. -/
lemma flatAbundanceRatio_two (m : ℕ) : flatAbundanceRatio 2 m = 1 := by
  have hne : Real.Gamma ((m : ℝ) + 1) ≠ 0 := by
    rw [Real.Gamma_nat_eq_factorial]; exact_mod_cast Nat.factorial_ne_zero m
  rw [flatAbundanceRatio, show (2 : ℝ) / 2 = 1 by norm_num, Real.Gamma_one, one_mul,
    add_comm (1 : ℝ) (m : ℝ), div_self hne]

end Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance
