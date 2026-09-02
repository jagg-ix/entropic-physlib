/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Physlib.Thermodynamics.Landauer
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# First-passage weights of a birth-death chain: the discrete Dirichlet problem

The exact solvable core of one-dimensional metastability: on sites
`0, 1, ..., N` with positive nearest-neighbour transition weights `p k` (up)
and `q k` (down), the classical gambler's-ruin / first-passage function is the
solution of the discrete Dirichlet problem

`p x * (h (x+1) - h x) = q x * (h x - h (x-1))`, `h 0 = 0`, `h N = 1`,

and it has the explicit weight-ratio form
`h x = (∑ k < x, γ k) / (∑ k < N, γ k)` with the path weights
`γ 0 = 1`, `γ (k+1) = γ k * (q (k+1) / p (k+1))`.

* **Explicit solution.** `dirichletSolution` satisfies both boundary
  conditions (`dirichletSolution_zero`, `dirichletSolution_boundary`) and the
  interior flux balance (`dirichletSolution_harmonic`); with normalized
  transition probabilities `p x + q x = 1` the flux balance becomes the
  probabilistic harmonic identity `h x = p x * h (x+1) + q x * h (x-1)`
  (`dirichletSolution_harmonic_prob`).
* **Uniqueness.** Any function with the same boundary values satisfying the
  flux balance on the interior agrees with `dirichletSolution` on
  `0, 1, ..., N` (`dirichletSolution_unique`) - the discrete Dirichlet
  problem of the birth-death generator has exactly one solution, and it is
  the weight-ratio formula.
* **Detailed balance and the Arrhenius bound.** If the weight ratios come
  from a potential, `q k / p k = exp (β * (V k - V (k-1)))` - detailed
  balance with respect to the Gibbs measure of `V` - the path weights
  telescope to `γ x = exp (β * (V x - V 0))` (`pathWeight_eq_exp`), and the
  first step out of the well is exponentially suppressed by any barrier
  value: `dirichletSolution 1 ≤ exp (-β * (V m - V 0))` for every interior
  site `m < N` (`arrhenius_escape_bound`) - the exact finite form of the
  Arrhenius/Kramers barrier factor.

**Honest boundary.** This file proves the identity layer only: the explicit
formula, its harmonicity, its uniqueness, and the Gibbs-weight bound. The
probabilistic reading - that this function is the hitting probability of the
birth-death Markov chain - is standard but is not constructed here: no Markov
chain, stopping time, or measure appears. Landauer-side context: metastable
wells whose escape is Arrhenius-suppressed are the physical substrate of the
stored bit whose erasure cost is formalized in
`Physlib.Thermodynamics.Landauer`.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Thermodynamics.BirthDeathFirstPassage

/-- **Path weight** of the birth-death chain: `γ 0 = 1` and
`γ (k+1) = γ k * (q (k+1) / p (k+1))` - the product of down/up weight ratios
along the first `k` sites. -/
noncomputable def pathWeight (p q : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => pathWeight p q k * (q (k + 1) / p (k + 1))

/-- Path weights are positive for positive transition weights. -/
theorem pathWeight_pos {p q : ℕ → ℝ} (hp : ∀ k, 0 < p k) (hq : ∀ k, 0 < q k) :
    ∀ k, 0 < pathWeight p q k
  | 0 => one_pos
  | k + 1 => mul_pos (pathWeight_pos hp hq k) (div_pos (hq _) (hp _))

/-- **The weight-ratio solution of the discrete Dirichlet problem**:
`h x = (∑ k < x, γ k) / (∑ k < N, γ k)`. -/
noncomputable def dirichletSolution (p q : ℕ → ℝ) (N x : ℕ) : ℝ :=
  (∑ k ∈ Finset.range x, pathWeight p q k) /
    (∑ k ∈ Finset.range N, pathWeight p q k)

/-- The absorbing boundary at the origin: `h 0 = 0`. -/
theorem dirichletSolution_zero (p q : ℕ → ℝ) (N : ℕ) :
    dirichletSolution p q N 0 = 0 := by
  simp [dirichletSolution]

/-- The target boundary: `h N = 1` (positive weights, nonempty range). -/
theorem dirichletSolution_boundary {p q : ℕ → ℝ} (hp : ∀ k, 0 < p k)
    (hq : ∀ k, 0 < q k) {N : ℕ} (hN : 0 < N) :
    dirichletSolution p q N N = 1 := by
  unfold dirichletSolution
  refine div_self (ne_of_gt ?_)
  exact Finset.sum_pos (fun k _ => pathWeight_pos hp hq k)
    (Finset.nonempty_range_iff.mpr hN.ne')

/-- **Interior flux balance**: for `1 ≤ x`, the weight-ratio solution
satisfies `p x * (h (x+1) - h x) = q x * (h x - h (x-1))` - discrete
harmonicity for the birth-death generator. -/
@[zil_level physical_theorem]
theorem dirichletSolution_harmonic {p q : ℕ → ℝ} (hp : ∀ k, 0 < p k)
    (N : ℕ) {x : ℕ} (hx : 1 ≤ x) :
    p x * (dirichletSolution p q N (x + 1) - dirichletSolution p q N x) =
      q x * (dirichletSolution p q N x - dirichletSolution p q N (x - 1)) := by
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hx
  set D := ∑ k ∈ Finset.range N, pathWeight p q k with hD
  have hstep : ∀ z : ℕ,
      dirichletSolution p q N (z + 1) - dirichletSolution p q N z =
        pathWeight p q z / D := by
    intro z
    unfold dirichletSolution
    rw [Finset.sum_range_succ, ← hD, add_div]
    ring
  have hyx : 1 + y = y + 1 := Nat.add_comm 1 y
  have hsub : 1 + y - 1 = y := by omega
  have h1 := hstep (1 + y)
  have h2 := hstep y
  rw [hyx] at h1
  rw [hsub, hyx]
  rw [h1, h2]
  have hrec : pathWeight p q (y + 1) =
      pathWeight p q y * (q (y + 1) / p (y + 1)) := rfl
  rw [hrec]
  have hpne := (hp (y + 1)).ne'
  have hcancel : p (y + 1) * (q (y + 1) / p (y + 1)) = q (y + 1) := by
    field_simp
  calc p (y + 1) * (pathWeight p q y * (q (y + 1) / p (y + 1)) / D)
      = p (y + 1) * (q (y + 1) / p (y + 1)) * (pathWeight p q y / D) := by ring
    _ = q (y + 1) * (pathWeight p q y / D) := by rw [hcancel]

/-- **Probabilistic harmonic identity**: with normalized transition
probabilities `p x + q x = 1`, the weight-ratio solution satisfies
`h x = p x * h (x+1) + q x * h (x-1)` on the interior. -/
@[zil_level physical_theorem]
theorem dirichletSolution_harmonic_prob {p q : ℕ → ℝ} (hp : ∀ k, 0 < p k)
    (N : ℕ) {x : ℕ} (hx : 1 ≤ x) (hpq : p x + q x = 1) :
    dirichletSolution p q N x =
      p x * dirichletSolution p q N (x + 1) +
        q x * dirichletSolution p q N (x - 1) := by
  have h := dirichletSolution_harmonic hp (q := q) N hx
  linear_combination (-1 : ℝ) * h - dirichletSolution p q N x * hpq

/-- **Uniqueness of the Dirichlet solution**: any `g` with `g 0 = 0`,
`g N = 1`, satisfying the interior flux balance
`p x * (g (x+1) - g x) = q x * (g x - g (x-1))` for `1 ≤ x < N`, agrees with
the weight-ratio solution at every site `x ≤ N`. The discrete Dirichlet
problem of the birth-death generator is exactly solvable and rigid. -/
@[zil_level physical_theorem]
theorem dirichletSolution_unique {p q : ℕ → ℝ} (hp : ∀ k, 0 < p k)
    (hq : ∀ k, 0 < q k) {N : ℕ} (hN : 0 < N) (g : ℕ → ℝ)
    (hg0 : g 0 = 0) (hgN : g N = 1)
    (hharm : ∀ x, 1 ≤ x → x < N →
      p x * (g (x + 1) - g x) = q x * (g x - g (x - 1)))
    {x : ℕ} (hx : x ≤ N) :
    g x = dirichletSolution p q N x := by
  set D := ∑ k ∈ Finset.range N, pathWeight p q k with hD
  have hDpos : 0 < D :=
    Finset.sum_pos (fun k _ => pathWeight_pos hp hq k)
      (Finset.nonempty_range_iff.mpr hN.ne')
  -- the increments of g are proportional to the path weights
  have hincr : ∀ z, z < N → g (z + 1) - g z = (g 1 - g 0) * pathWeight p q z := by
    intro z
    induction z with
    | zero =>
        intro _
        have h0 : pathWeight p q 0 = 1 := rfl
        rw [h0, mul_one]
    | succ w ih =>
        intro hwN
        have hw : w < N := Nat.lt_of_succ_lt hwN
        have hprev := ih hw
        have hflux := hharm (w + 1) (Nat.le_add_left 1 w) hwN
        have hsimp : w + 1 - 1 = w := by omega
        rw [hsimp] at hflux
        have hpne := (hp (w + 1)).ne'
        have hstep : g (w + 1 + 1) - g (w + 1) =
            (g (w + 1) - g w) * (q (w + 1) / p (w + 1)) := by
          field_simp
          linarith [hflux]
        rw [hstep, hprev]
        show _ = (g 1 - g 0) * pathWeight p q (w + 1)
        rw [show pathWeight p q (w + 1) =
          pathWeight p q w * (q (w + 1) / p (w + 1)) from rfl]
        ring
  -- summing the increments to N fixes the first increment
  have htel : ∀ z, z ≤ N → g z = (g 1 - g 0) * ∑ k ∈ Finset.range z, pathWeight p q k := by
    intro z
    induction z with
    | zero => intro _; simp [hg0]
    | succ w ih =>
        intro hwN
        have hw : w ≤ N := Nat.le_of_succ_le hwN
        have hwlt : w < N := hwN
        rw [Finset.sum_range_succ, mul_add, ← ih hw]
        have hw2 := hincr w hwlt
        linarith
  have hfirst : (g 1 - g 0) * D = 1 := by
    have hNval := htel N le_rfl
    rw [hgN, ← hD] at hNval
    linarith
  have hval := htel x hx
  unfold dirichletSolution
  rw [← hD, hval]
  have hDne := hDpos.ne'
  field_simp
  linear_combination (∑ k ∈ Finset.range x, pathWeight p q k) * hfirst

/-- **Detailed balance telescopes the path weights to Gibbs factors**: if
`q k / p k = exp (β * (V k - V (k-1)))` for `1 ≤ k` - detailed balance with
respect to the Gibbs measure of the potential `V` - then
`γ x = exp (β * (V x - V 0))`. -/
@[zil_level physical_theorem]
theorem pathWeight_eq_exp {p q : ℕ → ℝ} {β : ℝ} {V : ℕ → ℝ}
    (hr : ∀ k, 1 ≤ k → q k / p k = Real.exp (β * (V k - V (k - 1)))) :
    ∀ x, pathWeight p q x = Real.exp (β * (V x - V 0))
  | 0 => by simp [pathWeight]
  | x + 1 => by
      have hprev := pathWeight_eq_exp hr x
      have hstep := hr (x + 1) (Nat.le_add_left 1 x)
      have hsimp : x + 1 - 1 = x := by omega
      rw [hsimp] at hstep
      show pathWeight p q x * (q (x + 1) / p (x + 1)) = _
      rw [hprev, hstep, ← Real.exp_add]
      ring_nf

/-- **The Arrhenius escape bound**: under detailed balance with respect to the
potential `V`, the first step out of the well is exponentially suppressed by
any barrier value on the way: `h 1 ≤ exp (-β * (V m - V 0))` for every site
`m < N`. The exact finite form of the Arrhenius/Kramers barrier factor - a
metastable well is confining exactly as its barrier grows. -/
@[zil_level bridge_theorem]
theorem arrhenius_escape_bound {p q : ℕ → ℝ} {β : ℝ} {V : ℕ → ℝ}
    (hp : ∀ k, 0 < p k) (hq : ∀ k, 0 < q k)
    (hr : ∀ k, 1 ≤ k → q k / p k = Real.exp (β * (V k - V (k - 1))))
    {N : ℕ} {m : ℕ} (hm : m < N) :
    dirichletSolution p q N 1 ≤ Real.exp (-(β * (V m - V 0))) := by
  unfold dirichletSolution
  rw [Finset.sum_range_one]
  have hγ0 : pathWeight p q 0 = 1 := rfl
  rw [hγ0]
  have hterm : Real.exp (β * (V m - V 0)) ≤
      ∑ k ∈ Finset.range N, pathWeight p q k := by
    have hmem : m ∈ Finset.range N := Finset.mem_range.mpr hm
    have hle := Finset.single_le_sum
      (f := fun k => pathWeight p q k)
      (fun k _ => (pathWeight_pos hp hq k).le) hmem
    rw [pathWeight_eq_exp hr m] at hle
    exact hle
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos _) hterm

end Physlib.Thermodynamics.BirthDeathFirstPassage

end

open Physlib.Thermodynamics.BirthDeathFirstPassage in
#physlib_axiom_clean_all [
  pathWeight_pos,
  dirichletSolution_zero,
  dirichletSolution_boundary,
  dirichletSolution_harmonic,
  dirichletSolution_harmonic_prob,
  dirichletSolution_unique,
  pathWeight_eq_exp,
  arrhenius_escape_bound ]

open Physlib.Thermodynamics.BirthDeathFirstPassage in
#physlib_non_vacuous_all [
  pathWeight_pos,
  dirichletSolution_boundary,
  dirichletSolution_harmonic,
  dirichletSolution_harmonic_prob,
  dirichletSolution_unique,
  pathWeight_eq_exp,
  arrhenius_escape_bound ]

/- ZIL-BEGIN -/

zil attach Physlib.Thermodynamics.BirthDeathFirstPassage.dirichletSolution_harmonic where
  supported_by @ "lean:ProbDistribution.normalized",
  formalizes @ "claim:the-weight-ratio-formula-solves-the-discrete-dirichlet-problem-of-the-birth-death-generator",
  epistemic_status @ "consistency-identity"

zil attach Physlib.Thermodynamics.BirthDeathFirstPassage.dirichletSolution_harmonic_prob where
  supported_by @ "lean:Physlib.Thermodynamics.BirthDeathFirstPassage.dirichletSolution_harmonic",
  formalizes @ "claim:with-normalized-probabilities-the-solution-satisfies-the-gamblers-ruin-harmonic-identity",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-probabilistic-hitting-time-reading-is-standard-but-no-markov-chain-is-constructed-here"

zil attach Physlib.Thermodynamics.BirthDeathFirstPassage.dirichletSolution_unique where
  supported_by @ "lean:Physlib.Thermodynamics.BirthDeathFirstPassage.pathWeight_pos",
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-discrete-dirichlet-problem-of-the-birth-death-chain-is-exactly-solvable-and-rigid",
  epistemic_status @ "consistency-identity"

zil attach Physlib.Thermodynamics.BirthDeathFirstPassage.pathWeight_eq_exp where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:detailed-balance-telescopes-first-passage-path-weights-to-gibbs-factors",
  epistemic_status @ "consistency-identity"

zil attach Physlib.Thermodynamics.BirthDeathFirstPassage.arrhenius_escape_bound where
  formalizes @ "claim:barrier-escape-is-exponentially-suppressed-by-the-gibbs-factor-of-the-barrier",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:kramers-1940-brownian-motion-in-a-field-of-force-and-the-diffusion-model-of-chemical-reactions",
  caveat @ "claim:an-exact-finite-bound-on-the-dirichlet-solution-not-a-rate-asymptotics-statement"

zil_file_contract physlib.birthDeathFirstPassage where
  promises "The exact identity layer of one-dimensional metastability: the weight-ratio formula solves the discrete Dirichlet problem of the birth-death generator with absorbing and target boundaries, uniquely; detailed balance telescopes its path weights to Gibbs factors of the potential; and the first step out of a well is exponentially suppressed by any barrier value - the exact finite Arrhenius bound."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Real.exp", "lean:Finset.sum_range_succ",
    "lean:Finset.single_le_sum"]
  forbids_substitutes ["a Markov-chain hitting-probability construction with stopping times and measures",
    "a Kramers rate asymptotics or spectral-gap statement",
    "continuum diffusion or Fokker-Planck escape theory"]
  witnessed_by [
    Physlib.Thermodynamics.BirthDeathFirstPassage.dirichletSolution_harmonic,
    Physlib.Thermodynamics.BirthDeathFirstPassage.dirichletSolution_harmonic_prob,
    Physlib.Thermodynamics.BirthDeathFirstPassage.dirichletSolution_unique,
    Physlib.Thermodynamics.BirthDeathFirstPassage.pathWeight_eq_exp,
    Physlib.Thermodynamics.BirthDeathFirstPassage.arrhenius_escape_bound ]

/- ZIL-END -/

#zil_formalization_lint physlib.birthDeathFirstPassage
