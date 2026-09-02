/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Order
meta import Zil

/-!
# Orlicz operator ideals of nuclear and approximable operators (Castillo–Kaballo)

Formalizes the ideal-theoretic core of *S. Castillo, W. Kaballo, "On the Decomposition Theorem for
Meromorphic Fredholm Resolvents", Integr. Equ. Oper. Theory 18 (1994) 78–87* — the **Orlicz operator
ideals** `N_φ` (φ-nuclear) and `S_φ` (φ-approximable) built from an Orlicz function `φ` and the
singular / approximation numbers of an operator.

The membership condition of both ideals is the same summability of `φ` applied to a scale of numbers
(the nuclear coefficients `∑ φ(|μ_j|) < ∞`, resp. the approximation numbers `∑ φ(a_k(T)) < ∞`), so at
the level of the underlying nonnegative number sequence the ideals are one object. This module carries
that ideal structure — the Orlicz function, its **subadditivity**, the example `φ_p(t) = t^p`, and the
two defining properties of an operator ideal (closure under **domination** by singular numbers and
under **addition**) — on the sequence of characteristic numbers, taking the operator-theoretic
realization (approximation numbers, the tensor factorization) as cited.

This is the abstract framework behind the **nuclearity conditions** of algebraic QFT already in the
repository (`Mathematics/Nuclear/`, `SchwartzNuclear/`, the split property): the modular heat operator
`e^{−βH}` lies in an Orlicz operator ideal, and its "nuclearity index" is exactly `∑ φ(a_k)`.

* `OrliczFunction` — an increasing concave function on `[0,∞)` with `φ(0) = 0`.
* `OrliczFunction.subadditive` — `φ(s+t) ≤ φ(s) + φ(t)`: concavity through the origin gives
  subadditivity, the property making `∑ φ(|·|)` a metric on the ideal.
* `orliczPow` — the standard example `φ_p(t) = t^p` (`0 < p ≤ 1`) is an Orlicz function.
* `inOrliczIdeal φ a` — the ideal membership `∑ φ(a_k) < ∞` of a characteristic-number sequence.
* `inOrliczIdeal_mono` — **domination**: a sequence dominated by an ideal member is an ideal member
  (`S_φ ⊆ N_φ`, and the Weyl-eigenvalue consequence `∑ φ(|λ_k(T)|) < ∞`).
* `inOrliczIdeal_add` — the ideal is closed under addition (via subadditivity): `N_φ`, `S_φ` are
  vector spaces.
-/

set_option autoImplicit false

open scoped Topology

@[expose] public section

namespace Physlib.Mathematics.Nuclear.OrliczOperatorIdeals

/-- An **Orlicz function**: increasing on `[0,∞)`, concave on `[0,∞)`, with `φ(0) = 0`. These define
the Orlicz operator ideals `N_φ` (φ-nuclear) and `S_φ` (φ-approximable). -/
structure OrliczFunction where
  /-- The underlying function. -/
  toFun : ℝ → ℝ
  /-- `φ(0) = 0`. -/
  map_zero : toFun 0 = 0
  /-- `φ` is increasing on `[0,∞)`. -/
  mono : MonotoneOn toFun (Set.Ici 0)
  /-- `φ` is concave on `[0,∞)`. -/
  concave : ConcaveOn ℝ (Set.Ici 0) toFun

namespace OrliczFunction

variable (φ : OrliczFunction)

/-- An Orlicz function is nonnegative on `[0,∞)`: `0 = φ(0) ≤ φ(t)` by monotonicity. -/
theorem nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ φ.toFun t := by
  have hmt := φ.mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  rwa [φ.map_zero] at hmt

/-- **[Subadditivity]** `φ(s+t) ≤ φ(s) + φ(t)` for `s, t ≥ 0`. Concavity through the origin
(`φ(0) = 0`): writing `s = (s/(s+t))·(s+t) + (t/(s+t))·0` and symmetrically for `t`, the concavity
inequality gives `(s/(s+t))·φ(s+t) ≤ φ(s)` and `(t/(s+t))·φ(s+t) ≤ φ(t)`; summing (the weights add to
`1`) yields `φ(s+t) ≤ φ(s) + φ(t)`. This is the property that makes the Orlicz modular `∑ φ(|·|)` a
metric — the (F)-norm on the ideals `N_φ`, `S_φ`. -/
theorem subadditive {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    φ.toFun (s + t) ≤ φ.toFun s + φ.toFun t := by
  rcases eq_or_lt_of_le (add_nonneg hs ht) with hst | hst
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    rw [hs0, ht0, add_zero, φ.map_zero]; linarith [φ.map_zero]
  · have hune : s + t ≠ 0 := hst.ne'
    have hmu : (s + t) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hst.le
    have hm0 : (0 : ℝ) ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
    have ha : 0 ≤ s / (s + t) := div_nonneg hs hst.le
    have hb : 0 ≤ t / (s + t) := div_nonneg ht hst.le
    have hab : s / (s + t) + t / (s + t) = 1 := by field_simp
    have hba : t / (s + t) + s / (s + t) = 1 := by rw [add_comm]; exact hab
    have h1 := φ.concave.2 hmu hm0 ha hb hab
    have h2 := φ.concave.2 hmu hm0 hb ha hba
    simp only [smul_eq_mul, φ.map_zero, mul_zero, add_zero] at h1 h2
    have es : s / (s + t) * (s + t) = s := by field_simp
    have et : t / (s + t) * (s + t) = t := by field_simp
    rw [es] at h1
    rw [et] at h2
    have hsum : (s / (s + t) + t / (s + t)) * φ.toFun (s + t) ≤ φ.toFun s + φ.toFun t := by
      rw [add_mul]; linarith
    rwa [hab, one_mul] at hsum

end OrliczFunction

/-- The standard Orlicz function `φ_p(t) = t^p` for `0 < p ≤ 1` — increasing and concave on `[0,∞)`
with `φ_p(0) = 0` (the `p`-approximable / `p`-nuclear scale). -/
noncomputable def orliczPow {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : OrliczFunction where
  toFun := fun t => t ^ p
  map_zero := Real.zero_rpow hp0.ne'
  mono := fun _ ha _ _ hxy => Real.rpow_le_rpow (Set.mem_Ici.mp ha) hxy hp0.le
  concave := Real.concaveOn_rpow hp0.le hp1

/-- **Membership in the Orlicz operator ideal.** The characteristic-number sequence `a` (the nuclear
coefficients `|μ_k|`, or the approximation numbers `a_k(T)`) lies in the ideal `N_φ = S_φ` iff
`∑ φ(a_k) < ∞`. -/
def inOrliczIdeal (φ : OrliczFunction) (a : ℕ → ℝ) : Prop := Summable (fun k => φ.toFun (a k))

/-- **[Domination — the operator-ideal property, `S_φ ⊆ N_φ`]** A nonnegative sequence pointwise
dominated by an ideal member is itself an ideal member: `∑ φ(a_k) ≤ ∑ φ(b_k) < ∞` by monotonicity of
`φ`. Since the approximation numbers dominate the eigenvalue moduli (Weyl's inequality), this gives
the eigenvalue summability `∑ φ(|λ_k(T)|) < ∞` for `T ∈ N_φ`, and the always-true inclusion
`S_φ ⊆ N_φ`. -/
theorem inOrliczIdeal_mono (φ : OrliczFunction) {a b : ℕ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (hab : ∀ k, a k ≤ b k) (hb : inOrliczIdeal φ b) : inOrliczIdeal φ a :=
  Summable.of_nonneg_of_le (fun k => φ.nonneg (ha0 k))
    (fun k => φ.mono (Set.mem_Ici.mpr (ha0 k))
      (Set.mem_Ici.mpr (le_trans (ha0 k) (hab k))) (hab k)) hb

/-- **[The ideal is closed under addition — a vector space]** For nonnegative sequences, the sum of
two ideal members is an ideal member: `∑ φ(a_k + b_k) ≤ ∑ (φ(a_k) + φ(b_k)) < ∞` by subadditivity.
Hence `N_φ` and `S_φ` are vector spaces of operators. -/
theorem inOrliczIdeal_add (φ : OrliczFunction) {a b : ℕ → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (hb0 : ∀ k, 0 ≤ b k) (ha : inOrliczIdeal φ a) (hb : inOrliczIdeal φ b) :
    inOrliczIdeal φ (fun k => a k + b k) :=
  Summable.of_nonneg_of_le (fun k => φ.nonneg (add_nonneg (ha0 k) (hb0 k)))
    (fun k => φ.subadditive (ha0 k) (hb0 k)) (ha.add hb)

end Physlib.Mathematics.Nuclear.OrliczOperatorIdeals

end

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.OrliczFunction.subadditive where
  formalizes @ "claim:an-orlicz-function-concave-through-the-origin-is-subadditive-so-the-orlicz-modular-is-a-metric-on-the-operator-ideal",
  supported_by @ "paper:castillo-kaballo-orlicz-operator-ideals-meromorphic-fredholm-resolvents"

zil attach Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.inOrliczIdeal_mono where
  formalizes @ "claim:a-characteristic-number-sequence-dominated-by-an-orlicz-ideal-member-is-itself-an-ideal-member-domination-s-phi-subset-n-phi-and-the-weyl-eigenvalue-summability",
  supported_by @ "paper:castillo-kaballo-orlicz-operator-ideals-meromorphic-fredholm-resolvents",
  caveat @ "claim:the-operator-theoretic-realization-approximation-numbers-and-the-tensor-factorization-is-taken-as-cited"

zil attach Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.inOrliczIdeal_add where
  supported_by @ "lean:Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.OrliczFunction.subadditive",
  formalizes @ "claim:the-orlicz-operator-ideal-is-closed-under-addition-a-vector-space-via-subadditivity",
  requires @ "claim:an-orlicz-function-concave-through-the-origin-is-subadditive-so-the-orlicz-modular-is-a-metric-on-the-operator-ideal"

zil_file_contract physlib.orliczOperatorIdeals where
  promises "The ideal-theoretic core of the Castillo-Kaballo Orlicz operator ideals N_phi (phi-nuclear) and S_phi (phi-approximable): an Orlicz function is increasing, concave, and vanishes at zero; concavity through the origin makes it subadditive (so the Orlicz modular sum phi(|.|) is a metric, the (F)-norm on the ideal); the standard power example phi_p(t) = t^p (0 < p <= 1) is an Orlicz function; and the ideal membership sum phi(a_k) < infinity of the characteristic-number sequence is closed under domination (S_phi subset N_phi, the Weyl eigenvalue summability) and under addition (the ideal is a vector space). This is the abstract framework for the AQFT nuclearity conditions on the modular heat operator e^{-beta H}."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.OrliczFunction",
    "lean:Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.inOrliczIdeal"]
  forbids_substitutes ["the operator-theoretic approximation numbers, the phi-nuclear tensor representation, and the exponentially galbed embeddings, which are the cited Banach/Frechet-space infrastructure",
    "the meromorphic decomposition theorem itself, only the underlying Orlicz ideal structure of the singular part is carried"]
  witnessed_by [Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.OrliczFunction.nonneg,
    Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.OrliczFunction.subadditive,
    Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.orliczPow,
    Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.inOrliczIdeal_mono,
    Physlib.Mathematics.Nuclear.OrliczOperatorIdeals.inOrliczIdeal_add]

/- ZIL-END -/
