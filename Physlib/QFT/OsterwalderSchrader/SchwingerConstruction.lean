/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Physlib.QuantumMechanics.ComplexAction.HistoryHilbertGramIsomorphism

/-!
# Constructing the Osterwalder–Schrader measure from OS data: the Schwinger functional

The construction direction of the bijection between OS measures and OS data —
§§2.1–2.2 of Lang–Liegener–Thiemann, *Hamiltonian renormalisation I: derivation from
Osterwalder–Schrader reconstruction*, through Eq. 2.26.

**The input structures** (§2.1).  `WeylSystem` records the sharp-time Weyl elements
`w[f]` as bounded operators together with the label conjugation of the Weyl
relations (Eq. 2.2): `(w[f])* = w[f*]`.  `OSData` records the triple
`(ℋ, Ω, H)` through the properties §2.2 actually uses: a unit cyclic vacuum and the
Euclidian transfer semigroup `β ↦ e^{−βH}` (Eq. 2.4) — self-adjoint, a semigroup,
contractive on `β ≥ 0` (the shadow of `H ≥ 0`), and fixing the vacuum (`HΩ = 0`).

**The Schwinger generating functional** (§2.2).  `histOp` builds the time-ordered
operator word `e^{−(β₁−prev)H} w[f₁] e^{−(β₂−β₁)H} w[f₂] ⋯` of Eqs. 2.5/2.7,
`historyVector` applies it to the vacuum (the vectors of Eq. 2.24), and `schwinger`
is the `N`-point Schwinger generating functional
`S((f_N,β_N),…,(f_1,β_1)) = ⟨Ω, w[f₁] e^{−(β₂−β₁)H} ⋯ w[f_N] Ω⟩` (Eqs. 2.5, 2.12) —
the cylindrical data of the heat-kernel ("Wiener") measure (Eq. 2.7).  Proved here:

* `schwinger_nil` — the normalisation `μ(Γ) = 1` (below Eq. 2.7), from `HΩ = 0` and
  the unit vacuum.
* `historyVector_unit_singleton`, `histOp_unit_insert` — inserting a time slot
  whose Weyl element is the identity does not change the history word: "adding time
  slots with `1_ℋ` insertions does not affect the answer", the mechanism of
  cylindrical consistency of Eq. 2.7.
* `schwinger_shift` — **time translation invariance** (Eqs. 2.25–2.26): the
  functional depends only on the time differences, so the flow `𝒰(s) W[F] = W[T_sF]`
  preserves it.
* `schwinger_reflect_single`, `schwinger_reflect_pair` — **time reflection
  invariance** (Eqs. 2.20–2.21) in the one- and two-slot generating cases:
  `conj ∘ S ∘ θ = S ∘ (·)*`, by moving the self-adjoint transfer operators and the
  Weyl adjoints across the inner product.  The general finite sequence follows by
  the same adjoint-moving computation applied slot by slot (Eq. 2.21) and is not yet
  formalized.
* `schwinger_doubled_single` — the **reflection-positivity pairing** (Eqs. 2.22–2.24)
  in the single-time case treated explicitly by the paper's method: the doubled
  matrix element `⟨Ω, w[f*] e^{−(β+γ)H} w[g] Ω⟩` is the Gram element
  `⟨e^{−βH} w[f] Ω, e^{−γH} w[g] Ω⟩` of history vectors.
* `reflectionPositive_gram` — hence reflection positivity (Eq. 2.22): sesquilinear
  combinations of history vectors form a positive kernel, Eq. 2.24's "manifestly
  non-negative" `‖Σ_I z_I e^{−β₁ᴵH} w[f₁ᴵ] ⋯ Ω‖²` — by the Gram positivity lemma of
  the decoherence-functional arc
  (`HistoryHilbertGramIsomorphism.gram_posSemidef`).

**Scope.**  The GNS/Gelfand realization `ℋ ≅ L₂(Δ(𝔅), dν)` of §2.1 (Eqs. 2.1–2.2)
is recorded through the input structures only (the repository's
`AlgebraicQFT.StarAlgebraGNSFormCommutant` and the Reeh–Schlieder modules provide
the GNS side); the Wightman functional and its analytic continuation
(Eqs. 2.3–2.4) motivate the transfer-semigroup field and are not formalized as
statements; the σ-additive extension of the cylindrical data to the measure `μ` on
`Γ` (Eqs. 2.6–2.11, 2.13–2.18), Nelson–Symanzik positivity (Eq. 2.8, appendix B),
and the history Hilbert space `ℋ' = L₂(Γ, dμ)` (Eq. 2.19) are measure-theoretic
future material.  The reconstruction direction §2.3 (from Eq. 2.27 on) is the
companion module `OsterwalderSchrader.ReflectionPositivity`.

## References

* T. Lang, K. Liegener, T. Thiemann, *Hamiltonian renormalisation I: derivation from
  Osterwalder–Schrader reconstruction*, Class. Quantum Grav. **35** (2018) 245011,
  doi:10.1088/1361-6382/aaec56, §§2.1–2.2.
-/

set_option autoImplicit false

open Complex ContinuousLinearMap
open Physlib.QuantumMechanics.ComplexAction.HistoryHilbertGramIsomorphism
open scoped ComplexInnerProductSpace

@[expose] public section

namespace Physlib.QFT.OsterwalderSchrader

variable {ι : Type*} {ℋ : Type*}
  [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

/-! ## A. The input structures: sharp-time Weyl system and OS data -/

/-- **Sharp-time Weyl system** (§2.1, Eq. 2.2): bounded Weyl elements `w[f]` on the
OS Hilbert space, labelled by smearing data `ι`, with the label conjugation
realising `(w[f])* = w[f*]` — the part of the Weyl relations Eq. 2.2 used by the
Schwinger construction.  The product relations of Eq. 2.2 (with their structure
constants `z_α` and composition functions) are not needed below Eq. 2.26 and are
future material. -/
structure WeylSystem (ι : Type*) (ℋ : Type*) [NormedAddCommGroup ℋ]
    [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] where
  /-- The Weyl element `w[f]` at sharp time zero. -/
  weyl : ι → ℋ →L[ℂ] ℋ
  /-- The label conjugation `f ↦ f*` of Eq. 2.2 (for a free scalar field,
  `f* = −f`). -/
  conjLabel : ι → ι
  /-- `(w[f])* = w[f*]` (Eq. 2.2, first relation). -/
  adjoint_weyl : ∀ f, adjoint (weyl f) = weyl (conjLabel f)

/-- **Osterwalder–Schrader data** (§2.1, Eqs. 2.1 and 2.4): a unit vacuum vector and
the Euclidian transfer semigroup `β ↦ e^{−βH}` of the positive self-adjoint
Hamiltonian — self-adjoint, multiplicative on non-negative times, contractive
(Eq. 2.4: "bounded in operator norm by unity thanks to the positivity of `H`"), and
fixing the vacuum (`HΩ = 0`). -/
structure OSData (ℋ : Type*) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [CompleteSpace ℋ] where
  /-- The vacuum vector `Ω`. -/
  vacuum : ℋ
  /-- The vacuum is a unit vector. -/
  norm_vacuum : ‖vacuum‖ = 1
  /-- The Euclidian transfer semigroup `β ↦ e^{−βH}` (Eq. 2.4). -/
  transfer : ℝ → ℋ →L[ℂ] ℋ
  /-- `e^{−0·H} = 1`. -/
  transfer_zero : transfer 0 = 1
  /-- The semigroup law on non-negative times. -/
  transfer_add : ∀ {β γ : ℝ}, 0 ≤ β → 0 ≤ γ →
    transfer (β + γ) = transfer β ∘L transfer γ
  /-- `e^{−βH}` is self-adjoint. -/
  transfer_selfAdjoint : ∀ β, IsSelfAdjoint (transfer β)
  /-- Eq. 2.4: the transfer operators are contractions for `β ≥ 0` — the shadow of
  `H ≥ 0`. -/
  transfer_contraction : ∀ {β : ℝ}, 0 ≤ β → ∀ ψ : ℋ, ‖transfer β ψ‖ ≤ ‖ψ‖
  /-- `HΩ = 0`: the transfer semigroup fixes the vacuum. -/
  transfer_vacuum : ∀ β, transfer β vacuum = vacuum

namespace OSData

variable (D : OSData ℋ) (W : WeylSystem ι ℋ)

/-! ## B. The Schwinger generating functional -/

/-- The time-ordered **history operator word** of Eqs. 2.5/2.7/2.24,
`histOp prev [(f₁,β₁),…,(f_N,β_N)] = e^{−(β₁−prev)H} w[f₁] e^{−(β₂−β₁)H} w[f₂] ⋯`,
for a time-ordered list `prev ≤ β₁ ≤ … ≤ β_N`. -/
noncomputable def histOp : ℝ → List (ι × ℝ) → (ℋ →L[ℂ] ℋ)
  | _, [] => 1
  | prev, (f, β) :: L => D.transfer (β - prev) ∘L (W.weyl f ∘L histOp β L)

@[simp] lemma histOp_nil (prev : ℝ) : D.histOp W prev [] = 1 := rfl

lemma histOp_cons (prev β : ℝ) (f : ι) (L : List (ι × ℝ)) :
    D.histOp W prev ((f, β) :: L)
      = D.transfer (β - prev) ∘L (W.weyl f ∘L D.histOp W β L) := rfl

/-- The **history vector** (the vectors of Eq. 2.24 and the class representatives of
Eq. 2.48): the history word applied to the vacuum,
`e^{−(β₁−prev)H} w[f₁] ⋯ w[f_N] Ω`. -/
noncomputable def historyVector (prev : ℝ) (L : List (ι × ℝ)) : ℋ :=
  D.histOp W prev L D.vacuum

/-- The **Schwinger generating functional** (Eqs. 2.5, 2.12):
`S((f_k, β_k)_k) = ⟨Ω, w[f₁] e^{−(β₂−β₁)H} w[f₂] ⋯ w[f_N] Ω⟩` for time-ordered
sequences — the cylindrical data of the heat-kernel measure (Eq. 2.7). -/
noncomputable def schwinger : List (ι × ℝ) → ℂ
  | [] => ⟪D.vacuum, D.vacuum⟫
  | (f, β) :: L => ⟪D.vacuum, W.weyl f (D.historyVector W β L)⟫

/-- **Normalisation** (below Eq. 2.7): `μ(Γ) = 1`, from `HΩ = 0` and the unit
vacuum. -/
@[simp] lemma schwinger_nil : D.schwinger W [] = 1 := by
  show (⟪D.vacuum, D.vacuum⟫ : ℂ) = 1
  rw [inner_self_eq_norm_sq_to_K, D.norm_vacuum]
  norm_num

/-! ## C. Cylindrical consistency: unit insertions are invisible -/

/-- A single time slot whose Weyl element is the identity leaves the vacuum untouched. -/
lemma historyVector_unit_singleton {e : ι} (he : W.weyl e = 1) (prev β : ℝ) :
    D.historyVector W prev [(e, β)] = D.vacuum := by
  simp [historyVector, histOp, he, D.transfer_vacuum]

/-- **Unit insertions are invisible** (the cylindrical-consistency mechanism below
Eq. 2.7): inserting a time slot with the unit Weyl element between ordered times
merges the two adjacent transfer factors by the semigroup law, leaving the history
word unchanged. -/
lemma histOp_unit_insert {e : ι} (he : W.weyl e = 1) {prev β γ : ℝ}
    (h₁ : prev ≤ β) (h₂ : β ≤ γ) (g : ι) (L : List (ι × ℝ)) :
    D.histOp W prev ((e, β) :: (g, γ) :: L) = D.histOp W prev ((g, γ) :: L) := by
  ext x
  show D.transfer (β - prev) ((W.weyl e)
      ((D.transfer (γ - β)) ((W.weyl g) (D.histOp W γ L x))))
    = (D.transfer (γ - prev)) ((W.weyl g) (D.histOp W γ L x))
  rw [he, show γ - prev = (β - prev) + (γ - β) from by ring,
    D.transfer_add (by linarith) (by linarith)]
  simp

/-! ## D. Time translation invariance -/

/-- The time translation `T_s` on smearing sequences (Eq. 2.25): every sharp time is
shifted by `s`. -/
def shiftTimes (s : ℝ) (L : List (ι × ℝ)) : List (ι × ℝ) :=
  L.map fun p => (p.1, p.2 + s)

/-- The history word depends only on the time differences: shifting all times and
the reference time leaves it unchanged. -/
lemma histOp_shiftTimes (s : ℝ) :
    ∀ (L : List (ι × ℝ)) (prev : ℝ),
      D.histOp W (prev + s) (shiftTimes s L) = D.histOp W prev L := by
  intro L
  induction L with
  | nil => intro prev; rfl
  | cons p L ih =>
    intro prev
    obtain ⟨f, β⟩ := p
    show D.transfer (β + s - (prev + s)) ∘L (W.weyl f ∘L D.histOp W (β + s) (shiftTimes s L))
      = D.transfer (β - prev) ∘L (W.weyl f ∘L D.histOp W β L)
    rw [show β + s - (prev + s) = β - prev from by ring]
    have := ih β
    rw [this]

/-- **Time translation invariance of the Schwinger functional** (Eq. 2.26):
`μ(𝒰(s)·W[F]) = μ(W[F])`, since only the differences `β_k − β_l` enter. -/
theorem schwinger_shiftTimes (s : ℝ) (L : List (ι × ℝ)) :
    D.schwinger W (shiftTimes s L) = D.schwinger W L := by
  cases L with
  | nil => rfl
  | cons p L =>
    obtain ⟨f, β⟩ := p
    show (⟪D.vacuum, W.weyl f (D.historyVector W (β + s) (shiftTimes s L))⟫ : ℂ)
      = ⟪D.vacuum, W.weyl f (D.historyVector W β L)⟫
    rw [historyVector, D.histOp_shiftTimes W s L β]
    rfl

/-! ## E. Time reflection -/

/-- Time reflection `θ` on smearing sequences (Eq. 2.20): every sharp time is
negated and the sequence re-sorted to ascending order. -/
def reflectTimes (L : List (ι × ℝ)) : List (ι × ℝ) :=
  (L.map fun p => (p.1, -p.2)).reverse

/-- The label conjugation `F ↦ F*` applied slotwise. -/
def conjLabels (W : WeylSystem ι ℋ) (L : List (ι × ℝ)) : List (ι × ℝ) :=
  L.map fun p => (W.conjLabel p.1, p.2)

/-- **Reflection identity, one slot** (Eq. 2.21 for `N = 1`):
`conj (S ∘ θ) = S ∘ (·)*`. -/
theorem schwinger_reflect_single (f : ι) (β : ℝ) :
    (starRingEnd ℂ) (D.schwinger W (reflectTimes [(f, β)]))
      = D.schwinger W (conjLabels W [(f, β)]) := by
  show (starRingEnd ℂ) (⟪D.vacuum, W.weyl f (D.historyVector W (-β) [])⟫ : ℂ)
    = ⟪D.vacuum, W.weyl (W.conjLabel f) (D.historyVector W β [])⟫
  show (starRingEnd ℂ) (⟪D.vacuum, W.weyl f D.vacuum⟫ : ℂ)
    = ⟪D.vacuum, W.weyl (W.conjLabel f) D.vacuum⟫
  rw [inner_conj_symm, ← W.adjoint_weyl, adjoint_inner_right]

/-- **Reflection identity, two slots** (Eq. 2.21 for `N = 2`): for `β ≤ γ`,
`conj S((g,−γ),(f,−β)) = S((f*,β),(g*,γ))` — the self-adjoint transfer operator and
the Weyl adjoints move across the inner product, reversing the word.  The general
finite sequence follows by the same computation applied slot by slot. -/
theorem schwinger_reflect_pair (f g : ι) (β γ : ℝ) :
    (starRingEnd ℂ) (D.schwinger W (reflectTimes [(f, β), (g, γ)]))
      = D.schwinger W (conjLabels W [(f, β), (g, γ)]) := by
  show (starRingEnd ℂ)
      (⟪D.vacuum, W.weyl g (D.transfer (-β - -γ) (W.weyl f D.vacuum))⟫ : ℂ)
    = ⟪D.vacuum, W.weyl (W.conjLabel f)
        (D.transfer (γ - β) (W.weyl (W.conjLabel g) D.vacuum))⟫
  rw [inner_conj_symm, show -β - -γ = γ - β from by ring]
  calc (⟪W.weyl g (D.transfer (γ - β) (W.weyl f D.vacuum)), D.vacuum⟫ : ℂ)
      = ⟪D.transfer (γ - β) (W.weyl f D.vacuum), adjoint (W.weyl g) D.vacuum⟫ :=
        (adjoint_inner_right (W.weyl g) _ _).symm
    _ = ⟪W.weyl f D.vacuum,
          D.transfer (γ - β) (adjoint (W.weyl g) D.vacuum)⟫ :=
        (D.transfer_selfAdjoint (γ - β)).isSymmetric _ _
    _ = ⟪D.vacuum, adjoint (W.weyl f)
          (D.transfer (γ - β) (adjoint (W.weyl g) D.vacuum))⟫ :=
        (adjoint_inner_right (W.weyl f) _ _).symm
    _ = ⟪D.vacuum, W.weyl (W.conjLabel f)
          (D.transfer (γ - β) (W.weyl (W.conjLabel g) D.vacuum))⟫ := by
        rw [W.adjoint_weyl, W.adjoint_weyl]

/-! ## F. Reflection positivity -/

/-- **The reflection-positivity pairing, single-time sequences** (Eqs. 2.22–2.24 in
the case each sequence has a single sharp time, the case the paper's method
treats explicitly): the doubled matrix element with the reflected first argument is
the Gram element of the history vectors,
`⟨Ω, w[f*] e^{−(β+γ)H} w[g] Ω⟩ = ⟨e^{−βH} w[f] Ω, e^{−γH} w[g] Ω⟩`. -/
theorem schwinger_doubled_single (f g : ι) {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) :
    D.schwinger W [(W.conjLabel f, -β), (g, γ)]
      = ⟪D.historyVector W 0 [(f, β)], D.historyVector W 0 [(g, γ)]⟫ := by
  show (⟪D.vacuum, W.weyl (W.conjLabel f)
      (D.transfer (γ - -β) (W.weyl g D.vacuum))⟫ : ℂ)
    = ⟪D.transfer (β - 0) (W.weyl f D.vacuum),
        D.transfer (γ - 0) (W.weyl g D.vacuum)⟫
  rw [show β - 0 = β from by ring, show γ - 0 = γ from by ring]
  calc (⟪D.vacuum, W.weyl (W.conjLabel f)
        (D.transfer (γ - -β) (W.weyl g D.vacuum))⟫ : ℂ)
      = ⟪D.vacuum, adjoint (W.weyl f)
          (D.transfer (γ - -β) (W.weyl g D.vacuum))⟫ := by
        rw [W.adjoint_weyl]
    _ = ⟪W.weyl f D.vacuum, D.transfer (γ - -β) (W.weyl g D.vacuum)⟫ :=
        adjoint_inner_right (W.weyl f) _ _
    _ = ⟪W.weyl f D.vacuum, D.transfer β (D.transfer γ (W.weyl g D.vacuum))⟫ := by
        rw [show γ - -β = β + γ from by ring, D.transfer_add hβ hγ]
        rfl
    _ = ⟪D.transfer β (W.weyl f D.vacuum), D.transfer γ (W.weyl g D.vacuum)⟫ :=
        ((D.transfer_selfAdjoint β).isSymmetric _ _).symm

/-- **Reflection positivity** (Eqs. 2.22, 2.24): sesquilinear combinations of
history vectors of positive-time sequences form a positive kernel —
`Σ_{I,J} conj(z_I) z_J ⟨Ξ_I, Ξ_J⟩ = ‖Σ_I z_I Ξ_I‖² ≥ 0`, Eq. 2.24's "manifestly
non-negative".  This is Gram positivity, supplied by the decoherence-functional arc
(`HistoryHilbertGramIsomorphism.gram_posSemidef`). -/
theorem reflectionPositive_gram {κ : Type*} (F : κ → List (ι × ℝ))
    (s : Finset κ) (z : κ → ℂ) :
    0 ≤ (∑ I ∈ s, ∑ J ∈ s, (starRingEnd ℂ) (z I) * z J *
      ⟪D.historyVector W 0 (F I), D.historyVector W 0 (F J)⟫).re :=
  gram_posSemidef (fun I => D.historyVector W 0 (F I)) s z

end OSData

end Physlib.QFT.OsterwalderSchrader

end
