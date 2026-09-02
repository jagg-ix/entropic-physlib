/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Cantor diagonalization: one subsequence `Lᵖ`-convergent at every level

Re-authors the Cantor-diagonal argument of `NavierStokesClean/Galerkin/CantorDiagonal.lean` (which promotes a
Navier–Stokes Galerkin sequence's *per-`T`* `L²`-convergent subsequences to a *single* subsequence convergent
on every `[0,T]`) as a **general, axiom-free** measure-theory lemma. In the source the construction is entangled
with Navier–Stokes trajectory hypotheses and the per-`T` extractor is itself a (partially verified) axiom; here
the extractor is a plain hypothesis, so the diagonalization stands on its own.

`eLpNorm_diagonal_subseq`: given a sequence `u : ℕ → α → E`, a limit `g`, a family of measures `μ : ℕ → …`,
and a **per-level extractor** — for *any* reindexed sequence `v` and level `k`, a subsequence of `v` with
`‖v(ψ ·) − g‖_{L²(μ k)} → 0` — there is one strictly monotone `φ` with `‖u(φ ·) − g‖_{L²(μ k)} → 0` for
*every* `k` simultaneously.

Construction: `iterσ k` composes `k+1` successive extractions (at levels `0,…,k`), and the Cantor diagonal
`σ n = iterσ n n` inherits convergence at every level `j` because its tail `n ≥ j` factors through `iterσ j`
(`iterσ_refines_point`) via a cofinal reindexing. `eLpNorm_diagonal_subseq_of_le` then transports the
conclusion to any measure dominated by some `μ k` (e.g. `volume.restrict (Ioc 0 T)` for real `T`), via
`eLpNorm_mono_measure`.

## References

* J. Simon, Ann. Mat. Pura Appl. 146 (1987) 65 (Aubin–Lions–Simon compactness — the per-level extraction the
  diagonal promotes). Carrier: Mathlib `MeasureTheory.eLpNorm_mono_measure`, `Filter.Tendsto.comp/.congr'`.
-/

set_option autoImplicit false

open MeasureTheory Filter

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LpSubsequenceDiagonalization

variable {α : Type*} [MeasurableSpace α] {E : Type*} [NormedAddCommGroup E]

/-- **[`n ≤ f n` for a strictly monotone `f : ℕ → ℕ`]** — the elementary growth bound driving the diagonal's
cofinality. -/
theorem nat_le_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) : n ≤ f n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (hf (Nat.lt_succ_self n)))

variable (u : ℕ → α → E) (g : α → E) (μ : ℕ → Measure α)
  (hext : ∀ (v : ℕ → α → E) (k : ℕ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    Tendsto (fun n => eLpNorm (fun t => v (ψ n) t - g t) 2 (μ k)) atTop (nhds 0))

/-- The nested extractions: `iterσ 0` extracts `u` at level `0`; `iterσ (k+1)` refines `iterσ k` by extracting
`u ∘ iterσ k` at level `k+1`. -/
noncomputable def iterσ : ℕ → (ℕ → ℕ) :=
  Nat.rec
    (Classical.choose (hext u 0))
    (fun k σk => σk ∘ Classical.choose (hext (fun n => u (σk n)) (k + 1)))

theorem iterσ_succ (k : ℕ) :
    iterσ u g μ hext (k + 1)
      = iterσ u g μ hext k ∘
          Classical.choose (hext (fun n => u (iterσ u g μ hext k n)) (k + 1)) := rfl

theorem iterσ_strictMono (k : ℕ) : StrictMono (iterσ u g μ hext k) := by
  induction k with
  | zero => exact (Classical.choose_spec (hext u 0)).1
  | succ k ih =>
    exact ih.comp (Classical.choose_spec
      (hext (fun n => u (iterσ u g μ hext k n)) (k + 1))).1

/-- `u ∘ iterσ k` converges in `L²(μ k)` — the level-`k` extraction was applied at its top step. -/
theorem iterσ_tendsto_self (k : ℕ) :
    Tendsto (fun n => eLpNorm (fun t => u (iterσ u g μ hext k n) t - g t) 2 (μ k))
      atTop (nhds 0) := by
  cases k with
  | zero => exact (Classical.choose_spec (hext u 0)).2
  | succ k => exact (Classical.choose_spec
      (hext (fun n => u (iterσ u g μ hext k n)) (k + 1))).2

/-- For `j ≤ k`, every value of `iterσ k` equals a value of `iterσ j` at a not-smaller index — the refinement
that lets the diagonal inherit level-`j` convergence. -/
theorem iterσ_refines_point (j : ℕ) :
    ∀ k, j ≤ k → ∀ p, ∃ q, p ≤ q ∧
      iterσ u g μ hext k p = iterσ u g μ hext j q := by
  intro k hjk
  induction k with
  | zero =>
    obtain rfl := Nat.le_zero.mp hjk
    intro p; exact ⟨p, le_rfl, rfl⟩
  | succ k' ih =>
    intro p
    rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
    · exact ⟨p, le_rfl, rfl⟩
    · have hjk' : j ≤ k' := Nat.lt_succ_iff.mp hlt
      have hψ_SM : StrictMono (Classical.choose
          (hext (fun n => u (iterσ u g μ hext k' n)) (k' + 1))) :=
        (Classical.choose_spec (hext (fun n => u (iterσ u g μ hext k' n)) (k' + 1))).1
      obtain ⟨q, hge_q, hq_eq⟩ := ih hjk'
        (Classical.choose (hext (fun n => u (iterσ u g μ hext k' n)) (k' + 1)) p)
      exact ⟨q, (nat_le_of_strictMono hψ_SM p).trans hge_q, hq_eq⟩

/-- The Cantor diagonal `σ n = iterσ n n`. -/
noncomputable def σDiag : ℕ → ℕ := fun n => iterσ u g μ hext n n

theorem σDiag_strictMono : StrictMono (σDiag u g μ hext) := by
  apply strictMono_nat_of_lt_succ
  intro n
  show iterσ u g μ hext n n < iterσ u g μ hext (n + 1) (n + 1)
  rw [iterσ_succ u g μ hext n, Function.comp_apply]
  have hψ_SM : StrictMono (Classical.choose
      (hext (fun m => u (iterσ u g μ hext n m)) (n + 1))) :=
    (Classical.choose_spec (hext (fun m => u (iterσ u g μ hext n m)) (n + 1))).1
  have hle : n + 1 ≤ Classical.choose
      (hext (fun m => u (iterσ u g μ hext n m)) (n + 1)) (n + 1) :=
    nat_le_of_strictMono hψ_SM (n + 1)
  exact (iterσ_strictMono u g μ hext n (Nat.lt_succ_self n)).trans_le
    ((iterσ_strictMono u g μ hext n).monotone hle)

/-- The diagonal converges in `L²(μ k)` for every level `k`. -/
theorem σDiag_tendsto (k : ℕ) :
    Tendsto (fun n => eLpNorm (fun t => u (σDiag u g μ hext n) t - g t) 2 (μ k))
      atTop (nhds 0) := by
  have hbase := iterσ_tendsto_self u g μ hext k
  set selF : ℕ → ℕ := fun n =>
    if h : k ≤ n then
      Classical.choose (iterσ_refines_point u g μ hext k n h n)
    else n with hselF_def
  have hselF_ge : ∀ n, k ≤ n → n ≤ selF n := fun n hkn => by
    simp only [hselF_def, dif_pos hkn]
    exact (Classical.choose_spec (iterσ_refines_point u g μ hext k n hkn n)).1
  have hselF_eq : ∀ n, k ≤ n →
      σDiag u g μ hext n = iterσ u g μ hext k (selF n) := fun n hkn => by
    simp only [hselF_def, dif_pos hkn, σDiag]
    exact (Classical.choose_spec (iterσ_refines_point u g μ hext k n hkn n)).2
  have hcofinal : Tendsto selF atTop atTop :=
    tendsto_atTop_atTop.mpr fun N =>
      ⟨max k N, fun n hn =>
        (Nat.le_max_right _ _).trans (hn.trans (hselF_ge n ((Nat.le_max_left _ _).trans hn)))⟩
  have htail : ∀ᶠ n in atTop,
      eLpNorm (fun t => u (iterσ u g μ hext k (selF n)) t - g t) 2 (μ k) =
      eLpNorm (fun t => u (σDiag u g μ hext n) t - g t) 2 (μ k) :=
    eventually_atTop.mpr ⟨k, fun n hkn => by rw [hselF_eq n hkn]⟩
  exact (hbase.comp hcofinal).congr' htail

/-- **[Cantor diagonalization for `L²` convergence] one subsequence convergent at every level.** Given a
per-level extractor `hext` (from any reindexing `v` of the data, at any level `k`, a subsequence `ψ` with
`‖v(ψ ·) − g‖_{L²(μ k)} → 0`), there is a single strictly monotone `φ` with
`‖u(φ ·) − g‖_{L²(μ k)} → 0` for **every** `k`. The Cantor diagonal of the nested per-level extractions. -/
theorem eLpNorm_diagonal_subseq (hext : ∀ (v : ℕ → α → E) (k : ℕ), ∃ ψ : ℕ → ℕ,
      StrictMono ψ ∧ Tendsto (fun n => eLpNorm (fun t => v (ψ n) t - g t) 2 (μ k)) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, Tendsto (fun n => eLpNorm (fun t => u (φ n) t - g t) 2 (μ k)) atTop (nhds 0) :=
  ⟨σDiag u g μ hext, σDiag_strictMono u g μ hext, σDiag_tendsto u g μ hext⟩

/-- **[Level convergence transports to dominated measures].** If the diagonal `φ` converges in every `L²(μ k)`
and a measure `ν` is dominated by some `μ k` (`ν ≤ μ k`), then `φ` converges in `L²(ν)` too — `eLpNorm` is
monotone in the measure. This recovers, e.g., convergence on `volume.restrict (Ioc 0 T)` for every real `T`
from the integer-level diagonal. -/
theorem eLpNorm_tendsto_of_le {φ : ℕ → ℕ} {ν : Measure α} {k : ℕ} (hν : ν ≤ μ k)
    (hφ : Tendsto (fun n => eLpNorm (fun t => u (φ n) t - g t) 2 (μ k)) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun t => u (φ n) t - g t) 2 ν) atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hφ
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun _ => eLpNorm_mono_measure _ hν)

end Physlib.Mathematics.LpSubsequenceDiagonalization

end
