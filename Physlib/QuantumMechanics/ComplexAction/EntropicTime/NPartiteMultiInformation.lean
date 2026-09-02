/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality
public import Mathlib.Tactic.Linarith
meta import Zil

/-!
# N-partite multi-information: the general Grad–Layzer negentropy gap

The bipartite total correlation of `EntropicTime.TotalCorrelationEntropicClock` extends to an arbitrary
finite number of parts. For a joint distribution `F` on `n → α` (`n` parts, each valued in the alphabet
`α` — Grad–Layzer's `N` identical particles) the **multi-information**

  `C_N = D(F ‖ ∏ᵣ fᵣ) = Σᵣ H(Xᵣ) − H(X₁…X_N)`   (`totalCorrelationN`)

is the correlation generated among all parts, with `fᵣ` the coordinate marginals (`marginalN`). It is
nonnegative (`totalCorrelationN_nonneg`, the full `N`-body subadditivity `H(X₁…X_N) ≤ Σᵣ H(Xᵣ)`) and equals
the negentropy gap (`totalCorrelationN_eq_entropyGap`) — the faithful `C_N = H_N − N·H₁` with
`H = Σ p log p = −S`, for any finite `N` rather than only `N = 2`.

The arrow is a theorem of the same two inputs as the bipartite case (`totalCorrelationN_monotone`):

  * **Liouville / reversible conservation** — the joint entropy `H(X₁…X_N)` is invariant, and
  * **the Boltzmann `H`-theorem** — every reduced (single-part) entropy `H(Xᵣ)` does not decrease,

so `C_N` cannot decrease. The monotonicity is **conditional**: both premises enter as hypotheses, not
constructed here. Calibrating `τ_ent = γ·C_N` (`entropicClockN`) and `S_I = ħ·γ·C_N` (`imaginaryActionN`)
gives the `N`-body entropic clock and imaginary action, nonnegative and monotone under the same inputs.

The marginalization uses `Finset.sum_fiberwise_of_maps_to` (a sum against a coordinate function collapses
onto its marginal) and the product-of-marginals normalization uses `Fintype.piFinset_univ`.

* **the coordinate marginal** — `marginalN`, `marginalN_sum`, `sum_mul_coord_eq_marginalN`,
  `productMarginalN_sum`, `marginalN_pos`.
* **the multi-information** — `totalCorrelationN`, `totalCorrelationN_nonneg`,
  `totalCorrelationN_eq_entropyGap`.
* **the N-body arrow** — `totalCorrelationN_monotone`, `entropicClockN`, `imaginaryActionN`,
  `entropicClockN_monotone`, `imaginaryActionN_monotone`.

## References

* H. Grad, *Principles of the Kinetic Theory of Gases*, Handbuch der Physik XII (1958).
* D. Layzer, *The Arrow of Time* — `C_N = H_N − N·H₁`, macroscopic information flowing into correlations.
  Companion (bipartite `N = 2` case + the complex-action weight): `EntropicTime.TotalCorrelationEntropicClock`.
  Reuses `klDivergence`, `entropy`, `klDivergence_nonneg` from `EntropicTime.RelativeEntropyGibbsInequality`.
-/

set_option autoImplicit false

open Finset

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.NPartiteMultiInformation

variable {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] [DecidableEq α]

/-- The coordinate marginal `fᵣ(x) = ∑_{z : zᵣ = x} F(z)` of a joint distribution on `n → α`. -/
noncomputable def marginalN (r : n) (F : (n → α) → ℝ) (x : α) : ℝ :=
  ∑ z ∈ Finset.univ.filter (fun z => z r = x), F z

/-- The marginal preserves total mass. -/
lemma marginalN_sum (r : n) (F : (n → α) → ℝ) : ∑ x, marginalN r F x = ∑ z, F z := by
  simp only [marginalN]
  exact Finset.sum_fiberwise_of_maps_to (fun z _ => Finset.mem_univ (z r)) F

/-- A sum weighted by a function of the r-th coordinate collapses onto that marginal. -/
lemma sum_mul_coord_eq_marginalN (r : n) (F : (n → α) → ℝ) (g : α → ℝ) :
    ∑ z, F z * g (z r) = ∑ x, marginalN r F x * g x := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset α))
        (fun z (_ : z ∈ Finset.univ) => Finset.mem_univ (z r)) (fun z => F z * g (z r))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [marginalN, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2])

/-- The product of the marginals is a normalized distribution when `F` is. -/
lemma productMarginalN_sum (F : (n → α) → ℝ) (hF : ∑ z, F z = 1) :
    ∑ z : n → α, ∏ r, marginalN r F (z r) = 1 := by
  have key : ∀ r, (∑ x, marginalN r F x) = 1 := fun r => by rw [marginalN_sum, hF]
  calc ∑ z : n → α, ∏ r, marginalN r F (z r)
      = ∏ r, ∑ x, marginalN r F x := by
        rw [Finset.prod_univ_sum (fun _ : n => (Finset.univ : Finset α)) (fun r => marginalN r F),
          Fintype.piFinset_univ]
    _ = ∏ _r : n, (1 : ℝ) := Finset.prod_congr rfl (fun r _ => key r)
    _ = 1 := Finset.prod_const_one

/-- Each marginal is strictly positive when `F` is (via a nonempty fiber). -/
lemma marginalN_pos [Nonempty α] (r : n) (F : (n → α) → ℝ) (hF : ∀ z, 0 < F z) (x : α) :
    0 < marginalN r F x := by
  refine Finset.sum_pos (fun z _ => hF z) ?_
  exact ⟨Function.update (fun _ => Classical.arbitrary α) r x,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩

/-- The **N-partite total correlation** (multi-information) `C_N = D(F ‖ ∏ᵣ fᵣ)` of an `N`-body joint
distribution — the correlation generated among all `N` parts. -/
noncomputable def totalCorrelationN (F : (n → α) → ℝ) : ℝ :=
  klDivergence F (fun z => ∏ r, marginalN r F (z r))

/-- **[N-partite total correlation ≥ 0]** the multi-information is nonnegative — the full `N`-body
subadditivity of entropy `H(X₁…X_N) ≤ Σᵣ H(Xᵣ)`. -/
@[zil_level physical_theorem]
theorem totalCorrelationN_nonneg [Nonempty α] (F : (n → α) → ℝ) (hF : ∀ z, 0 < F z)
    (hsum : ∑ z, F z = 1) : 0 ≤ totalCorrelationN F :=
  klDivergence_nonneg F _ (fun z => (hF z).le)
    (fun z => Finset.prod_pos (fun r _ => marginalN_pos r F hF (z r))) hsum
    (productMarginalN_sum F hsum)

/-- **[N-partite total correlation is the negentropy gap]** `C_N = Σᵣ H(Xᵣ) − H(X₁…X_N)` — the faithful
`C_N = H_N − N·H₁` of Grad–Layzer (with `H = Σ p log p = −S`) for an arbitrary finite number of parts. -/
@[zil_level physical_theorem]
theorem totalCorrelationN_eq_entropyGap [Nonempty α] (F : (n → α) → ℝ) (hF : ∀ z, 0 < F z) :
    totalCorrelationN F = (∑ r, entropy (marginalN r F)) - entropy F := by
  have hm : ∀ r x, 0 < marginalN r F x := fun r x => marginalN_pos r F hF x
  have key : ∀ z, F z * Real.log (F z / ∏ r, marginalN r F (z r))
      = F z * Real.log (F z) - ∑ r, F z * Real.log (marginalN r F (z r)) := by
    intro z
    have hprodpos : 0 < ∏ r, marginalN r F (z r) := Finset.prod_pos (fun r _ => hm r (z r))
    rw [Real.log_div (ne_of_gt (hF z)) (ne_of_gt hprodpos),
        Real.log_prod (fun r _ => ne_of_gt (hm r (z r))), mul_sub, Finset.mul_sum]
  have hswap : ∑ z, ∑ r, F z * Real.log (marginalN r F (z r))
      = ∑ r, ∑ x, marginalN r F x * Real.log (marginalN r F x) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl
      (fun r _ => sum_mul_coord_eq_marginalN r F (fun x => Real.log (marginalN r F x)))
  simp only [totalCorrelationN, klDivergence, entropy, Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl (fun z _ => key z), Finset.sum_sub_distrib, hswap]
  ring

/-- **[The N-partite arrow, derived]** the multi-information does not decrease under Liouville conservation
of the joint entropy and the Boltzmann increase of every reduced (single-part) entropy — the `N`-body form
of the entropic-time arrow, conditional on the same two inputs. -/
@[zil_level physical_theorem]
theorem totalCorrelationN_monotone [Nonempty α] (F G : (n → α) → ℝ)
    (hF : ∀ z, 0 < F z) (hG : ∀ z, 0 < G z)
    (hLiouville : entropy G = entropy F)
    (hBoltzmann : ∀ r, entropy (marginalN r F) ≤ entropy (marginalN r G)) :
    totalCorrelationN F ≤ totalCorrelationN G := by
  rw [totalCorrelationN_eq_entropyGap F hF, totalCorrelationN_eq_entropyGap G hG, hLiouville]
  have := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hBoltzmann r)
  linarith

/-- The **N-partite entropic clock** `τ_ent = γ·C_N`. -/
noncomputable def entropicClockN (γ : ℝ) (F : (n → α) → ℝ) : ℝ := γ * totalCorrelationN F

/-- The **N-partite imaginary action** `S_I = ħ·γ·C_N`. -/
noncomputable def imaginaryActionN (ħ γ : ℝ) (F : (n → α) → ℝ) : ℝ := ħ * entropicClockN γ F

/-- **[The N-partite clock never runs backward]** `τ_ent ≥ 0` for `γ ≥ 0`. -/
@[zil_level physical_theorem]
theorem entropicClockN_nonneg [Nonempty α] (γ : ℝ) (hγ : 0 ≤ γ) (F : (n → α) → ℝ)
    (hF : ∀ z, 0 < F z) (hsum : ∑ z, F z = 1) : 0 ≤ entropicClockN γ F :=
  mul_nonneg hγ (totalCorrelationN_nonneg F hF hsum)

/-- **[The N-partite clock advances]** monotone under Liouville conservation and the Boltzmann increase of
every reduced entropy, for `γ ≥ 0`. -/
@[zil_level physical_theorem]
theorem entropicClockN_monotone [Nonempty α] (γ : ℝ) (hγ : 0 ≤ γ) (F G : (n → α) → ℝ)
    (hF : ∀ z, 0 < F z) (hG : ∀ z, 0 < G z) (hLiouville : entropy G = entropy F)
    (hBoltzmann : ∀ r, entropy (marginalN r F) ≤ entropy (marginalN r G)) :
    entropicClockN γ F ≤ entropicClockN γ G :=
  mul_le_mul_of_nonneg_left (totalCorrelationN_monotone F G hF hG hLiouville hBoltzmann) hγ

/-- **[The N-partite imaginary action accumulates]** `S_I(F) ≤ S_I(G)` under the same inputs, `ħ, γ ≥ 0`. -/
@[zil_level physical_theorem]
theorem imaginaryActionN_monotone [Nonempty α] (ħ γ : ℝ) (hħ : 0 ≤ ħ) (hγ : 0 ≤ γ)
    (F G : (n → α) → ℝ) (hF : ∀ z, 0 < F z) (hG : ∀ z, 0 < G z)
    (hLiouville : entropy G = entropy F)
    (hBoltzmann : ∀ r, entropy (marginalN r F) ≤ entropy (marginalN r G)) :
    imaginaryActionN ħ γ F ≤ imaginaryActionN ħ γ G :=
  mul_le_mul_of_nonneg_left (entropicClockN_monotone γ hγ F G hF hG hLiouville hBoltzmann) hħ

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.NPartiteMultiInformation

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NPartiteMultiInformation.totalCorrelationN_eq_entropyGap where
  formalizes @ "claim:the-n-partite-multi-information-of-a-joint-distribution-over-n-parts-equals-the-sum-of-single-part-entropies-minus-the-joint-entropy-the-general-grad-layzer-negentropy-gap-c-n-equals-h-n-minus-n-h-one",
  supported_by @ "paper:layzer-arrow-of-time-macroscopic-to-microscopic-information-flow"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.NPartiteMultiInformation.totalCorrelationN_monotone where
  formalizes @ "claim:the-n-partite-arrow-of-time-the-multi-information-does-not-decrease-under-liouville-conservation-of-the-joint-entropy-and-the-boltzmann-increase-of-every-single-part-reduced-entropy",
  requires @ "claim:the-n-partite-multi-information-of-a-joint-distribution-over-n-parts-equals-the-sum-of-single-part-entropies-minus-the-joint-entropy-the-general-grad-layzer-negentropy-gap-c-n-equals-h-n-minus-n-h-one",
  supported_by @ "paper:grad-1958-principles-of-the-kinetic-theory-of-gases-reversible-hn-conserved-reduced-h1-decreases"

zil_file_contract physlib.nPartiteMultiInformation where
  promises "The bipartite total correlation generalized to an arbitrary finite number of parts. For a joint distribution F on n -> alpha the N-partite multi-information C_N = D(F || prod_r f_r) with coordinate marginals f_r (via Finset.sum_fiberwise_of_maps_to) and product normalization (via Fintype.piFinset_univ) is nonnegative (the full N-body subadditivity H(X_1..X_N) <= sum_r H(X_r)) and equals the negentropy gap C_N = sum_r H(X_r) - H(X_1..X_N), the faithful Grad-Layzer C_N = H_N - N H_1 with H = sum p log p = -S for any finite N. The N-body arrow C_N nondecreasing is a theorem conditional on two supplied premises -- Liouville conservation of the joint entropy and the Boltzmann increase of every single-part reduced entropy; neither is constructed here. The clock tau_ent = gamma C_N and imaginary action S_I = hbar gamma C_N are nonnegative and monotone under the same inputs. Reuses klDivergence, entropy and klDivergence_nonneg from RelativeEntropyGibbsInequality; the homogeneous single-alphabet form (N identical particles) is used, not the dependent heterogeneous product."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.entropy",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.RelativeEntropyGibbsInequality.klDivergence_nonneg"]
  forbids_substitutes ["an unconditional arrow-of-time theorem: the Liouville and per-part Boltzmann inequalities are explicit inputs",
    "the bipartite N = 2 special case alone, whereas this covers an arbitrary finite number of parts"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.NPartiteMultiInformation.totalCorrelationN_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NPartiteMultiInformation.totalCorrelationN_eq_entropyGap,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NPartiteMultiInformation.totalCorrelationN_monotone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NPartiteMultiInformation.entropicClockN_nonneg,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NPartiteMultiInformation.entropicClockN_monotone,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.NPartiteMultiInformation.imaginaryActionN_monotone]

#zil_formalization_lint physlib.nPartiteMultiInformation

/- ZIL-END -/
