/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenSorkinJohnston
public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
public import Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert

/-!
# The consistent-histories decoherence functional is a Sorkin–Johnston state

The consistent-histories **decoherence functional**
`D(α,β) = Σ e^{(i/ℏ)(S_R[Φ]−S_R[Φ'])} · e^{−½(S_ent[Φ]+S_ent[Φ'])}`
factors, per history pair, as `D(α,β) = w(α)·conj(w(β))` with the complex-action history weight
`w(α) = e^{(i/ℏ)S_R[α] − ½ S_ent[α]}` (`PathIntegral.ComplexActionPathIntegralWeight`, with `S_I = (ℏ/2)S_ent`).
This is **exactly** the rank-one Hermitian kernel `nnWightman (conj ∘ w)` of `TimeOperator.NagaoNielsenSorkinJohnston`,
so — reusing that infrastructure — the decoherence functional is a **Sorkin–Johnston state**: its diagonal
`D(α,α) = |w(α)|² = e^{−S_ent[α]}` is the (real, non-negative) **Born probability**, and its off-diagonal is
suppressed by the entanglement action.

**Scope of this inspection.** This addresses the *quantum* open question posed at the end of Ghose-Choudhury et al.
(arXiv:1906.10387) — the quantisation / decoherence structure of the generalized isotonic oscillator — by giving
the consistent-histories decoherence functional (into which the isotonic real and entropic actions feed) its
Sorkin–Johnston form. It does **not** supplement the paper's *classical* pending items (the Ateb-function solutions
and the hypergeometric period series `T`), which are special-function computations that neither the decoherence
functional nor Yang–Baxter infrastructure can shortcut (and the repository has no Calogero / R-matrix machinery
applicable to the isotonic period).

* **`historyWeight`** — the complex-action weight `e^{(i/ℏ)S_R − ½ S_ent}`.
* **`decoherenceFunctional`** — `D(α,β) = w(α)conj(w(β))` as `nnWightman (conj ∘ w)`; **`decoherenceFunctional_apply`**,
  **`decoherenceFunctional_isHermitian`**, **`decoherenceFunctional_isSJState`**.
* **`decoherenceFunctional_diag_re`** — the diagonal is the Born weight `|w(α)|²`; **`historyWeight_born`**
  (`= e^{−S_ent}`, grounding the Born probability in the entanglement action).
* **§D — plugged into the quantum-measure hierarchy.** **`decoherenceFunctional_isDecoherenceFunctional`** (it is a
  genuine `QuantumMeasureHistoryHilbert.IsDecoherenceFunctional` when `w` is amplitude-additive on disjoint events —
  Hermiticity + rank-one strong positivity are free), whence **`decoherenceFunctional_quantalMeasure`** (`μ = |w|²`
  via `quantalMeasure`) and **`decoherenceFunctional_third_order`** (Sorkin's `I₃ = 0`, reusing
  `sorkin_third_order_sum_rule` — no re-derivation).

**Honest layering.** The SJ structure is reused verbatim from `NagaoNielsenSorkinJohnston`; the only new content is
the identification of the consistent-histories weight with `nnWightman`'s coordinate and the Born diagonal via the
entropic modulus. No new physical input beyond the two source modules.

## References

* Composes `PathIntegral.ComplexActionPathIntegralWeight` and `TimeOperator.NagaoNielsenSorkinJohnston`; addresses
  the quantum open question of arXiv:1906.10387.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenSorkinJohnston
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.QuantumMeasureHistoryHilbert

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston

variable {ι : Type*}

/-- The **complex-action history weight** `w = e^{(i/ℏ)S_R − ½ S_ent}` — the per-history contribution to the
decoherence functional, the master weight `exp[(i/ℏ)S_R − (1/ℏ)S_I]` with `S_I = (ℏ/2)S_ent`. -/
noncomputable def historyWeight (S_R S_ent ℏ : ℝ) : ℂ :=
  complexActionPathIntegralWeight S_R (ℏ / 2 * S_ent) ℏ

/-- The **decoherence functional** `D(α,β) = w(α)·conj(w(β))` — the consistent-histories kernel, realised as the
rank-one Sorkin–Johnston Wightman kernel `nnWightman (conj ∘ w)`. -/
noncomputable def decoherenceFunctional (w : ι → ℂ) : ι → ι → ℂ :=
  nnWightman (fun a => (starRingEnd ℂ) (w a))

/-- **The decoherence functional in product form** `D(α,β) = w(α)·conj(w(β))`. -/
lemma decoherenceFunctional_apply (w : ι → ℂ) (α β : ι) :
    decoherenceFunctional w α β = w α * (starRingEnd ℂ) (w β) := by
  simp only [decoherenceFunctional, nnWightman, Complex.conj_conj]

/-- **The decoherence functional is a Hermitian kernel** `D(β,α) = conj D(α,β)`. -/
lemma decoherenceFunctional_isHermitian (w : ι → ℂ) : IsHermitianKernel (decoherenceFunctional w) :=
  nnWightman_isHermitian _

/-- **The decoherence functional is a Sorkin–Johnston state** — being a rank-one Hermitian kernel with
non-negative diagonal, the consistent-histories decoherence functional realises an SJ vacuum (its Pauli–Jordan
part `2 Im D` is the antisymmetric interference). -/
lemma decoherenceFunctional_isSJState (w : ι → ℂ) :
    IsSJState (decoherenceFunctional w) (nnPauliJordan (fun a => (starRingEnd ℂ) (w a))) :=
  nnWightman_isSJState _

/-- **The diagonal is the Born probability** `D(α,α).re = |w(α)|²` — the quantal measure (diagonal of the
decoherence functional) is the modulus-squared of the history amplitude, non-negative by construction. -/
lemma decoherenceFunctional_diag_re (w : ι → ℂ) (α : ι) :
    (decoherenceFunctional w α α).re = Complex.normSq (w α) := by
  rw [decoherenceFunctional, nnWightman_diag_re, Complex.normSq_conj]

/-- **The Born diagonal is the entanglement damping** `|w|² = e^{−S_ent}` — the diagonal weight of the decoherence
functional is `e^{−S_ent}`, the entanglement action exponentiated: the Born probability is set by the entropic
(imaginary-action) sector. -/
lemma historyWeight_born (S_R S_ent ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    Complex.normSq (historyWeight S_R S_ent ℏ) = Real.exp (-S_ent) := by
  rw [Complex.normSq_eq_norm_sq, historyWeight, master_modulus_is_kuiken, kuikenWeight,
    show ℏ / 2 * S_ent / ℏ = S_ent / 2 from by field_simp, pow_two, ← Real.exp_add]
  congr 1; ring


/-- **The decoherence functional is a genuine `IsDecoherenceFunctional`** when the history weight is additive on
disjoint events `w(β⊔γ) = w(β)+w(γ)` (the additivity of quantum amplitudes over coarse-grainings) — Hermiticity
and rank-one strong positivity hold automatically. This plugs the SJ history kernel into the entire
`QuantumMeasureHistoryHilbert` machinery (quantal measure, interference, `I₃ = 0`), no re-derivation. -/
lemma decoherenceFunctional_isDecoherenceFunctional [DistribLattice ι] [OrderBot ι] (w : ι → ℂ)
    (hadd : ∀ β γ : ι, Disjoint β γ → w (β ⊔ γ) = w β + w γ) :
    IsDecoherenceFunctional (decoherenceFunctional w) where
  hermitian α β := decoherenceFunctional_isHermitian w α β
  biadditive α β γ hd := by
    rw [decoherenceFunctional_apply, decoherenceFunctional_apply, decoherenceFunctional_apply,
      hadd β γ hd, map_add, mul_add]
  posSemidef s c := by
    have hfact :
        (∑ α ∈ s, ∑ β ∈ s, (starRingEnd ℂ) (c α) * c β * decoherenceFunctional w α β)
          = (∑ α ∈ s, (starRingEnd ℂ) (c α) * w α)
            * (starRingEnd ℂ) (∑ α ∈ s, (starRingEnd ℂ) (c α) * w α) := by
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun α _ => Finset.sum_congr rfl (fun β _ => ?_))
      rw [decoherenceFunctional_apply]
      simp only [map_mul, Complex.conj_conj]
      ring
    rw [hfact, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _

/-- **The quantal (Born) measure of the decoherence functional** `μ(α) = |w(α)|²` — reusing
`QuantumMeasureHistoryHilbert.quantalMeasure` (the diagonal `Re D(α,α)`). -/
lemma decoherenceFunctional_quantalMeasure (w : ι → ℂ) (α : ι) :
    quantalMeasure (decoherenceFunctional w) α = Complex.normSq (w α) :=
  decoherenceFunctional_diag_re w α

/-- **Sorkin's third-order sum rule `I₃ = 0` holds for the decoherence functional** — being a genuine decoherence
functional, the SJ history kernel obeys the consistent-histories quantum-measure identity
(`QuantumMeasureHistoryHilbert.sorkin_third_order_sum_rule`): no third-order interference. -/
lemma decoherenceFunctional_third_order [DistribLattice ι] [OrderBot ι] (w : ι → ℂ)
    (hadd : ∀ β γ : ι, Disjoint β γ → w (β ⊔ γ) = w β + w γ) (α β γ : ι)
    (hab : Disjoint α β) (hbc : Disjoint β γ) (hac : Disjoint α γ) :
    quantalMeasure (decoherenceFunctional w) (α ⊔ β ⊔ γ)
      = quantalMeasure (decoherenceFunctional w) (α ⊔ β)
          + quantalMeasure (decoherenceFunctional w) (β ⊔ γ)
          + quantalMeasure (decoherenceFunctional w) (α ⊔ γ)
        - quantalMeasure (decoherenceFunctional w) α - quantalMeasure (decoherenceFunctional w) β
        - quantalMeasure (decoherenceFunctional w) γ :=
  sorkin_third_order_sum_rule (decoherenceFunctional_isDecoherenceFunctional w hadd) α β γ hab hbc hac

end Physlib.QuantumMechanics.ComplexAction.DecoherenceFunctionalSorkinJohnston
