/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperatorPositive
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Basis-independence of the trace `Tr ρ = 1`

`SciamaFockThermalTrace.thermalTrace_normalized` computed the trace of the density matrix `ρ` in the number
basis.  Here that is shown to be **basis-independent**: for *every* Hilbert basis `(b i)` of `ℓ²`,
`∑ᵢ ⟨b i, ρ (b i)⟩ = 1`.

The proof is the textbook Parseval + Tonelli argument, valid for the diagonal positive `ρ` even without a
general trace-class theory: `⟨b i, ρ (b i)⟩ = Σₖ pₖ |⟨k|b i⟩|²`, so summing over `i` and exchanging the order
(Tonelli, all terms `≥ 0`) gives `Σₖ pₖ (Σᵢ |⟨k|b i⟩|²) = Σₖ pₖ ‖|k⟩‖² = Σₖ pₖ = 1` by Parseval
(`HilbertBasis.tsum_inner_mul_inner`) and `thermalProbability_tsum_one`.

* `densityOp_diag_hasSum` — `⟨v, ρ v⟩.re = Σₖ pₖ |⟨k|v⟩|²` (as a `HasSum`).
* `fockKet_parseval_hasSum` — `Σᵢ |⟨k|b i⟩|² = 1` (Parseval for the number states).
* `densityOp_trace_hilbertBasis` — `Σᵢ ⟨b i, ρ (b i)⟩.re = 1` for every Hilbert basis `b`: the trace is
  basis-independent.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockTraceBasisIndependence

open scoped ENNReal
open RCLike
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperator
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockDensityOperatorPositive

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The `k`-th ℓ² coordinate of a vector is its inner product with the number state `|k⟩`. -/
theorem inner_fockKet (v : FockHilbert) (k : ℕ) : ⟪fockKet k, v⟫ = v k := by
  rw [fockKet, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

/-- **[Diagonal element] `⟨v, ρ v⟩.re = Σₖ pₖ |⟨k|v⟩|²`** (as a `HasSum`). -/
theorem densityOp_diag_hasSum (β E : ℝ) (h : 0 < β * E) (v : FockHilbert) :
    HasSum (fun k => thermalProbability β E k * Complex.normSq ⟪fockKet k, v⟫)
      ((⟪v, densityOp β E h v⟫).re) := by
  have hs := Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) v (densityOp β E h v))
  have hfun : (fun k => (⟪v k, (densityOp β E h v) k⟫).re)
      = (fun k => thermalProbability β E k * Complex.normSq ⟪fockKet k, v⟫) := by
    funext k
    rw [densityOp_apply_coe, RCLike.inner_apply,
      show (↑(thermalProbability β E k) * v k) * (starRingEnd ℂ) (v k)
        = ↑(thermalProbability β E k) * (v k * (starRingEnd ℂ) (v k)) from by ring,
      Complex.mul_conj, ← inner_fockKet v k, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hfun] at hs
  exact hs

/-- **[Parseval] `Σᵢ |⟨k|b i⟩|² = 1`** for a Hilbert basis `b` (as a `HasSum`). -/
theorem fockKet_parseval_hasSum (b : HilbertBasis ℕ ℂ FockHilbert) (k : ℕ) :
    HasSum (fun i => Complex.normSq ⟪fockKet k, b i⟫) 1 := by
  have hs := Complex.hasSum_re (b.hasSum_inner_mul_inner (fockKet k) (fockKet k))
  have hfun : (fun i => (⟪fockKet k, b i⟫ * ⟪b i, fockKet k⟫).re)
      = (fun i => Complex.normSq ⟪fockKet k, b i⟫) := by
    funext i
    rw [show ⟪b i, fockKet k⟫ = (starRingEnd ℂ) ⟪fockKet k, b i⟫ from
        (inner_conj_symm _ _).symm, Complex.mul_conj, Complex.ofReal_re]
  rw [hfun, fockKet_inner] at hs
  simpa using hs

/-- **[Trace is basis-independent] `Σᵢ ⟨b i, ρ (b i)⟩ = 1`** for every Hilbert basis `b`.  The trace of the
density matrix is `1` in every orthonormal basis, not just the number basis. -/
theorem densityOp_trace_hilbertBasis (β E : ℝ) (h : 0 < β * E)
    (b : HilbertBasis ℕ ℂ FockHilbert) :
    ∑' i, (⟪b i, densityOp β E h (b i)⟫).re = 1 := by
  have hnonneg : ∀ i, 0 ≤ (⟪b i, densityOp β E h (b i)⟫).re := by
    intro i
    rw [← inner_conj_symm, Complex.conj_re]
    exact densityOp_re_inner_self_nonneg β E h (b i)
  have hg_nonneg : ∀ i k, 0 ≤ thermalProbability β E k * Complex.normSq ⟪fockKet k, b i⟫ :=
    fun i k => mul_nonneg (thermalProbability_nonneg β E h k) (Complex.normSq_nonneg _)
  have hA : ∀ i, HasSum (fun k => thermalProbability β E k * Complex.normSq ⟪fockKet k, b i⟫)
      ((⟪b i, densityOp β E h (b i)⟫).re) := fun i => densityOp_diag_hasSum β E h (b i)
  have hB : ∀ k, HasSum (fun i => thermalProbability β E k * Complex.normSq ⟪fockKet k, b i⟫)
      (thermalProbability β E k) := by
    intro k
    simpa using (fockKet_parseval_hasSum b k).mul_left (thermalProbability β E k)
  have hp_summable : Summable (fun k => thermalProbability β E k) := by
    unfold thermalProbability
    exact (summable_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_lt_one β E h)).mul_right _
  have hEnn : ∑' i, ENNReal.ofReal ((⟪b i, densityOp β E h (b i)⟫).re) = 1 := by
    calc ∑' i, ENNReal.ofReal ((⟪b i, densityOp β E h (b i)⟫).re)
        = ∑' i, ∑' k, ENNReal.ofReal (thermalProbability β E k * Complex.normSq ⟪fockKet k, b i⟫) := by
          refine tsum_congr (fun i => ?_)
          rw [← (hA i).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (hg_nonneg i) (hA i).summable]
      _ = ∑' k, ∑' i, ENNReal.ofReal (thermalProbability β E k * Complex.normSq ⟪fockKet k, b i⟫) :=
          ENNReal.tsum_comm
      _ = ∑' k, ENNReal.ofReal (thermalProbability β E k) := by
          refine tsum_congr (fun k => ?_)
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hg_nonneg i k) (hB k).summable, (hB k).tsum_eq]
      _ = ENNReal.ofReal (∑' k, thermalProbability β E k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => thermalProbability_nonneg β E h k) hp_summable).symm
      _ = 1 := by rw [thermalProbability_tsum_one β E h, ENNReal.ofReal_one]
  have hsummable : Summable (fun i => (⟪b i, densityOp β E h (b i)⟫).re) := by
    have hne : ∑' i, ENNReal.ofReal ((⟪b i, densityOp β E h (b i)⟫).re) ≠ ⊤ := by
      rw [hEnn]; exact ENNReal.one_ne_top
    exact (ENNReal.summable_toReal hne).congr (fun i => ENNReal.toReal_ofReal (hnonneg i))
  have hkey : ENNReal.ofReal (∑' i, (⟪b i, densityOp β E h (b i)⟫).re) = 1 := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable, hEnn]
  have htr := congrArg ENNReal.toReal hkey
  rwa [ENNReal.toReal_ofReal (tsum_nonneg hnonneg), ENNReal.toReal_one] at htr

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockTraceBasisIndependence

end
