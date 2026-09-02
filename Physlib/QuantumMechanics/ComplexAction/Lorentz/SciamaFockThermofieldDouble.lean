/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The two-mode thermofield double: the purification of the Gibbs state

The **thermofield double** `|TFD⟩` doubles the mode into a system copy and a fictitious "tilde" copy so that the
mixed Gibbs state `ρ = e^{−βH}/Z` of `SciamaThermalDensityMatrix` becomes a *pure* state on the doubled
Hilbert space `ℓ²(ℕ) ⊗ ℓ²(ℕ) = ℓ²(ℕ × ℕ)` whose reduced state (tracing out the tilde copy) is exactly `ρ`:

`|TFD⟩ = Σₙ √(pₙ) |n⟩⊗|ñ⟩ = √(1−r) Σₙ r^{n/2} |n, n⟩`   (`r = e^{−βE}`, `pₙ = rⁿ(1−r)`).

Like the coherent state, this is a genuinely convergent `ℓ²(ℕ × ℕ)` vector — `Σₙ pₙ = 1` — and needs no
exponential of the (unbounded) two-mode squeeze generator: the two-mode Bogoliubov squeeze acts on the vacuum
by *this series*, exactly as the displacement acts by the coherent series (`SciamaFockDisplacement`).

* `tfdVector`, `tfdVector_norm` — `|TFD⟩` as a **unit vector** in `ℓ²(ℕ × ℕ)`.
* `tfd_offdiagonal` — `⟨n, m|TFD⟩ = 0` for `n ≠ m` (perfect system–tilde correlation).
* `tfd_reduced_diagonal` — **`Σₘ |⟨n, m|TFD⟩|² = pₙ`**: tracing out the tilde copy returns the Gibbs weight `pₙ`,
  i.e. the reduced density matrix is the thermal state `ρ`.  This is the purification property.

Complements the finite diagonal `TFDGibbsVariational.tfdReducedWeight`, which by design does not build the
infinite tensor; here the reduced state is read off the honest `ℓ²(ℕ × ℕ)` vector.

Honest scope: the TFD as a unit vector in `ℓ²(ℕ × ℕ)` and its diagonal reduced state (the Gibbs weights).  A
general partial-trace superoperator on the tensor factors is not built; the reduced *diagonal* — which is all
`ρ` has, since `ρ` is diagonal — is computed directly.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermofieldDouble

open scoped ENNReal
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaThermalDensityMatrix

/-- **The doubled Hilbert space** `ℓ²(ℕ × ℕ; ℂ) = ℓ²(ℕ) ⊗ ℓ²(ℕ)`. -/
abbrev FockHilbert2 : Type := lp (fun _ : ℕ × ℕ => ℂ) 2

/-- **The thermofield-double coefficient** `⟨n, m|TFD⟩ = δₙₘ √(pₙ)`. -/
def tfdCoeff (β E : ℝ) : ℕ × ℕ → ℂ :=
  fun p => if p.1 = p.2 then (Real.sqrt (thermalProbability β E p.1) : ℂ) else 0

/-- The Gibbs weight is nonnegative (`pₙ = rⁿ(1−r) ≥ 0` for `0 < βE`). -/
theorem thermalProbability_nonneg (β E : ℝ) (h : 0 < β * E) (n : ℕ) :
    0 ≤ thermalProbability β E n := by
  have hr1 : Real.exp (-(β * E)) < 1 := exp_neg_lt_one β E h
  unfold thermalProbability
  exact mul_nonneg (by positivity) (by linarith)

/-- The Gibbs distribution is summable. -/
theorem thermalProbability_summable (β E : ℝ) (h : 0 < β * E) :
    Summable (thermalProbability β E) := by
  have hr0 : 0 < Real.exp (-(β * E)) := Real.exp_pos _
  have hr1 : Real.exp (-(β * E)) < 1 := exp_neg_lt_one β E h
  unfold thermalProbability
  exact (summable_geometric_of_lt_one hr0.le hr1).mul_right _

/-- The diagonal squared amplitude is the Gibbs weight: `|⟨n, n|TFD⟩|² = pₙ`. -/
theorem tfdCoeff_diag_normSq (β E : ℝ) (h : 0 < β * E) (n : ℕ) :
    ‖tfdCoeff β E (n, n)‖ ^ 2 = thermalProbability β E n := by
  rw [tfdCoeff, if_pos rfl, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (thermalProbability_nonneg β E h n)]

/-- The coefficients are square-summable (`Σ_{n,m} |δₙₘ√pₙ|² = Σₙ pₙ = 1`). -/
theorem tfdCoeff_memℓp (β E : ℝ) (h : 0 < β * E) : Memℓp (tfdCoeff β E) 2 := by
  refine memℓp_gen ?_
  have hcong : (fun p : ℕ × ℕ => ‖tfdCoeff β E p‖ ^ (2 : ℝ≥0∞).toReal)
      = (fun p : ℕ × ℕ => if p.1 = p.2 then thermalProbability β E p.1 else 0) := by
    funext p
    rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, tfdCoeff]
    split_ifs with hp
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (thermalProbability_nonneg β E h p.1)]
    · rw [norm_zero]; norm_num
  rw [hcong]
  refine (Function.Injective.summable_iff (g := fun n : ℕ => (n, n))
    (fun a b hab => (Prod.ext_iff.mp hab).1) ?_).mp ?_
  · intro p hp
    have hne : p.1 ≠ p.2 := fun hpp => hp ⟨p.1, by simp [Prod.ext_iff, hpp]⟩
    rw [if_neg hne]
  · have hcomp : ((fun p : ℕ × ℕ => if p.1 = p.2 then thermalProbability β E p.1 else 0)
        ∘ fun n : ℕ => (n, n)) = thermalProbability β E := by
      funext n; simp
    rw [hcomp]; exact thermalProbability_summable β E h

/-- **The thermofield double** `|TFD⟩` as a vector in `ℓ²(ℕ × ℕ)`. -/
def tfdVector (β E : ℝ) (h : 0 < β * E) : FockHilbert2 := ⟨tfdCoeff β E, tfdCoeff_memℓp β E h⟩

@[simp] theorem tfdVector_apply (β E : ℝ) (h : 0 < β * E) (p : ℕ × ℕ) :
    (tfdVector β E h) p = tfdCoeff β E p := rfl

/-- **[TFD is a unit vector] `‖|TFD⟩‖ = 1`.**  The thermofield double is a genuine (normalized) pure state on
the doubled Hilbert space. -/
theorem tfdVector_norm (β E : ℝ) (h : 0 < β * E) : ‖tfdVector β E h‖ = 1 := by
  have hsupp : Function.support (fun p : ℕ × ℕ => ‖(tfdVector β E h) p‖ ^ 2)
      ⊆ Set.range (fun n : ℕ => (n, n)) := by
    intro p hp
    simp only [Function.mem_support, ne_eq, tfdVector_apply] at hp
    by_contra hpr
    have hne : p.1 ≠ p.2 := fun hpp => hpr ⟨p.1, by simp [Prod.ext_iff, hpp]⟩
    exact hp (by rw [tfdCoeff, if_neg hne, norm_zero]; norm_num)
  have hns : ‖tfdVector β E h‖ ^ 2 = 1 := by
    have hrpow := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (tfdVector β E h)
    rw [show (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) from by norm_num] at hrpow
    simp only [Real.rpow_natCast] at hrpow
    rw [hrpow, ← Function.Injective.tsum_eq (g := fun n : ℕ => (n, n))
      (fun a b hab => (Prod.ext_iff.mp hab).1) hsupp,
      show (fun n : ℕ => ‖(tfdVector β E h) (n, n)‖ ^ 2) = thermalProbability β E from by
        funext n; rw [tfdVector_apply]; exact tfdCoeff_diag_normSq β E h n]
    exact thermalProbability_tsum_one β E h
  rw [← Real.sqrt_sq (norm_nonneg (tfdVector β E h)), hns, Real.sqrt_one]

/-- **[System–tilde correlation] `⟨n, m|TFD⟩ = 0` for `n ≠ m`.**  The two copies are perfectly correlated —
the TFD is supported on the diagonal `|n, n⟩`. -/
theorem tfd_offdiagonal (β E : ℝ) (h : 0 < β * E) (n m : ℕ) (hnm : n ≠ m) :
    (tfdVector β E h) (n, m) = 0 := by
  rw [tfdVector_apply, tfdCoeff, if_neg hnm]

/-- **[Reduced state is the Gibbs state] `Σₘ |⟨n, m|TFD⟩|² = pₙ`.**  Tracing out the tilde copy returns the
thermal weight `pₙ` — the reduced density matrix of the thermofield double is the Gibbs state `ρ`.  This is the
defining purification property. -/
theorem tfd_reduced_diagonal (β E : ℝ) (h : 0 < β * E) (n : ℕ) :
    ∑' m : ℕ, ‖(tfdVector β E h) (n, m)‖ ^ 2 = thermalProbability β E n := by
  rw [tsum_eq_single n ?_]
  · rw [tfdVector_apply]; exact tfdCoeff_diag_normSq β E h n
  · intro m hm
    rw [tfdVector_apply, tfdCoeff, if_neg (Ne.symm hm), norm_zero]
    norm_num

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockThermofieldDouble

end
