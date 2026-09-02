/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentStateProperties
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The mean photon number of a coherent state: `⟨N⟩ = |α|²`

The coherent state `|α⟩` has a Poissonian photon-number distribution
(`SciamaFockCoherentStateProperties.coherentState_photon_poisson`), whose mean occupation is `|α|²`:

`⟨α|N|α⟩ / ‖|α⟩‖² = |α|²`.

The key analytic ingredient is the mean of the (unnormalized) Poisson weights,
`Σₙ n·xⁿ/n! = x·eˣ`.

* `tsum_nat_mul_pow_div_factorial` — `Σₙ n·xⁿ/n! = x·eˣ` (the Poisson-mean series).
* `coherentState_meanPhoton` — `Σₙ n·|⟨n|α⟩|² = |α|²·e^{|α|²}` (unnormalized mean occupation).
* `coherentState_meanPhoton_normalized` — `⟨N⟩ = Σₙ n·|⟨n|α⟩|² / ‖|α⟩‖² = |α|²`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockMeanPhoton

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockL2Completion
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentState
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockCoherentStateProperties

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- **[Poisson-mean series] `Σₙ n·xⁿ/n! = x·eˣ`.** -/
theorem tsum_nat_mul_pow_div_factorial (x : ℝ) :
    ∑' n : ℕ, (n : ℝ) * x ^ n / n.factorial = x * Real.exp x := by
  have he : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  have hshift : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * x ^ (n + 1) / ((n + 1).factorial))
      (x * Real.exp x) := by
    have hfn : (fun n : ℕ => x * (x ^ n / (n.factorial : ℝ)))
        = (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * x ^ (n + 1) / ((n + 1).factorial)) := by
      funext n
      rw [Nat.factorial_succ]
      have : ((n.factorial : ℝ)) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    rw [← hfn]
    exact he.mul_left x
  have hkey := (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ) * x ^ n / n.factorial) 1).mp hshift
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, zero_div, add_zero] at hkey
  exact hkey.tsum_eq

/-- **[Unnormalized mean occupation] `Σₙ n·|⟨n|α⟩|² = |α|²·e^{|α|²}`.** -/
theorem coherentState_meanPhoton (α : ℂ) :
    ∑' n : ℕ, (n : ℝ) * ‖⟪fockKet n, coherentState α⟫‖ ^ 2 = ‖α‖ ^ 2 * Real.exp (‖α‖ ^ 2) := by
  rw [show (fun n : ℕ => (n : ℝ) * ‖⟪fockKet n, coherentState α⟫‖ ^ 2)
      = (fun n : ℕ => (n : ℝ) * (‖α‖ ^ 2) ^ n / n.factorial) from ?_]
  · exact tsum_nat_mul_pow_div_factorial (‖α‖ ^ 2)
  · funext n
    rw [coherentState_photon_amp_sq, pow_mul]
    ring

/-- **[Mean photon number] `⟨N⟩ = |α|²`.**  The mean occupation of a coherent state is `|α|²` — the Poisson
mean. -/
theorem coherentState_meanPhoton_normalized (α : ℂ) :
    (∑' n : ℕ, (n : ℝ) * ‖⟪fockKet n, coherentState α⟫‖ ^ 2) / ‖coherentState α‖ ^ 2 = ‖α‖ ^ 2 := by
  rw [coherentState_meanPhoton, coherentState_norm_sq, mul_div_assoc,
    div_self (Real.exp_ne_zero _), mul_one]

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaFockMeanPhoton

end
