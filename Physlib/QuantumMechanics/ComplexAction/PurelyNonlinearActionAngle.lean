/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator

/-!
# Action-angle variables for the purely nonlinear oscillator (Ghosh–Bhamidipati 1905.08062)

The action-angle treatment of the **same** purely nonlinear oscillator `q̈ + sgn(q)|q|^α = 0` as
`GeneralizedIsotonicOscillator` (Ghose-Choudhury et al. 1906.10387) — here solved by Hamiltonian action-angle
variables, reproducing the amplitude-dependent period/frequency and the exact generalized-trigonometric solution.
This module formalizes the exact-algebra core and **links it back** to `GeneralizedIsotonicOscillator`'s `betaFn`,
`periodU` (`= T`) and `frequencyCa` (`= ω_ca`).

The Hamiltonian `H = p²/2 + |q|^{α+1}/(α+1) = E` (Eq. 2.2) is a constant of motion; the momentum on a level set is
`p² = 2E(1 − |q/q₀|^{α+1})`. The action `J = ∮ p dq` and angle `θ = arcsin_{2,α+1}(q/q₀)` (Eqs. 2.3–2.5) give the
period `T = ∂J/∂E` and frequency `Ω_{2,α+1} = 2π_{2,α+1}/T`; the generalized `π` is a Beta value
`π_{2,α+1} = (2/(α+1)) B(1/2, 1/(α+1))` (Eqs. 2.7, and `π_{m,n} = (2/n)B((m−1)/m, 1/n)`). The main exact identities:

* `Ω_{2,α+1} = √(2/(α+1)) |q₀|^{(α−1)/2}` (Eq. 2.11), obtained as `T·Ω = 2π_{2,α+1}` with the Γ-ratio cancelling;
* the ateb-function period relation `2Π_α/ω_ca = T` (Eq. 1.5) — the same period two ways;
* `ω_ca = ((α+1)/2)·Ω_{2,α+1}` — the ateb frequency and the generalized-sine frequency differ by `(α+1)/2`;
* at `α = 1` the system is the **isochronous** harmonic oscillator: `Ω = 1`, `T = 2π`.

* **§A — Hamiltonian and momentum (Eq. 2.2).** `pnlHamiltonian`; **`momentum_sq`**.
* **§B — the generalized `π` as a Beta value (Eqs. 1.2, 2.7).** `genPi2`, `atebPi`; **`genPi2_eq_atebPi`**.
* **§C — period and frequency (Eqs. 1.5, 2.11).** `pnlFrequency`; **`periodU_mul_frequency`** (`T·Ω = 2π_{2,α+1}`),
 **`frequencyCa_eq_pnlFrequency`** (`ω_ca = (α+1)/2·Ω`), **`periodU_mul_frequencyCa`** / **`atebPi_period_relation`**
 (`2Π_α/ω_ca = T`).
* **§D — the isochronous harmonic limit `α = 1`.** **`pnlFrequency_at_one`** (`= 1`); `periodU 1 1 q₀ = 2π`
 (`GeneralizedIsotonicOscillator.periodU_at_one`).

Exact `ring`/`Real.sqrt`/`Real.rpow`/`betaFn` identities for the Hamiltonian momentum, the
Beta-value `π`, the Γ-cancelling period/frequency relations and the harmonic limit. The action integral `J = ∮ p dq`
itself, the generalized-trigonometric inversion `arcsin_{2,α+1}`, the ateb functions `sa/ca` and the adiabatic
invariance of `J` are the paper's analysis / special-function content, recorded not re-derived.

## References

* A. Ghosh, C. Bhamidipati, arXiv:1905.08062, Eqs. 1.2, 1.5, 2.2, 2.7, 2.10–2.13. Companion to
 `GeneralizedIsotonicOscillator` (1906.10387).

No new axioms.
-/

set_option autoImplicit false

open scoped Real
open Physlib.QuantumMechanics.ComplexAction.GeneralizedIsotonicOscillator

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngle

/-! ## §A — Hamiltonian and momentum (Eq. 2.2) -/

/-- The **purely nonlinear oscillator Hamiltonian** `H = p²/2 + |q|^{α+1}/(α+1)` (Eq. 2.2). -/
noncomputable def pnlHamiltonian (α q p : ℝ) : ℝ := p ^ 2 / 2 + |q| ^ (α + 1) / (α + 1)

/-- **The on-shell momentum** `p² = 2E(1 − |q/q₀|^{α+1})` — from energy conservation `H = E` with turning point `q₀`
(`E = |q₀|^{α+1}/(α+1)`, `p = 0`), the momentum squared on the level set (Eq. 2.2 / §2.1). -/
theorem momentum_sq (α q q₀ p E : ℝ) (hα : α + 1 ≠ 0) (hq₀ : |q₀| ^ (α + 1) ≠ 0)
    (hE : E = |q₀| ^ (α + 1) / (α + 1)) (hH : pnlHamiltonian α q p = E) :
    p ^ 2 = 2 * E * (1 - |q| ^ (α + 1) / |q₀| ^ (α + 1)) := by
  subst hE
  rw [pnlHamiltonian] at hH
  have hp : p ^ 2 = 2 * (|q₀| ^ (α + 1) / (α + 1)) - 2 * (|q| ^ (α + 1) / (α + 1)) := by linarith
  rw [hp]
  field_simp

/-! ## §B — the generalized `π` as a Beta value (Eqs. 1.2, 2.7) -/

/-- The **generalized `π`** `π_{2,α+1} = (2/(α+1)) B(1/2, 1/(α+1))` (Eq. 2.7, from `π_{m,n} = (2/n)B((m−1)/m,1/n)`
at `m = 2`, `n = α+1`) — the half-period of the generalized sine `sin_{2,α+1}`. -/
noncomputable def genPi2 (α : ℝ) : ℝ := 2 / (α + 1) * betaFn (1 / 2) (1 / (α + 1))

/-- The **ateb generalized `π`** `Π_α = B(1/(α+1), 1/2)` (Eq. 1.2) — the ateb-function half-period. -/
noncomputable def atebPi (α : ℝ) : ℝ := betaFn (1 / (α + 1)) (1 / 2)

/-- **The two generalized `π` agree up to `2/(α+1)`** `π_{2,α+1} = (2/(α+1)) Π_α` — the generalized-sine and ateb
half-periods coincide via the symmetry `B(1/2,1/(α+1)) = B(1/(α+1),1/2)`. -/
theorem genPi2_eq_atebPi (α : ℝ) : genPi2 α = 2 / (α + 1) * atebPi α := by
  unfold genPi2 atebPi betaFn
  rw [show (1 : ℝ) / 2 + 1 / (α + 1) = 1 / (α + 1) + 1 / 2 from by ring]
  ring

/-! ## §C — period and frequency (Eqs. 1.5, 2.11) -/

/-- The **purely nonlinear oscillator frequency** `Ω_{2,α+1} = √(2/(α+1)) |q₀|^{(α−1)/2}` (Eqs. 1.9, 2.11) —
amplitude-dependent (non-isochronous) for `α ≠ 1`. -/
noncomputable def pnlFrequency (α q₀ : ℝ) : ℝ := Real.sqrt (2 / (α + 1)) * |q₀| ^ ((α - 1) / 2)

/-- **Frequency from the period and the generalized `π` (Eq. 2.11)** `T·Ω_{2,α+1} = 2π_{2,α+1}` — the period
`T = periodU 1 α q₀` (Eq. 2.10) times the frequency is twice the generalized half-period; the Γ-ratio and the
amplitude power `|q₀|` cancel, giving the amplitude-dependent frequency `Ω_{2,α+1}`. -/
theorem periodU_mul_frequency (α q₀ : ℝ) (hα : 0 < α + 1) (hq₀ : q₀ ≠ 0) :
    periodU 1 α q₀ * pnlFrequency α q₀ = 2 * genPi2 α := by
  have habs : (0 : ℝ) < |q₀| := abs_pos.mpr hq₀
  have hpow : |q₀| ^ ((1 - α) / 2) * |q₀| ^ ((α - 1) / 2) = 1 := by
    rw [← Real.rpow_add habs, show (1 - α) / 2 + (α - 1) / 2 = 0 from by ring, Real.rpow_zero]
  have hsqrtprod :
      Real.sqrt (8 * π / (1 ^ 2 * (α + 1))) * Real.sqrt (2 / (α + 1)) = 4 / (α + 1) * Real.sqrt π := by
    rw [one_pow, one_mul, ← Real.sqrt_mul (by positivity),
      show 8 * π / (α + 1) * (2 / (α + 1)) = (4 / (α + 1)) ^ 2 * π from by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [genPi2_eq_atebPi, atebPi, betaFn_half α hα.ne']
  unfold periodU pnlFrequency
  rw [show Real.sqrt (8 * π / (1 ^ 2 * (α + 1))) *
        (Real.Gamma (1 / (α + 1)) / Real.Gamma ((α + 3) / (2 * (α + 1)))) * |q₀| ^ ((1 - α) / 2) *
        (Real.sqrt (2 / (α + 1)) * |q₀| ^ ((α - 1) / 2))
      = Real.sqrt (8 * π / (1 ^ 2 * (α + 1))) * Real.sqrt (2 / (α + 1)) *
        (Real.Gamma (1 / (α + 1)) / Real.Gamma ((α + 3) / (2 * (α + 1)))) *
        (|q₀| ^ ((1 - α) / 2) * |q₀| ^ ((α - 1) / 2)) from by ring,
    hsqrtprod, hpow, mul_one]
  ring

/-- **The ateb frequency is `(α+1)/2` times the generalized-sine frequency** `ω_ca = ((α+1)/2) Ω_{2,α+1}`
(Eqs. 1.3, 2.11) — the two exact-solution frequencies of the same oscillator differ by the fixed factor
`(α+1)/2`. -/
theorem frequencyCa_eq_pnlFrequency (α A : ℝ) (hα : 0 < α + 1) :
    frequencyCa 1 α A = (α + 1) / 2 * pnlFrequency α A := by
  have hsqrt : (α + 1) / 2 * Real.sqrt (2 / (α + 1)) = Real.sqrt ((α + 1) / 2) := by
    have h1 : (0 : ℝ) ≤ (α + 1) / 2 * Real.sqrt (2 / (α + 1)) := by positivity
    rw [← Real.sqrt_sq h1, mul_pow, Real.sq_sqrt (by positivity)]
    congr 1
    field_simp
  unfold frequencyCa pnlFrequency
  rw [one_pow, one_mul,
    show (α + 1) / 2 * (Real.sqrt (2 / (α + 1)) * |A| ^ ((α - 1) / 2))
      = (α + 1) / 2 * Real.sqrt (2 / (α + 1)) * |A| ^ ((α - 1) / 2) from by ring,
    hsqrt, mul_comm (|A| ^ ((α - 1) / 2))]

/-- **The period as `2Π_α/ω_ca`, product form (Eq. 1.5)** `T·ω_ca = 2Π_α` — the period `T = periodU 1 α A`
(Eq. 2.10) times the ateb frequency `ω_ca` is twice the ateb half-period `Π_α`; the Γ-ratio and the amplitude
power cancel. -/
theorem periodU_mul_frequencyCa (α A : ℝ) (hα : 0 < α + 1) (hA : A ≠ 0) :
    periodU 1 α A * frequencyCa 1 α A = 2 * atebPi α := by
  have habs : (0 : ℝ) < |A| := abs_pos.mpr hA
  have hpow : |A| ^ ((1 - α) / 2) * |A| ^ ((α - 1) / 2) = 1 := by
    rw [← Real.rpow_add habs, show (1 - α) / 2 + (α - 1) / 2 = 0 from by ring, Real.rpow_zero]
  have hsqrtprod :
      Real.sqrt (8 * π / (1 ^ 2 * (α + 1))) * Real.sqrt (1 ^ 2 * (α + 1) / 2) = 2 * Real.sqrt π := by
    rw [one_pow, one_mul, ← Real.sqrt_mul (by positivity),
      show 8 * π / (α + 1) * ((α + 1) / 2) = (2 * Real.sqrt π) ^ 2 from by
        rw [show (2 * Real.sqrt π) ^ 2 = 4 * Real.sqrt π ^ 2 from by ring, Real.sq_sqrt Real.pi_pos.le]
        field_simp; ring,
      Real.sqrt_sq (by positivity)]
  rw [atebPi, betaFn_half α hα.ne']
  unfold periodU frequencyCa
  rw [show Real.sqrt (8 * π / (1 ^ 2 * (α + 1))) *
        (Real.Gamma (1 / (α + 1)) / Real.Gamma ((α + 3) / (2 * (α + 1)))) * |A| ^ ((1 - α) / 2) *
        (|A| ^ ((α - 1) / 2) * Real.sqrt (1 ^ 2 * (α + 1) / 2))
      = Real.sqrt (8 * π / (1 ^ 2 * (α + 1))) * Real.sqrt (1 ^ 2 * (α + 1) / 2) *
        (Real.Gamma (1 / (α + 1)) / Real.Gamma ((α + 3) / (2 * (α + 1)))) *
        (|A| ^ ((1 - α) / 2) * |A| ^ ((α - 1) / 2)) from by ring,
    hsqrtprod, hpow, mul_one]
  ring

/-- **The ateb-function period relation (Eq. 1.5)** `2Π_α/ω_ca = T` — the period of the purely nonlinear
oscillator obtained from the ateb half-period `Π_α` and the ateb frequency `ω_ca` equals `T = periodU 1 α A`
(Eq. 2.10): the same amplitude-dependent period reached through the ateb functions and the action-angle route. -/
theorem atebPi_period_relation (α A : ℝ) (hα : 0 < α + 1) (hA : A ≠ 0) :
    2 * atebPi α / frequencyCa 1 α A = periodU 1 α A := by
  have hfc : frequencyCa 1 α A ≠ 0 := by
    have habs : (0 : ℝ) < |A| := abs_pos.mpr hA
    unfold frequencyCa
    positivity
  rw [← periodU_mul_frequencyCa α A hα hA, mul_div_assoc, div_self hfc, mul_one]

/-! ## §D — the isochronous harmonic limit `α = 1` -/

/-- **At `α = 1` the oscillator is isochronous** `Ω_{2,2} = 1` — the amplitude dependence `|q₀|^{(α−1)/2}`
disappears, recovering the amplitude-independent harmonic frequency (`GeneralizedIsotonicOscillator.periodU_at_one`
gives the matching period `T = 2π`). -/
theorem pnlFrequency_at_one (q₀ : ℝ) : pnlFrequency 1 q₀ = 1 := by
  unfold pnlFrequency
  rw [show (2 : ℝ) / (1 + 1) = 1 from by norm_num, show ((1 : ℝ) - 1) / 2 = 0 from by norm_num,
    Real.rpow_zero, mul_one, Real.sqrt_one]

end Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearActionAngle
