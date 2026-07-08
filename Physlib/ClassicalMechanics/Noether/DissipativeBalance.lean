/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Noether balance law with a dissipative defect

The reversible (real-action) Noether content is *conservation*: a continuous
symmetry of `S_R` yields a charge `Q` with `dQ/dt = 0`. The entropic-time framework does not replace
this — it **extends** it. With an imaginary/dissipative action `S_I`, the
first-variation identity becomes a **balance law**

  `Q(t₂) − Q(t₁) = −∫_{t₁}^{t₂} defect`,   i.e.   `dQ/dt = −defect`,

where `defect = δS_I` is the dissipative leakage rate. This module records that
balance law abstractly (the integral form of the first-variation identity, with
the variational origin deferred) and proves its two regimes:

* **zero defect ⇒ ordinary Noether conservation** (`conserved_of_zero_defect`);
* **non-negative defect ⇒ monotone charge leakage**
  (`charge_decreasing_of_nonneg_defect`).

The lost reversible charge is recorded as entropy production; that link is made in
`Physlib.StatisticalMechanics.EntropyProduction`.


## References

- **Gough, Ratiu, Smolyanov 2015** — *Noether's theorem for dissipative quantum semigroups*
- **Bartosiewicz & Torres 2008** — *Noether's theorem on time scales*
- **Noether 1918** — *Invariante Variationsprobleme*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.ClassicalMechanics.Noether.DissipativeBalance

/-- **Noether balance datum.** A reversible Noether charge `Q` and a dissipative
defect rate `defect`, related by the balance law
`Q(t₂) − Q(t₁) = −∫_{t₁}^{t₂} defect` (the integrated `dQ/dt = −defect`). This is
the first-variation identity of Noether's theorem in the presence of an
imaginary/dissipative action. -/
structure NoetherBalance where
  /-- Reversible Noether charge. -/
  Q : ℝ → ℝ
  /-- Dissipative defect rate `δS_I`. -/
  defect : ℝ → ℝ
  /-- Balance law: the charge change equals minus the accumulated defect. -/
  balance : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ → Q t₂ - Q t₁ = -∫ t in t₁..t₂, defect t

namespace NoetherBalance

variable (B : NoetherBalance)

/-- **Ordinary Noether conservation at zero defect.** With no dissipative defect
the charge is conserved, `Q(t₂) = Q(t₁)`. -/
theorem conserved_of_zero_defect (hzero : ∀ t, B.defect t = 0) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    B.Q t₂ = B.Q t₁ := by
  have hb := B.balance t₁ t₂ h
  simp only [hzero, intervalIntegral.integral_zero, neg_zero] at hb
  linarith

/-- **Monotone leakage at non-negative defect.** A non-negative dissipative defect
makes the reversible charge non-increasing, `Q(t₂) ≤ Q(t₁)`. -/
theorem charge_decreasing_of_nonneg_defect (hdef : ∀ t, 0 ≤ B.defect t) {t₁ t₂ : ℝ}
    (h : t₁ ≤ t₂) : B.Q t₂ ≤ B.Q t₁ := by
  have hb := B.balance t₁ t₂ h
  have hnn : 0 ≤ ∫ t in t₁..t₂, B.defect t :=
    intervalIntegral.integral_nonneg h (fun u _ => hdef u)
  linarith

/-- **Energy/charge conservation ⇔ zero accumulated dissipative defect (A2).**
The reversible Noether charge `Q` is conserved on a forward interval `[t₁, t₂]`
*iff* the accumulated dissipative defect over that interval vanishes — the
**iff strengthening** of `conserved_of_zero_defect`.

This is the classical-mechanics counterpart to
`Physlib.Thermodynamics.SecondLaw.clausius_inequality_eq_iff_locally_reversible`:
in both cases the *equality case* of the dissipative inequality coincides with
zero entropic / dissipative activity over the interval. -/
theorem charge_conserved_iff_zero_integrated_defect
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    B.Q t₂ = B.Q t₁ ↔ ∫ t in t₁..t₂, B.defect t = 0 := by
  have hb := B.balance t₁ t₂ h
  constructor
  · intro hQ; linarith
  · intro hint; linarith

end NoetherBalance

end Physlib.ClassicalMechanics.Noether.DissipativeBalance

end
