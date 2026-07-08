/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Physlib.ClassicalMechanics.Noether.DissipativeBalance

/-!
# First law of thermodynamics — energy / heat / work balance

In the entropic-time framework the first law `ΔU = ΔQ − ΔW` is the integrated balance
equation for an open thermodynamic worldline:

  `U(t₂) − U(t₁)  =  ∫_{t₁}^{t₂} (δQ/dt − δW/dt) dt`,

with sign convention `δQ > 0` heat absorbed by the system and
`δW > 0` work done by the system on the surroundings.

This module defines a minimal `ThermodynamicWorldline` structure (internal
energy, heat-flux rate, work-rate, first-law balance) and two
theorems:

* **B3 — `internalEnergy_conserved_iff_zero_net_heatWork`** — internal
  energy is conserved on a forward interval iff the net (heat − work)
  flux over that interval vanishes.  This is the iff strengthening of
  the bare first law.

* **C1 — `internalEnergy_conserved_iff_zero_integrated_defect`** — a
  thermodynamic worldline projects to a `NoetherBalance` (with internal
  energy as the conserved charge and `δW/dt − δQ/dt` as the dissipative
  defect), and the first law is then *exactly* the iff form of
  `charge_conserved_iff_zero_integrated_defect` from
  `Physlib.ClassicalMechanics.Noether.DissipativeBalance`.

C1 is the cross-layer identification: thermodynamic energy
conservation and classical-mechanics charge conservation are the same
inequality-with-equality-case structure, just applied to different
structures.  Both reduce to the inverted-ProperTime thesis at frozen LRF.

-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics.FirstLaw

open Physlib.ClassicalMechanics.Noether.DissipativeBalance MeasureTheory

/-- **Thermodynamic worldline structure.** Internal energy `U`, heat-flux
rate `dQ_dt` (positive = heat absorbed), work-rate `dW_dt` (positive =
work done by the system), with the integrated first law as a
structural identity over the *net* flux `δQ − δW` (avoids per-summand
integrability assumptions). -/
structure ThermodynamicWorldline where
  /-- Internal energy along the worldline. -/
  U : ℝ → ℝ
  /-- Rate of heat absorbed by the system: `δQ/dt`. -/
  dQ_dt : ℝ → ℝ
  /-- Rate of work done by the system: `δW/dt`. -/
  dW_dt : ℝ → ℝ
  /-- **First law as integrated net-flux balance**: the change in internal
  energy equals the net (heat − work) integrated over the interval. -/
  firstLaw : ∀ t₁ t₂ : ℝ, t₁ ≤ t₂ →
    U t₂ - U t₁ = ∫ t in t₁..t₂, (dQ_dt t - dW_dt t)

namespace ThermodynamicWorldline

variable (T : ThermodynamicWorldline)

/-- **B3 — First law as an iff (internal-energy conservation).** Internal
energy is conserved on a forward interval `[t₁, t₂]` iff the net
(heat − work) flux over that interval vanishes. -/
theorem internalEnergy_conserved_iff_zero_net_heatWork
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    T.U t₂ = T.U t₁ ↔ ∫ t in t₁..t₂, (T.dQ_dt t - T.dW_dt t) = 0 := by
  have hb := T.firstLaw t₁ t₂ h
  constructor
  · intro hU; linarith
  · intro hint; linarith

/-- **Projection to NoetherBalance.** A thermodynamic worldline gives a
`NoetherBalance` whose conserved charge is the internal energy `U`
and whose dissipative defect is `δW/dt − δQ/dt` (the *negation* of the
net-flux integrand, so the Noether balance `Q(t₂) − Q(t₁) = −∫ defect`
matches the first law). -/
def toNoetherBalance : NoetherBalance where
  Q := T.U
  defect := fun t => T.dW_dt t - T.dQ_dt t
  balance := by
    intro t₁ t₂ h
    have hfl := T.firstLaw t₁ t₂ h
    have hneg :
        ∫ t in t₁..t₂, (T.dQ_dt t - T.dW_dt t)
          = - ∫ t in t₁..t₂, (T.dW_dt t - T.dQ_dt t) := by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext t
      ring
    linarith

/-- **C1 — Cross-layer identification.** Internal-energy conservation
on a forward interval is *exactly* the iff form of
`charge_conserved_iff_zero_integrated_defect` applied to the
`toNoetherBalance` projection.  This makes the thermodynamic first law
and the classical-mechanics Noether balance the same inequality-with-
equality-case structure on different structures. -/
theorem internalEnergy_conserved_iff_zero_integrated_defect
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    T.U t₂ = T.U t₁
      ↔ ∫ t in t₁..t₂, T.toNoetherBalance.defect t = 0 :=
  T.toNoetherBalance.charge_conserved_iff_zero_integrated_defect h

end ThermodynamicWorldline

end Physlib.Thermodynamics.FirstLaw

end
