/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.ContinuumWeakCouplingReduction
public import Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OneLevelChannelProduction

/-!
# A concrete Gaussian continuum bath: the weak-coupling certificate discharged unconditionally

`ContinuumWeakCouplingReduction` proves the weak-coupling reduction for *every* `GaussianContinuumBath`, but
supplies no named instance, so the certificates read as universally-quantified interfaces. This module gives
the first concrete witness — the **resonant unit bath** (`transitionFrequency = 0`, `spectralWeight = 1`) — for
which the whole chain closes with **no supplied certificate and no free parameter**:

* the on-shell spectral transform evaluates to the closed form `2π` (`resonantUnitBath_transform`);
* the modulated bath correlation is the exact Gaussian envelope `4π e^{−πt²}`
  (`resonantUnitBath_modulatedCorrelation`);
* the finite-window truncation error vanishes (`resonantUnitBath_truncationError_tendsto_zero`);
* the golden-rule driving rate selected by the bath at unit coupling is the concrete number `2π`
  (`resonantUnitBath_rate`);
* the resulting one-level channel has strictly positive entropy production for any interior
  non-equilibrium occupation (`resonantUnitBath_weakCoupling_closes`).

So the correlation `C(t)`, its spectral transform `J(ω₀)`, and the truncation limit are all *evaluated in
closed form* here, not assumed — a concrete instantiation of the continuum bath model that the
error-composition theorem otherwise leaves as an interface.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.LindbladDrivenLeads

open Filter Topology

/-- The **resonant unit Gaussian continuum bath**: transition frequency `0`, unit spectral weight. -/
def resonantUnitBath : GaussianContinuumBath where
  transitionFrequency := 0
  spectralWeight := 1
  spectralWeight_pos := one_pos

/-- The on-shell spectral transform of the concrete bath is exactly `2π`. -/
theorem resonantUnitBath_transform :
    resonantUnitBath.transform = ((2 * Real.pi : ℝ) : ℂ) := by
  simp [GaussianContinuumBath.transform, resonantUnitBath]

/-- The modulated bath correlation is the exact Gaussian envelope `4π e^{−πt²}`. -/
theorem resonantUnitBath_modulatedCorrelation (t : ℝ) :
    resonantUnitBath.modulatedCorrelation t
      = ((4 * Real.pi : ℝ) : ℂ) * Complex.exp ((-(Real.pi * t ^ 2) : ℝ) : ℂ) := by
  rw [resonantUnitBath.modulatedCorrelation_eq]
  simp [resonantUnitBath]

/-- The finite-window truncation error of the concrete bath vanishes. -/
theorem resonantUnitBath_truncationError_tendsto_zero :
    Tendsto resonantUnitBath.truncationError atTop (𝓝 0) :=
  resonantUnitBath.truncationError_tendsto_zero

/-- The golden-rule driving rate selected by the concrete bath at unit coupling is exactly `2π`. -/
theorem resonantUnitBath_rate (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    (resonantUnitBath.toRateData 1 f one_pos hf0 hf1).gamma = 2 * Real.pi := by
  simp only [GaussianContinuumBath.toRateData, GaussianContinuumBath.toOnShellData,
    OnShellSpectralBathData.toRateData_gamma, OnShellSpectralBathData.goldenRuleGamma,
    BathCorrelationTransformCertificate.toOnShellSpectralBathData,
    GaussianContinuumBath.toCertificate, resonantUnitBath]
  ring

/-- **The weak-coupling certificate, discharged unconditionally on the concrete bath.**  For the resonant unit
Gaussian continuum bath at unit coupling and any strictly-interior non-equilibrium occupation, all of the
following hold with **no supplied certificate**: the golden-rule driving rate is the closed-form number `2π`,
the finite-window truncation error vanishes, and the induced one-level channel has strictly positive entropy
production. This is the concrete continuum instantiation the error-composition theorem otherwise leaves open. -/
theorem resonantUnitBath_weakCoupling_closes
    (N f : ℝ) (hN0 : 0 < N) (hN1 : N < 1) (hf0 : 0 < f) (hf1 : f < 1) (hNf : N ≠ f) :
    (resonantUnitBath.toRateData 1 f one_pos hf0.le hf1.le).gamma = 2 * Real.pi
      ∧ Tendsto resonantUnitBath.truncationError atTop (𝓝 0)
      ∧ 0 < entropyProductionRate (resonantUnitBath.toRateData 1 f one_pos hf0.le hf1.le).gamma N f := by
  refine ⟨resonantUnitBath_rate f hf0.le hf1.le, resonantUnitBath_truncationError_tendsto_zero, ?_⟩
  rw [resonantUnitBath_rate f hf0.le hf1.le]
  exact entropyProductionRate_pos (by positivity) hN0 hN1 hf0 hf1 hNf

end QuantumMechanics.LindbladDrivenLeads

end
