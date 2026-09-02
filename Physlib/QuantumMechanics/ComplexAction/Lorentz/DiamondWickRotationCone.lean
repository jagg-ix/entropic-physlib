/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondBisognanoWichmannKMS

/-!
# Appendix A of Sciama–Candelas–Deutsch: the rotation to complex time, read by the three clocks

Sciama, Candelas, Deutsch (1981), Appendix A ("Analytic properties of the manifold: the rotation to complex
time").  Setting `τ = −iη` in the Rindler line element gives `ds² = ξ²dη² + dξ² + dy² + dz²` — a **flat
two-space in polar coordinates** `(ξ, η)`, with `ξ` the radius and `η` the angle (`λ = ξ sin η`, `x = ξ cos
η`).  The point `ξ = 0` (the horizon) is a **conical singularity unless `η` is periodic with period `2π`**;
equivalently the propagator is periodic in Rindler time `τ` with period `2πi`.  "The fact that the Minkowski
propagator is periodic in Rindler time with period `2πi` is intimately related to the fact that the Minkowski
vacuum contains a thermal distribution" — this *is* the Unruh/KMS thermality, of geometric origin.

The three-clock reading: the Wick rotation `τ = −iη` sends the **Lorentzian** diamond mode `(cosh τ, sinh τ)`
on the mass-shell hyperbola `cosh²−sinh²=1` to the **Euclidean** `(cos η, sin η)` on the **circle**
`cos²+sin²=1`, and the modular/KMS period `β = 2π` (`DiamondBisognanoWichmannKMS`, imaginary rapidity `2πi`)
becomes the angle `2π` that closes the circle — cone smoothness at the horizon.

* `wick_diamondEnergy_eq_cos`, `wick_diamondMomentum_eq_sin` — the Wick rotation `cosh(iη)=cos η`,
  `sinh(iη)=i sin η` (diamond energy/momentum → Euclidean angle).
* `euclidean_circle` — the Wick-rotated mass shell is the Euclidean circle `cos²η+sin²η=1`.
* `coneSmoothness_period` — the Euclidean angle has period `2π` (regularity at `ξ=0`).
* `diamond_kms_period_eq_cone_angle` — the diamond KMS `2πi` period, at imaginary rapidity `η`, lands on the
  same Euclidean angle `cos η`: the modular period *is* the cone angle.

Honest scope: the algebraic Wick-rotation identities and the cone/circle periodicity; the metric regularity
argument and the field-theoretic thermality (Fulling vacuum) are contextualized, not reconstructed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondWickRotationCone

open Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondBisognanoWichmannKMS
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SummersRelativisticVacuum

/-- **[Wick rotation of the diamond energy] `cosh(iη) = cos η`.**  Under `τ = −iη`, the diamond horizon energy
becomes the Euclidean angle cosine — the Lorentzian time direction rotates into the polar angle. -/
theorem wick_diamondEnergy_eq_cos (η : ℝ) :
    diamondEnergyC ((η : ℂ) * Complex.I) = Complex.cos (η : ℂ) := by
  unfold diamondEnergyC
  rw [Complex.cosh_mul_I]

/-- **[Wick rotation of the diamond momentum] `sinh(iη) = sin η · i`.**  The momentum rotates into `i` times
the Euclidean angle sine. -/
theorem wick_diamondMomentum_eq_sin (η : ℝ) :
    diamondMomentumC ((η : ℂ) * Complex.I) = Complex.sin (η : ℂ) * Complex.I := by
  unfold diamondMomentumC
  rw [Complex.sinh_mul_I]

/-- **[Euclidean mass shell is the circle] `cos²η + sin²η = 1`.**  The Wick rotation sends the Lorentzian
mass-shell hyperbola `cosh²−sinh²=1` to the Euclidean circle — the boost orbit becomes a rotation orbit. -/
theorem euclidean_circle (η : ℝ) : Real.cos η ^ 2 + Real.sin η ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq η

/-- **[Cone smoothness] the Euclidean angle has period `2π`.**  Regularity at `ξ = 0` (the horizon) — no
conical singularity — requires exactly `η ↦ η + 2π` invariance; this `2π` is the Unruh/KMS period. -/
theorem coneSmoothness_period (η : ℝ) :
    Real.cos (η + 2 * Real.pi) = Real.cos η ∧ Real.sin (η + 2 * Real.pi) = Real.sin η :=
  ⟨Real.cos_add_two_pi η, Real.sin_add_two_pi η⟩

/-- **[Modular period = cone angle] `diamondEnergyC(iη + 2πi) = cos η`.**  The diamond energy KMS-shifted by
the Unruh inverse temperature `β = 2π` (`DiamondBisognanoWichmannKMS.diamond_energy_kms_periodic`), evaluated
at imaginary rapidity `η`, returns the same Euclidean angle `cos η` — the Bisognano–Wichmann `2πi` modular
period is Appendix A's `2π` cone angle. -/
theorem diamond_kms_period_eq_cone_angle (η : ℝ) :
    diamondEnergyC ((η : ℂ) * Complex.I + (unruhInverseTemperature : ℂ) * Complex.I)
      = Complex.cos (η : ℂ) := by
  rw [diamond_energy_kms_periodic]
  exact wick_diamondEnergy_eq_cos η

end Physlib.QuantumMechanics.ComplexAction.Lorentz.DiamondWickRotationCone

end
