/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.QIFThermodynamicReversible

/-!
# Adapting the effective mass to massless bosons: inertia without rest mass

The Nagao–Nielsen effective mass (`PathIntegral.MomentumPathIntegral.effectiveMass`, arXiv:1304.4017
Eq. 5.10)

  `m_eff = m_R + m_I²/m_R = (m_R² + m_I²)/m_R = |m|²/Re m`

**divides by the real (rest) mass `m_R`**, so it is singular precisely for a *massless*
boson (`m_R = 0`): a photon, gluon, or any gapless gauge boson has no rest-mass term to
include the imaginary-mass correction. Yet such bosons manifestly encode **inertia** — light
of energy `E` records inertial mass `E/c²` (mass–energy equivalence), and a boson in a
thermal bath acquires a thermal mass set by `k_B T`. This file adapts the §5 objects to that
regime.

## The mechanism: a *generated* real scale replaces the rest mass

For a massless boson the inertial mass is **generated**, not fundamental:

* **Relativistic (energy) inertia** — `relativisticInertialMass E c = E/c²`: a massless
  boson of energy `E` has inertial mass `E/c²` even though its rest mass is `0`
  (`E = m_inert·c²`, the `massEnergyEquivalence` of `Thermodynamics.VerlindeNewtonGravity`
  with `M ↦ m_inert`).
* **Thermal inertia** — `thermalInertialMass kB T c = k_B T/c²`: a gapless boson dressed by
  a thermal frame at temperature `T` acquires an inertial-mass scale `k_B T/c²`, which is
  exactly `ℏ·λ_KMS/c²` for the QIF thermal rate `λ_KMS = k_B T/ℏ`
  (`thermalInertialMass_eq_hbar_kmsRate`, linking to
  `QuantumInertialFrame.kmsThermalRate`).

Using this generated scale `μ > 0` in place of the (zero) rest mass, the §5 effective mass
`bosonicEffectiveMass μ m_I = μ + m_I²/μ` is finite and the §5 theorems lift verbatim:
`bosonicEffectiveMass_eq_self_iff` (`m_eff = μ ⟺ m_I = 0`), `bosonicEffectiveMass_ge`,
and the momentum relation `p = m_eff q̇` (`bosonic_momentum_relation`).

## Link to the `T = 0` / reversible / no-information arc

`thermalInertialMass_zero_iff`: the generated thermal scale vanishes **iff `T = 0`**. At the
zero-temperature, reversible-QIF, no-information point (`TimeOperator.QIFThermodynamicReversible`),
the massless boson has *no* inertia and — by reversibility — `m_I = 0` as well: no rest mass,
no thermal mass, no imaginary mass. So the boson is inertia-free exactly where the action
has no information, and acquires inertial mass `k_B T/c² > 0` the moment `T > 0`.

## References

* K. Nagao, H. B. Nielsen, arXiv:1304.4017, Eq. 5.10 (`m_eff`); arXiv:1104.3381 (`H_C`).
* Mass–energy equivalence `E = m c²` (`Thermodynamics.VerlindeNewtonGravity.massEnergyEquivalence`).
* Thermal field theory: gapless bosons acquire a thermal mass `∼ g T`; here the
  inertial-energy scale `k_B T`. Connes–Rovelli thermal time `λ_KMS = k_B T/ℏ`
  (`QuantumMechanics.FiniteTarget.kmsThermalRate`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open QuantumMechanics.FiniteTarget

namespace Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass

/-! ## §A — the rest-mass effective mass is singular for a massless boson -/

/-- **`m_eff = |m|²/m_R`** (Nagao–Nielsen Eq. 5.10 rewritten): the effective mass is the
squared modulus of the complex mass over its real part, `(m_R² + m_I²)/m_R`. This makes the
massless singularity explicit — for `m_R = 0` and `m_I ≠ 0` there is no real `m_eff`. -/
theorem effectiveMass_eq_normSq_div (m_R m_I : ℝ) (hm_R : m_R ≠ 0) :
    effectiveMass m_R m_I = (m_R ^ 2 + m_I ^ 2) / m_R := by
  unfold effectiveMass
  field_simp

/-! ## §B — generated inertial scales for a massless boson -/

/-- **Relativistic inertial mass** `m_inert = E/c²`: a massless boson of energy `E` records
inertia `E/c²` despite zero rest mass (mass–energy equivalence). -/
def relativisticInertialMass (E c : ℝ) : ℝ := E / c ^ 2

/-- A massless boson of positive energy has positive inertial mass. -/
theorem relativisticInertialMass_pos (E c : ℝ) (hE : 0 < E) (hc : 0 < c) :
    0 < relativisticInertialMass E c := by
  unfold relativisticInertialMass; positivity

/-- **`E = m_inert·c²`**: the energy is the inertial mass times `c²` (the
`massEnergyEquivalence` of `VerlindeNewtonGravity`, read with `M ↦ m_inert`). -/
theorem energy_eq_inertialMass_mul_c_sq (E c : ℝ) (hc : 0 < c) :
    E = relativisticInertialMass E c * c ^ 2 := by
  unfold relativisticInertialMass
  field_simp

/-- **Thermal inertial mass** `μ_th = k_B T/c²`: the inertial-mass scale a gapless boson
acquires in a thermal frame at temperature `T`. -/
def thermalInertialMass (kB T c : ℝ) : ℝ := kB * T / c ^ 2

/-- **The thermal inertial mass is the QIF thermal rate in mass units**:
`μ_th = ℏ·λ_KMS/c²` with `λ_KMS = k_B T/ℏ` (`kmsThermalRate`). -/
theorem thermalInertialMass_eq_hbar_kmsRate (kB T c ℏ : ℝ) (hℏ : 0 < ℏ) (hc : 0 < c) :
    thermalInertialMass kB T c = ℏ * kmsThermalRate kB T ℏ / c ^ 2 := by
  unfold thermalInertialMass kmsThermalRate
  have hℏ' : ℏ ≠ 0 := hℏ.ne'
  have hc' : c ≠ 0 := hc.ne'
  field_simp

/-- **The massless boson is inertia-free iff `T = 0`**: the generated thermal scale vanishes
exactly at zero temperature — the reversible-QIF / no-information ground state. -/
theorem thermalInertialMass_zero_iff (kB T c : ℝ) (hkB : 0 < kB) (hc : 0 < c) :
    thermalInertialMass kB T c = 0 ↔ T = 0 := by
  unfold thermalInertialMass
  rw [div_eq_zero_iff, mul_eq_zero]
  simp [ne_of_gt hkB, (pow_pos hc 2).ne']

/-- At positive temperature the massless boson has positive inertial mass. -/
theorem thermalInertialMass_pos (kB T c : ℝ) (hkB : 0 < kB) (hT : 0 < T) (hc : 0 < c) :
    0 < thermalInertialMass kB T c := by
  unfold thermalInertialMass; positivity

/-! ## §C — bosonic effective mass on the generated scale -/

/-- **Bosonic effective mass**: the Nagao–Nielsen `m_eff` evaluated on a *generated* real
inertial scale `μ` (relativistic `E/c²` or thermal `k_B T/c²`) in place of the absent rest
mass — `m_eff = μ + m_I²/μ`, finite whenever `μ > 0`. -/
def bosonicEffectiveMass (μ m_I : ℝ) : ℝ := effectiveMass μ m_I

/-- **Reversibility ⟺ no imaginary-mass correction** lifts to the bosonic scale:
`m_eff = μ ⟺ m_I = 0`. -/
theorem bosonicEffectiveMass_eq_self_iff (μ m_I : ℝ) (hμ : μ ≠ 0) :
    bosonicEffectiveMass μ m_I = μ ↔ m_I = 0 :=
  effectiveMass_eq_self_iff μ m_I hμ

/-- The generated scale only adds inertia: `μ ≤ m_eff`. -/
theorem bosonicEffectiveMass_ge (μ m_I : ℝ) (hμ : 0 < μ) :
    μ ≤ bosonicEffectiveMass μ m_I :=
  effectiveMass_ge μ m_I hμ

/-- **The momentum relation `p = m_eff q̇`** holds on the generated scale, with the same real
effective Lagrangian `L_eff = ½ m_eff q̇² − V_R` (Nagao–Nielsen Eqs. 5.11, 5.14). -/
theorem bosonic_momentum_relation (μ m_I V_R qdot : ℝ) :
    HasDerivAt (fun q' : ℝ => effectiveLagrangian μ m_I V_R q')
      (bosonicEffectiveMass μ m_I * qdot) qdot :=
  effective_momentum_relation μ m_I V_R qdot

/-- **Capstone — a massless boson on the thermal scale.** With the generated thermal inertial
mass `μ_th = k_B T/c² > 0` (`T > 0`), the massless boson has a finite effective mass
`m_eff = μ_th + m_I²/μ_th`, equal to `μ_th` exactly at reversibility (`m_I = 0`). At `T = 0`
the scale vanishes (`thermalInertialMass_zero_iff`) and — being the reversible / no-information
point — `m_I = 0` too: no rest mass, no thermal mass, no imaginary mass, no inertia. -/
theorem thermalBosonicEffectiveMass_eq_self_iff
    (kB T c m_I : ℝ) (hkB : 0 < kB) (hT : 0 < T) (hc : 0 < c) :
    bosonicEffectiveMass (thermalInertialMass kB T c) m_I = thermalInertialMass kB T c
      ↔ m_I = 0 :=
  bosonicEffectiveMass_eq_self_iff _ m_I (thermalInertialMass_pos kB T c hkB hT hc).ne'

end Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass

end

end
