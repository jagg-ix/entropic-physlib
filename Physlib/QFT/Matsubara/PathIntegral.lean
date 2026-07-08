/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.NonHermitian.WickRotation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Matsubara / thermal path integral, Wick's theorem, and Wick rotation

This module adds the **imaginary-time (thermal) circle** layer on top
of `Physlib.QuantumMechanics.NonHermitian.WickRotation`, and connects it to all three
neighbouring structures:

* the **non-Hermitian Schrödinger** evolution factor `u(t) = exp(−i E_C t/ℏ)`;
* **Wick rotation** `t ↦ −iτ` (reversible-sector continuation);
* Physlib's **Wick's theorem** (the contraction expansion of time-ordered
  products).

The path-integral kernel is `lorentzianKernel S_R S_I ℏ = exp(i S_R/ℏ − S_I/ℏ)`
(our `complexActionWeight`) and the propagator is `lorentzianPropagator H t ℏ`
(our `evolutionFactor`).

## Thermal circle and Matsubara frequencies

A `ThermalCircle` records `β, ℏ > 0` with Euclidean period `βℏ`. The bosonic and
fermionic Matsubara frequencies are `ω_n = 2πn/(βℏ)` and `ω_n = (2n+1)π/(βℏ)`.

## KMS / boundary conditions

The bosonic Matsubara mode `exp(i ω_n τ)` is **periodic** on the circle
(`matsubaraModeBoson_periodic`) and the fermionic mode is **antiperiodic**
(`matsubaraModeFermion_antiperiodic`) — the thermal (KMS) boundary conditions.

## Wick rotation ⇒ Boltzmann weight

Wick-rotating the reversible phase to the full thermal period `τ = βℏ` produces
the Boltzmann weight `exp(−βE_R)` (`euclidean_reversiblePhase_at_thermalPeriod_eq_boltzmann`):
the thermal weight is the imaginary-time evolution over one period.

## Path integral ⇔ Wick's theorem

The Matsubara/thermal weight is a scalar in the Wick algebra, so it distributes
over the contraction expansion (`matsubaraWeight_smul_wicks_theorem`), exactly as
the Lorentzian propagator weight does.

## Reduction

At `H_I = 0` the Lorentzian propagator is the pure reversible phase, whose
one-period Wick rotation is the Boltzmann weight
(`boltzmann_from_unitary_sector`).


## References

- **Matsubara 1955** — *A New Approach to Quantum-Statistical Mechanics*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.QuantumMechanics.NonHermitian.WickRotation
namespace Physlib.QFT.Matsubara.PathIntegral

open QuantumInfo.Finite FieldSpecification

/-! ## §1 — Thermal circle and Matsubara frequencies -/

/-- Euclidean thermal circle data: inverse temperature `β` and `ℏ`, both positive.
The Euclidean time has period `βℏ`. -/
structure ThermalCircle where
  /-- Inverse temperature `β = 1/(k_B T)`. -/
  beta : ℝ
  /-- Reduced Planck constant. -/
  hbar : ℝ
  /-- `β > 0`. -/
  beta_pos : 0 < beta
  /-- `ℏ > 0`. -/
  hbar_pos : 0 < hbar

namespace ThermalCircle

/-- Euclidean thermal period `βℏ`. -/
def period (T : ThermalCircle) : ℝ := T.beta * T.hbar

theorem period_pos (T : ThermalCircle) : 0 < T.period :=
  mul_pos T.beta_pos T.hbar_pos

theorem period_ne_zero (T : ThermalCircle) : T.period ≠ 0 :=
  ne_of_gt T.period_pos

/-- Bosonic Matsubara frequency `ω_n = 2πn/(βℏ)`. -/
def matsubaraOmegaBoson (T : ThermalCircle) (n : ℤ) : ℝ :=
  (2 * Real.pi * (n : ℝ)) / T.period

/-- Fermionic Matsubara frequency `ω_n = (2n+1)π/(βℏ)`. -/
def matsubaraOmegaFermion (T : ThermalCircle) (n : ℤ) : ℝ :=
  ((2 * (n : ℝ) + 1) * Real.pi) / T.period

/-- `ω_n · βℏ = 2πn` for the bosonic frequency. -/
theorem matsubaraOmegaBoson_mul_period (T : ThermalCircle) (n : ℤ) :
    T.matsubaraOmegaBoson n * T.period = 2 * Real.pi * (n : ℝ) := by
  unfold matsubaraOmegaBoson
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self T.period_ne_zero, mul_one]

/-- `ω_n · βℏ = (2n+1)π` for the fermionic frequency. -/
theorem matsubaraOmegaFermion_mul_period (T : ThermalCircle) (n : ℤ) :
    T.matsubaraOmegaFermion n * T.period = (2 * (n : ℝ) + 1) * Real.pi := by
  unfold matsubaraOmegaFermion
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self T.period_ne_zero, mul_one]

end ThermalCircle

/-! ## §2 — Matsubara modes and KMS boundary conditions -/

/-- Bosonic Matsubara mode `exp(i ω_n τ)` on the Euclidean circle. -/
def matsubaraModeBoson (T : ThermalCircle) (n : ℤ) (τ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((T.matsubaraOmegaBoson n * τ : ℝ) : ℂ))

/-- Fermionic Matsubara mode `exp(i ω_n τ)` on the Euclidean circle. -/
def matsubaraModeFermion (T : ThermalCircle) (n : ℤ) (τ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((T.matsubaraOmegaFermion n * τ : ℝ) : ℂ))

/-- **Bosonic KMS boundary condition**: the bosonic Matsubara mode is *periodic*
on the Euclidean circle, `φ(τ + βℏ) = φ(τ)`. -/
theorem matsubaraModeBoson_periodic (T : ThermalCircle) (n : ℤ) (τ : ℝ) :
    matsubaraModeBoson T n (τ + T.period) = matsubaraModeBoson T n τ := by
  have harg : Complex.I * ((T.matsubaraOmegaBoson n * (τ + T.period) : ℝ) : ℂ)
      = Complex.I * ((T.matsubaraOmegaBoson n * τ : ℝ) : ℂ)
        + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [show T.matsubaraOmegaBoson n * (τ + T.period)
          = T.matsubaraOmegaBoson n * τ + 2 * Real.pi * (n : ℝ)
        from by rw [mul_add, T.matsubaraOmegaBoson_mul_period]]
    push_cast; ring
  unfold matsubaraModeBoson
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Fermionic KMS boundary condition**: the fermionic Matsubara mode is
*antiperiodic* on the Euclidean circle, `ψ(τ + βℏ) = −ψ(τ)`. -/
theorem matsubaraModeFermion_antiperiodic (T : ThermalCircle) (n : ℤ) (τ : ℝ) :
    matsubaraModeFermion T n (τ + T.period) = - matsubaraModeFermion T n τ := by
  have harg : Complex.I * ((T.matsubaraOmegaFermion n * (τ + T.period) : ℝ) : ℂ)
      = Complex.I * ((T.matsubaraOmegaFermion n * τ : ℝ) : ℂ)
        + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        + (Real.pi : ℂ) * Complex.I := by
    rw [show T.matsubaraOmegaFermion n * (τ + T.period)
          = T.matsubaraOmegaFermion n * τ + (2 * (n : ℝ) + 1) * Real.pi
        from by rw [mul_add, T.matsubaraOmegaFermion_mul_period]]
    push_cast; ring
  unfold matsubaraModeFermion
  rw [harg, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_pi_mul_I, mul_one, mul_neg_one]

/-! ## §3 — Wick rotation to the thermal period gives the Boltzmann weight -/

/-- **Thermal Boltzmann weight from Wick rotation.** Wick-rotating the reversible
phase `exp(−i E_R t/ℏ)` to the full thermal period `t = −iβℏ` yields the
Boltzmann weight `exp(−βE_R)` — the imaginary-time evolution over one period of
the thermal circle. -/
theorem euclidean_reversiblePhase_at_thermalPeriod_eq_boltzmann
    (E_R : ℝ) (T : ThermalCircle) :
    reversiblePhaseC E_R T.hbar (-Complex.I * (T.period : ℂ)) =
      ((Real.exp (-(T.beta * E_R)) : ℝ) : ℂ) := by
  rw [reversiblePhase_wickRotation]
  have hℏ : T.hbar ≠ 0 := ne_of_gt T.hbar_pos
  norm_cast
  congr 1
  unfold ThermalCircle.period
  field_simp

/-! ## §4 — Matsubara / thermal path-integral weight and Wick's theorem -/

/-- **Thermal (Matsubara) path-integral weight** `exp(−βE_R)` — the diagonal
Euclidean weight that the imaginary-time path integral assigns to an energy
level. It is the `τ = βℏ` Wick rotation of the reversible propagator phase. -/
def matsubaraWeight (E_R : ℝ) (T : ThermalCircle) : ℂ :=
  ((Real.exp (-(T.beta * E_R)) : ℝ) : ℂ)

/-- The thermal weight is the one-period Wick rotation of the reversible phase. -/
theorem matsubaraWeight_eq_wickRotation (E_R : ℝ) (T : ThermalCircle) :
    matsubaraWeight E_R T = reversiblePhaseC E_R T.hbar (-Complex.I * (T.period : ℂ)) :=
  (euclidean_reversiblePhase_at_thermalPeriod_eq_boltzmann E_R T).symm

/-- The thermal weight is real and positive (a genuine Boltzmann factor). -/
theorem matsubaraWeight_pos (E_R : ℝ) (T : ThermalCircle) :
    0 < (matsubaraWeight E_R T).re := by
  unfold matsubaraWeight
  rw [Complex.ofReal_re]
  exact Real.exp_pos _

/-- **The thermal path-integral weight distributes over the Wick-contraction
expansion**: `w_β • 𝓣(ofFieldOpList φs) = ∑ φsΛ, w_β • φsΛ.wickTerm`. The thermal
weight factors uniformly across the time-ordered Wick expansion exactly as the
Lorentzian propagator weight does (the contraction enumeration being HepLean's
`wicks_theorem`). -/
theorem matsubaraWeight_smul_wicks_theorem
    {𝓕 : FieldSpecification} (E_R : ℝ) (T : ThermalCircle) (φs : List 𝓕.FieldOp) :
    matsubaraWeight E_R T •
        WickAlgebra.timeOrder (WickAlgebra.ofFieldOpList φs) =
      ∑ φsΛ : WickContraction φs.length, matsubaraWeight E_R T • φsΛ.wickTerm := by
  rw [wicks_theorem φs, Finset.smul_sum]

/-- The thermal weight commutes through Wick time-ordering. -/
theorem timeOrder_matsubaraWeight_smul
    {𝓕 : FieldSpecification} (E_R : ℝ) (T : ThermalCircle) (A : 𝓕.WickAlgebra) :
    WickAlgebra.timeOrder (matsubaraWeight E_R T • A) =
      matsubaraWeight E_R T • WickAlgebra.timeOrder A :=
  map_smul WickAlgebra.timeOrder (matsubaraWeight E_R T) A

/-! ## §5 — Non-Hermitian Schrödinger ⇒ Wick rotation ⇒ Matsubara -/

/-- **Theorem.** At `H_I = 0` the non-Hermitian Schrödinger evolution factor is
the pure reversible (unitary) phase, and the one-period Wick rotation of that
phase is the thermal Boltzmann weight. This chains
non-Hermitian Schrödinger → Wick rotation → Matsubara/thermal:

* (i) `evolutionFactor E_R 0 ℏ t = reversiblePhase E_R ℏ t`  (unitary sector);
* (ii) the `τ = βℏ` Wick rotation of that phase is `exp(−βE_R)`. -/
theorem boltzmann_from_unitary_sector (E_R : ℝ) (T : ThermalCircle) (t : ℝ) :
    evolutionFactor E_R 0 T.hbar t = reversiblePhase E_R T.hbar t
    ∧ reversiblePhaseC E_R T.hbar (-Complex.I * (T.period : ℂ)) = matsubaraWeight E_R T :=
  ⟨evolutionFactor_at_H_I_zero E_R T.hbar t,
   euclidean_reversiblePhase_at_thermalPeriod_eq_boltzmann E_R T⟩

end Physlib.QFT.Matsubara.PathIntegral

end
