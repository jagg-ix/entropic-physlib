/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Physlib.QuantumMechanics.PeriodicSchrodinger.Basic
public import Physlib.QuantumMechanics.PeriodicSchrodinger.BlochApproximation
public import Physlib.QuantumMechanics.PeriodicSchrodinger.Continuum
public import Physlib.QuantumMechanics.PeriodicSchrodinger.EntropicSelection
meta import Zil

/-!
# Free-Bloch phase evolution on the reciprocal-mode space

The diagonal free-Bloch one-step evolution on the reciprocal-mode coefficient
space `ℓ²(Γ.Mode, ℂ)`: each mode `γ` is multiplied by the unit phase
`exp(-i E_γ Δt)` with `E_γ = modeEnergy Γ t γ`, so the map is a linear isometric
equivalence on the possibly infinite mode space.  A generic diagonal unit-phase
unitary `unitPhaseStep` underlies it; the phases obey the additive time law and
the mode-wise Schrödinger generator law `i ∂ₜ ψ_γ = E_γ ψ_γ`.  An independent
integer clock reads `n Δt`.

The Fourier–Bloch isometry to the continuum physical-space carrier
`PeriodicSchrodingerHilbertSpace d` is recorded as an explicit obligation
(`ContinuumCoefficientIdentification`), not asserted.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution

open Physlib.QuantumMechanics.PeriodicSchrodinger

variable {I : Type*}

private theorem unitPhase_ne_zero
    (phase : I → ℂ) (hphase : ∀ i, ‖phase i‖ = 1) (i : I) :
    phase i ≠ 0 := by
  intro hi
  have hzero : (0 : ℝ) = 1 := by
    simpa [hi] using hphase i
  norm_num at hzero

/-- Pointwise multiplication by a unit-modulus phase, as an `ℓ²` state. -/
noncomputable def unitPhaseMap
    (phase : I → ℂ) (hphase : ∀ i, ‖phase i‖ = 1)
    (ψ : lp (fun _ : I => ℂ) 2) : lp (fun _ : I => ℂ) 2 :=
  ⟨fun i => phase i * ψ i,
    Memℓp.mono' ψ.property fun i => by
      rw [norm_mul, hphase i, one_mul]⟩

@[simp] theorem unitPhaseMap_apply
    (phase : I → ℂ) (hphase : ∀ i, ‖phase i‖ = 1)
    (ψ : lp (fun _ : I => ℂ) 2) (i : I) :
    unitPhaseMap phase hphase ψ i = phase i * ψ i :=
  rfl

/-- A diagonal family of unit phases defines a unitary on arbitrary-index
`ℓ²`, finite or infinite. -/
noncomputable def unitPhaseStep
    (phase : I → ℂ) (hphase : ∀ i, ‖phase i‖ = 1) :
    lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : I => ℂ) 2 where
  toFun := unitPhaseMap phase hphase
  invFun := unitPhaseMap (fun i => (phase i)⁻¹)
    (fun i => by rw [norm_inv, hphase i, inv_one])
  left_inv ψ := by
    ext i
    change (phase i)⁻¹ * (phase i * ψ i) = ψ i
    rw [← mul_assoc, inv_mul_cancel₀ (unitPhase_ne_zero phase hphase i), one_mul]
  right_inv ψ := by
    ext i
    change phase i * ((phase i)⁻¹ * ψ i) = ψ i
    rw [← mul_assoc, mul_inv_cancel₀ (unitPhase_ne_zero phase hphase i), one_mul]
  map_add' ψ φ := by
    ext i
    change phase i * (ψ i + φ i) = phase i * ψ i + phase i * φ i
    ring
  map_smul' c ψ := by
    ext i
    change phase i * (c * ψ i) = c * (phase i * ψ i)
    ring
  norm_map' ψ := by
    rw [lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num),
      lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num)]
    congr 1
    refine tsum_congr fun i => ?_
    have h : ‖unitPhaseMap phase hphase ψ i‖ = ‖ψ i‖ := by
      rw [unitPhaseMap_apply, norm_mul, hphase i, one_mul]
    exact congrArg (· ^ ENNReal.toReal 2) h

@[simp] theorem unitPhaseStep_apply
    (phase : I → ℂ) (hphase : ∀ i, ‖phase i‖ = 1)
    (ψ : lp (fun _ : I => ℂ) 2) (i : I) :
    unitPhaseStep phase hphase ψ i = phase i * ψ i :=
  rfl

/-- Free Bloch evolution phase for one reciprocal mode. -/
noncomputable def modePhase {d : ℕ}
    (Γ : ReciprocalLattice d) (t : QuantumMechanics.PeriodicSchrodinger.Momentum d)
    (Δt : ℝ) (γ : Γ.Mode) : ℂ :=
  Complex.exp ((-(modeEnergy Γ t γ * Δt) : ℝ) * Complex.I)

/-- Every free Bloch phase has unit norm. -/
@[simp] theorem norm_modePhase {d : ℕ}
    (Γ : ReciprocalLattice d) (t : QuantumMechanics.PeriodicSchrodinger.Momentum d)
    (Δt : ℝ) (γ : Γ.Mode) :
    ‖modePhase Γ t Δt γ‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- Bloch phases obey the additive time law. -/
theorem modePhase_add {d : ℕ}
    (Γ : ReciprocalLattice d) (t : QuantumMechanics.PeriodicSchrodinger.Momentum d)
    (Δt₁ Δt₂ : ℝ) (γ : Γ.Mode) :
    modePhase Γ t (Δt₁ + Δt₂) γ =
      modePhase Γ t Δt₁ γ * modePhase Γ t Δt₂ γ := by
  unfold modePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The diagonal free-Bloch unitary on the full reciprocal-mode `ℓ²` space. -/
noncomputable def periodicStateStep {d : ℕ}
    (Γ : ReciprocalLattice d) (t : QuantumMechanics.PeriodicSchrodinger.Momentum d) (Δt : ℝ) :
    lp (fun _ : Γ.Mode => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : Γ.Mode => ℂ) 2 :=
  unitPhaseStep (modePhase Γ t Δt) (norm_modePhase Γ t Δt)

/-- The periodic state step acts modewise by the exact free Bloch phase. -/
@[simp, zil_level structural] theorem periodicStateStep_apply {d : ℕ}
    (Γ : ReciprocalLattice d) (t : QuantumMechanics.PeriodicSchrodinger.Momentum d) (Δt : ℝ)
    (ψ : lp (fun _ : Γ.Mode => ℂ) 2) (γ : Γ.Mode) :
    periodicStateStep Γ t Δt ψ γ =
      modePhase Γ t Δt γ * ψ γ :=
  rfl

/-- The free-Bloch steps compose according to addition of durations. -/
@[zil_level structural]
theorem periodicStateStep_add {d : ℕ}
    (Γ : ReciprocalLattice d) (t : QuantumMechanics.PeriodicSchrodinger.Momentum d)
    (Δt₁ Δt₂ : ℝ) (ψ : lp (fun _ : Γ.Mode => ℂ) 2) :
    periodicStateStep Γ t Δt₁ (periodicStateStep Γ t Δt₂ ψ) =
      periodicStateStep Γ t (Δt₁ + Δt₂) ψ := by
  ext γ
  rw [periodicStateStep_apply, periodicStateStep_apply,
    periodicStateStep_apply, modePhase_add]
  ring

/-- The Bloch phase satisfies the mode-frequency derivative law:
`d/ds modePhase = −i·E_γ · modePhase`. -/
theorem modePhase_hasDerivAt {d : ℕ}
    (Γ : ReciprocalLattice d)
    (t : QuantumMechanics.PeriodicSchrodinger.Momentum d) (γ : Γ.Mode)
    (s : ℝ) :
    HasDerivAt (fun Δt : ℝ => modePhase Γ t Δt γ)
      (-(Complex.I) * (modeEnergy Γ t γ) * modePhase Γ t s γ) s := by
  have hfun : (fun Δt : ℝ => modePhase Γ t Δt γ)
      = fun Δt : ℝ =>
          Complex.exp ((-(Complex.I) * (modeEnergy Γ t γ)) * (Δt : ℂ)) := by
    funext Δt
    unfold modePhase
    congr 1
    push_cast
    ring
  rw [hfun]
  have hlin : HasDerivAt
      (fun Δt : ℝ => (-(Complex.I) * (modeEnergy Γ t γ)) * (Δt : ℂ))
      (-(Complex.I) * (modeEnergy Γ t γ)) s := by
    simpa using
      (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul
        (-(Complex.I) * (modeEnergy Γ t γ : ℂ))
  have h := hlin.cexp
  have harg : Complex.exp ((-(Complex.I) * (modeEnergy Γ t γ)) * (s : ℂ))
      = modePhase Γ t s γ := by
    unfold modePhase
    congr 1
    push_cast
    ring
  rw [harg] at h
  convert h using 1
  ring

/-- **The mode-wise Schrödinger equation of the diagonal Bloch evolution**:
every reciprocal-mode coefficient of the periodic state step
satisfies `i·∂ₜ ψ_γ(t) = E_γ · ψ_γ(t)` — the generator of the diagonal
unitary is the mode energy, pointwise.  The operator-exponential form on the
full unbounded periodic-potential Hamiltonian remains a recorded
continuum-identification obligation
(`periodicPotentialOperator_isSelfAdjoint` is the cited self-adjoint
carrier). -/
@[zil_level physical_theorem]
theorem periodic_mode_schrodinger {d : ℕ}
    (Γ : ReciprocalLattice d)
    (t : QuantumMechanics.PeriodicSchrodinger.Momentum d)
    (ψ : lp (fun _ : Γ.Mode => ℂ) 2) (γ : Γ.Mode) (s : ℝ) :
    HasDerivAt (fun Δt : ℝ => (periodicStateStep Γ t Δt ψ : Γ.Mode → ℂ) γ)
      (-(Complex.I) * (modeEnergy Γ t γ) *
        (periodicStateStep Γ t s ψ : Γ.Mode → ℂ) γ) s := by
  have hfun : (fun Δt : ℝ => (periodicStateStep Γ t Δt ψ : Γ.Mode → ℂ) γ)
      = fun Δt : ℝ => modePhase Γ t Δt γ * ψ γ := by
    funext Δt
    exact periodicStateStep_apply Γ t Δt ψ γ
  rw [hfun, periodicStateStep_apply]
  have h := (modePhase_hasDerivAt Γ t γ s).mul_const (ψ γ)
  have hval : -(Complex.I) * (modeEnergy Γ t γ) * modePhase Γ t s γ * ψ γ
      = -(Complex.I) * (modeEnergy Γ t γ) * (modePhase Γ t s γ * ψ γ) := by
    ring
  rw [← hval]
  exact h

/-- One step of the independent integer clock. -/
def integerClockStep : ℤ ≃ ℤ where
  toFun n := n + 1
  invFun n := n - 1
  left_inv n := by simp
  right_inv n := by simp

/-- Real clock reading `n Δt`. -/
def integerClockAge (Δt : ℝ) (n : ℤ) : ℝ :=
  (n : ℝ) * Δt

/-- The integer clock advances by exactly `Δt`. -/
@[zil_level structural]
theorem integerClockAge_step (Δt : ℝ) (n : ℤ) :
    integerClockAge Δt (integerClockStep n) =
      integerClockAge Δt n + Δt := by
  unfold integerClockAge
  show ((n + 1 : ℤ) : ℝ) * Δt = (n : ℝ) * Δt + Δt
  push_cast
  ring

/-- Data required to identify the reciprocal-mode coefficient carrier with the
continuum physical-space periodic Schrödinger Hilbert space. No inhabitant is
asserted here. -/
structure ContinuumCoefficientIdentification (d : ℕ)
    (Γ : ReciprocalLattice d) where
  transform :
    PeriodicSchrodingerHilbertSpace d ≃ₗᵢ[ℂ] lp (fun _ : Γ.Mode => ℂ) 2


end Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.PeriodicSchrodinger.BlochPhaseEvolution

zil attach periodic_mode_schrodinger where
  formalizes @ "claim:the-periodic-step-satisfies-the-mode-schrodinger-equation-in-physical-time",
  supported_by @ "lean:Physlib.QuantumMechanics.PeriodicSchrodinger.modeEnergy",
  supported_by @ "lean:Physlib.QuantumMechanics.PeriodicSchrodinger.periodicPotentialOperator_isSelfAdjoint",
  caveat @ "claim:the-generator-law-is-mode-wise-the-physical-space-form-awaits-a-fourier-bloch-isometry-and-self-adjoint-exponentiation"

zil_file_contract physlib.blochPhaseEvolution where
  promises "The free Bloch mode energies generate a diagonal unit-phase unitary on the reciprocal-mode l2 space: the underlying unitPhaseStep is a linear isometric equivalence, the phases obey the additive time law, the diagonal step acts modewise by the exact free Bloch phase and satisfies the mode-wise Schrodinger generator law i d_t psi_gamma = E_gamma psi_gamma in physical time, and an independent integer clock reads n Delta t. The Fourier-Bloch isometry to the continuum physical-space carrier is recorded as an obligation, not asserted."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.PeriodicSchrodinger.ReciprocalLattice",
    "lean:Physlib.QuantumMechanics.PeriodicSchrodinger.modeEnergy"
  ]
  forbids_substitutes [
    "a Fourier-Bloch isometry to the continuum physical-space L2 carrier",
    "exponentiation of the full unbounded periodic-potential Hamiltonian"
  ]
  witnessed_by [
    periodicStateStep_apply,
    periodicStateStep_add,
    periodic_mode_schrodinger,
    integerClockAge_step
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.blochPhaseEvolution
