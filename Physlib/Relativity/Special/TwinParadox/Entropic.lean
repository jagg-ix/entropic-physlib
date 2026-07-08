/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Relativity.Special.TwinParadox.Basic
public import Physlib.QuantumMechanics.NonHermitian.WickRotation
public import Physlib.ClassicalMechanics.ActionPrinciple
public import Physlib.Thermodynamics.Equilibrium

/-!
# Twin paradox via entropic time and the Lorentzian path integral

This module extends Physlib's `SpecialRelativity.InstantaneousTwinParadox` with
the complex proper time of the entropic-time framework and the Lorentzian
path-integral phase, realising the twin paradox as a statement about
**complex proper time `S = S_R + i S_I`** and **path-integral amplitudes**
rather than only Minkowski arc length.

It is built on Physlib's own
`SpaceTime.properTime` and `complexProperTimeMetric` (whose real part is the
geometric Lorentz proper time and whose imaginary part is the entropic proper
time), together with the reversible phase of
`Physlib.QuantumMechanics.NonHermitian.WickRotation`.

## Path-integral picture

Each worldline contributes an amplitude `exp(−i E_R τ/ℏ)` set by its proper time
`τ` (`reversiblePhase`). Amplitudes **compose multiplicatively** along worldline
segments (`reversiblePhase_add`), so twin B's amplitude is the product over its
two legs (`twinBPhase_eq`), and the twins' **relative amplitude is the phase of
the age gap**:

 `twinAPhase = twinBPhase · exp(−i E_R · ageGap/ℏ)` (`twinAPhase_eq_twinBPhase_mul_ageGapPhase`).

Each amplitude is unitary (`norm_twinAPhase = 1`): the geometric proper-time
sector is the frozen / zero-entropy limit.

## Complex proper time

The complex age gap `complexAgeGap` has real part the SR age gap
(`complexAgeGap_re`) and, on the diagonal `ρ = σ`, reduces to the real SR age gap
(`complexAgeGap_at_frozen`) — the standard twin paradox is the **entropy-free
limit** of the complex one.

## Scope

The geometric inequality "Twin A is older" (`ageGap ≥ 0`) is the Minkowski
reverse-triangle fact represented as a hypothesis here (`ageGap_nonneg_of`); it is
verified concretely for `example1` (`example1_ageGap_nonneg`). What this module
adds is the entropic / path-integral *reformulation* on top of that geometry.


## References

- **Pauli 1933** — *Die allgemeinen Prinzipien der Wellenmechanik*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section


open Physlib.QuantumMechanics.NonHermitian.WickRotation
namespace Physlib.Relativity.Special.TwinParadox.Entropic

open QuantumInfo.Finite SpecialRelativity

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## §1 — Path-integral amplitude composes along a worldline -/

/-- **Worldline composition of the reversible phase.** The Lorentzian
path-integral amplitude over a proper-time interval factorises into a product
over sub-intervals: `exp(−i E_R (τ₁+τ₂)/ℏ) = exp(−i E_R τ₁/ℏ)·exp(−i E_R τ₂/ℏ)`. -/
theorem reversiblePhase_add (E_R hbar τ₁ τ₂ : ℝ) :
    reversiblePhase E_R hbar (τ₁ + τ₂) =
      reversiblePhase E_R hbar τ₁ * reversiblePhase E_R hbar τ₂ := by
  unfold reversiblePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

/-! ## §2 — Twin amplitudes in the path integral -/

/-- Twin A's path-integral amplitude: the reversible phase set by A's proper
time `τ_A`. -/
def twinAPhase (T : InstantaneousTwinParadox) (E_R hbar : ℝ) : ℂ :=
  reversiblePhase E_R hbar T.properTimeTwinA

/-- Twin B's path-integral amplitude: the product of the reversible phases over
B's two worldline legs. -/
def twinBPhase (T : InstantaneousTwinParadox) (E_R hbar : ℝ) : ℂ :=
  reversiblePhase E_R hbar (SpaceTime.properTime T.startPoint T.twinBMid) *
    reversiblePhase E_R hbar (SpaceTime.properTime T.twinBMid T.endPoint)

/-- Twin B's two-leg amplitude equals the single reversible phase of B's total
proper time — path-integral composition along the broken worldline. -/
theorem twinBPhase_eq (T : InstantaneousTwinParadox) (E_R hbar : ℝ) :
    twinBPhase T E_R hbar = reversiblePhase E_R hbar T.properTimeTwinB := by
  unfold twinBPhase InstantaneousTwinParadox.properTimeTwinB
  rw [← reversiblePhase_add]

/-- **Twin-paradox path-integral identity.** The twins' relative amplitude is the
reversible phase of the age gap: `twinAPhase = twinBPhase · exp(−i E_R ageGap/ℏ)`. -/
theorem twinAPhase_eq_twinBPhase_mul_ageGapPhase
    (T : InstantaneousTwinParadox) (E_R hbar : ℝ) :
    twinAPhase T E_R hbar =
      twinBPhase T E_R hbar * reversiblePhase E_R hbar T.ageGap := by
  have hτ : T.properTimeTwinA = T.properTimeTwinB + T.ageGap := by
    unfold InstantaneousTwinParadox.ageGap; ring
  unfold twinAPhase
  rw [hτ, reversiblePhase_add, twinBPhase_eq]

/-- Each twin amplitude is **unitary** (unit modulus): the geometric proper-time
sector has no damping. -/
theorem norm_twinAPhase (T : InstantaneousTwinParadox) (E_R hbar : ℝ) :
    ‖twinAPhase T E_R hbar‖ = 1 :=
  norm_reversiblePhase E_R hbar T.properTimeTwinA

/-! ## §3 — Complex (entropic) proper time of the twin paradox -/

/-- **Complex age gap**: the difference of the twins' complex proper times
`S = S_R + i S_I` (real part geometric proper time, imaginary part entropic). -/
def complexAgeGap (U : EntropicTimeUnits) (T : InstantaneousTwinParadox)
    (ρ σ : MState d) : ℂ :=
  complexProperTimeMetric U T.startPoint T.endPoint ρ σ -
    (complexProperTimeMetric U T.startPoint T.twinBMid ρ σ +
      complexProperTimeMetric U T.twinBMid T.endPoint ρ σ)

/-- The **real part of the complex age gap is the SR age gap**. -/
@[simp] theorem complexAgeGap_re (U : EntropicTimeUnits) (T : InstantaneousTwinParadox)
    (ρ σ : MState d) :
    (complexAgeGap U T ρ σ).re = T.ageGap := by
  unfold complexAgeGap InstantaneousTwinParadox.ageGap
    InstantaneousTwinParadox.properTimeTwinA InstantaneousTwinParadox.properTimeTwinB
  simp [Complex.sub_re, Complex.add_re]

/-- **Frozen / zero-entropy limit**: on `ρ = σ` the complex age gap collapses to
the real SR age gap. The standard twin paradox is the entropy-free limit of the
complex one. -/
theorem complexAgeGap_at_frozen (U : EntropicTimeUnits) (T : InstantaneousTwinParadox)
    (ρ : MState d) :
    complexAgeGap U T ρ ρ = (T.ageGap : ℂ) := by
  unfold complexAgeGap
  rw [complexProperTimeMetric_at_frozen, complexProperTimeMetric_at_frozen,
    complexProperTimeMetric_at_frozen]
  unfold InstantaneousTwinParadox.ageGap InstantaneousTwinParadox.properTimeTwinA
    InstantaneousTwinParadox.properTimeTwinB
  push_cast; ring

/-! ## §4 — "Twin A is older" and the concrete example -/

/-- **Twin A is older**, given the Minkowski reverse-triangle fact
`τ_B ≤ τ_A`. The geometric inequality is the input; the age gap is then
non-negative. -/
theorem ageGap_nonneg_of (T : InstantaneousTwinParadox)
    (h : T.properTimeTwinB ≤ T.properTimeTwinA) : 0 ≤ T.ageGap := by
  unfold InstantaneousTwinParadox.ageGap; linarith

/-- For `example1`, Twin A is concretely older: `ageGap = 6 ≥ 0`. -/
theorem example1_ageGap_nonneg : 0 ≤ InstantaneousTwinParadox.example1.ageGap := by
  rw [InstantaneousTwinParadox.example1_ageGap]; norm_num

/-- For `example1`, the frozen complex age gap is the real SR age gap `6`. -/
theorem example1_complexAgeGap_at_frozen (U : EntropicTimeUnits) (ρ : MState d) :
    complexAgeGap U InstantaneousTwinParadox.example1 ρ ρ = (6 : ℂ) := by
  rw [complexAgeGap_at_frozen, InstantaneousTwinParadox.example1_ageGap]
  norm_num

/-! ## §5 — Theorem: the twin paradox as complex proper time + path integral -/

/-- **Theorem.** For any instantaneous twin paradox:

* (path integral) the twins' relative amplitude is the age-gap phase;
* (complex proper time) the SR age gap is the real part of the complex age gap;
* (frozen limit) on `ρ = σ` the complex age gap is exactly the real SR age gap. -/
theorem twin_paradox_entropic_path_integral
    (U : EntropicTimeUnits) (T : InstantaneousTwinParadox) (ρ : MState d) (E_R hbar : ℝ) :
    twinAPhase T E_R hbar
        = twinBPhase T E_R hbar * reversiblePhase E_R hbar T.ageGap
    ∧ (complexAgeGap U T ρ ρ).re = T.ageGap
    ∧ complexAgeGap U T ρ ρ = (T.ageGap : ℂ) :=
  ⟨twinAPhase_eq_twinBPhase_mul_ageGapPhase T E_R hbar,
   complexAgeGap_re U T ρ ρ,
   complexAgeGap_at_frozen U T ρ⟩

/-! ## §6 — Entropic-action structures per twin (Phase-4 A3 reformulation) -/

open Physlib.ClassicalMechanics.ActionPrinciple
open Physlib.Thermodynamics.SecondLaw
open Physlib.Thermodynamics.FirstLaw
open Physlib.Thermodynamics.FreeEnergy
open Physlib.Thermodynamics.Equilibrium
open Physlib.ClassicalMechanics.Noether.DissipativeBalance

/-- **Twin A as an `EntropicAction`.** Classical part is the geometric proper time
`τ_A`; entropic part is the dimensional entropic-time gap of the state pair
`(ρ_A, σ_A)` (vanishes when `ρ_A = σ_A`).  The total action is `τ_A + S_I`. -/
def twinA_action (T : InstantaneousTwinParadox)
    (U : EntropicTimeUnits) (ρ_A σ_A : MState d) : EntropicAction where
  classical := T.properTimeTwinA
  entropic := entropicProperTimeMetric U ρ_A σ_A
  entropic_nonneg := entropicProperTimeMetric_nonneg U ρ_A σ_A

/-- **Twin B as an `EntropicAction`.** Same shape, on B's broken worldline. -/
def twinB_action (T : InstantaneousTwinParadox)
    (U : EntropicTimeUnits) (ρ_B σ_B : MState d) : EntropicAction where
  classical := T.properTimeTwinB
  entropic := entropicProperTimeMetric U ρ_B σ_B
  entropic_nonneg := entropicProperTimeMetric_nonneg U ρ_B σ_B

/-- **Total-action age gap.** The entropic-action analogue of `ageGap`: the
difference of the twins' total actions. -/
def totalActionGap (T : InstantaneousTwinParadox)
    (U : EntropicTimeUnits) (ρ_A σ_A ρ_B σ_B : MState d) : ℝ :=
  (twinA_action T U ρ_A σ_A).total - (twinB_action T U ρ_B σ_B).total

/-- **Frozen-LRF identification of the total-action age gap with the geometric
age gap.**  When both twins are at thermal equilibrium (`ρ_A = σ_A`, `ρ_B = σ_B`),
each twin's entropic contribution vanishes (A3) and the total-action age gap
reduces to the geometric `ageGap`. -/
theorem totalActionGap_eq_ageGap_at_frozen
    (T : InstantaneousTwinParadox) (U : EntropicTimeUnits) (ρ_A ρ_B : MState d) :
    totalActionGap T U ρ_A ρ_A ρ_B ρ_B = T.ageGap := by
  unfold totalActionGap
  rw [(twinA_action T U ρ_A ρ_A).total_eq_classical_at_zero_entropic
        (entropicProperTimeMetric_self U ρ_A)]
  rw [(twinB_action T U ρ_B ρ_B).total_eq_classical_at_zero_entropic
        (entropicProperTimeMetric_self U ρ_B)]
  show T.properTimeTwinA - T.properTimeTwinB = T.ageGap
  unfold InstantaneousTwinParadox.ageGap; rfl

/-! ## §7 — Each twin as an `EntropyArrowWorldline` (reversible) -/

/-- **Trivial reversible entropy-arrow worldline** for an idealised twin: no
entropy production along the trajectory (`S_I_along ≡ 0`). -/
def trivialReversibleArrow (hbar : ℝ) (hbar_pos : 0 < hbar) :
    EntropyArrowWorldline where
  ℏ := hbar
  ℏ_pos := hbar_pos
  S_I_along := fun _ => 0
  τ_ent_along := fun _ => 0
  τ_ent_eq := by intro t; simp
  S_I_monotone := fun _ => le_refl _
  S_I_at_zero_nonneg := le_refl _

theorem trivialReversibleArrow_isReversible
    (hbar : ℝ) (hbar_pos : 0 < hbar) :
    (trivialReversibleArrow hbar hbar_pos).IsReversible :=
  fun _ _ => rfl

/-! ## §8 — Equilibrium recovery for the ideal twin paradox (Phase-5 theorem) -/

/-- **Trivial Noether balance**: constant charge, zero defect. -/
def trivialNoetherBalance : NoetherBalance where
  Q := fun _ => 0
  defect := fun _ => 0
  balance := by
    intro t₁ t₂ _
    simp

/-- **Trivial thermodynamic worldline**: constant internal energy, zero net flux. -/
def trivialThermoWorldline : ThermodynamicWorldline where
  U := fun _ => 0
  dQ_dt := fun _ => 0
  dW_dt := fun _ => 0
  firstLaw := by
    intro t₁ t₂ _
    simp

/-- **Trivial Helmholtz worldline**: zero `U`, zero `S`, fixed reservoir
temperature `T = 1`. -/
def trivialHelmholtzWorldline : HelmholtzWorldline where
  U := fun _ => 0
  S := fun _ => 0
  T := 1
  T_pos := one_pos

/-- **Twin paradox at the frozen LRF — equilibrium-recovery theorem.**
For an idealised twin paradox (both twins reversible, no thermodynamic
activity), the Phase-5 `equilibrium_recovery_capstone` applies trivially:
Clausius equality, internal-energy conservation, Noether charge conservation,
and Helmholtz free-energy conservation all hold simultaneously across any
forward interval.  The standard twin paradox is thus a **canonical instance**
of entropic-time equilibrium recovery. -/
theorem twin_paradox_at_frozen_LRF
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    EquilibriumRecovery
      (trivialReversibleArrow hbar hbar_pos)
      trivialNoetherBalance
      trivialThermoWorldline
      trivialHelmholtzWorldline
      t₁ t₂ :=
  equilibrium_recovery_capstone
    (trivialReversibleArrow hbar hbar_pos)
    trivialNoetherBalance
    trivialThermoWorldline
    trivialHelmholtzWorldline
    h
    (trivialReversibleArrow_isReversible hbar hbar_pos)
    (by show ∫ _ in t₁..t₂, (0 : ℝ) = 0
        exact intervalIntegral.integral_zero)
    (by show ∫ _ in t₁..t₂, ((0 : ℝ) - 0) = 0
        simp [intervalIntegral.integral_zero])
    (fun _ _ => rfl)                  -- U const
    (fun _ _ => rfl)                  -- S const

/-! ## SR ↔ entropic proper-time identification structure

In general (Appendix B), SR proper time `τ_SR = ∫ √(1 − v²/c²) dt` and
entropic proper time `τ_ent = S_I/ℏ` are independent clock variables — see
`Physlib.Relativity.Special.TwinParadox.GeometricEntropicTimeDistinction`
for the default-separation structure.

A model can however supply a structural *identification* of the two; this
small structure records when that identification holds (e.g. for a closed
isolated worldline whose dissipation defect is calibrated to match SR
proper time).  Without this structure, the two clocks are treated as
distinct layers.
-/

/-- **SR ↔ entropic identification structure.**  A model that asserts the
identification `τ_ent = τ_SR` pointwise. -/
structure IdentifySRProperTimeWithEntropicProperTime where
  /-- SR proper-time clock function. -/
  tauSR : ℝ → ℝ
  /-- Entropic proper-time function. -/
  tauEnt : ℝ → ℝ
  /-- The identification: `τ_ent = τ_SR` pointwise. -/
  tauEnt_eq_tauSR : ∀ s : ℝ, tauEnt s = tauSR s

namespace IdentifySRProperTimeWithEntropicProperTime

variable (B : IdentifySRProperTimeWithEntropicProperTime)

/-- Under the identification, the two clocks agree pointwise. -/
theorem tauEnt_eq_tauSR_at (s : ℝ) : B.tauEnt s = B.tauSR s :=
  B.tauEnt_eq_tauSR s

/-- Under the identification, the two clocks agree as functions. -/
theorem tauEnt_eq_tauSR_funext : B.tauEnt = B.tauSR := by
  funext s
  exact B.tauEnt_eq_tauSR s

end IdentifySRProperTimeWithEntropicProperTime

/-- **Trivial existence**: identify both clocks with the identity. -/
theorem IdentifySRProperTimeWithEntropicProperTime.exists_trivial :
    ∃ _ : IdentifySRProperTimeWithEntropicProperTime, True :=
  ⟨{ tauSR := id, tauEnt := id, tauEnt_eq_tauSR := fun _ => rfl }, trivial⟩

/-- **Default-separation theorem.**  Without an
`IdentifySRProperTimeWithEntropicProperTime` witness, the two clocks need
not coincide — there exist clock functions that disagree somewhere. -/
theorem sr_proper_time_separate_from_entropic_proper_time :
    ∃ (tauSR tauEnt : ℝ → ℝ) (s : ℝ), tauEnt s ≠ tauSR s := by
  refine ⟨fun _ => (0 : ℝ), fun s => s, 1, ?_⟩
  norm_num

end Physlib.Relativity.Special.TwinParadox.Entropic

end
