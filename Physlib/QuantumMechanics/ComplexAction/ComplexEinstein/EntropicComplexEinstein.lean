/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
public import Physlib.QuantumMechanics.Clock.EntropicAgreement
meta import Zil

/-!
# The complex-action/entropic-time entropic damping is sourced by the imaginary Einstein energy

Links the complex-action/entropic-time damping/entropic-time machinery (`PathIntegral.ComplexActionDampingCoercivity`) to the **complex Einstein
equation** (`ComplexEinstein.ComplexMassEinsteinEquations`): the entropic (imaginary) action `S_I` that damps the
path-integral weight is *exactly* the **imaginary Einstein energy** `Im E = m_I c²` accumulated over proper
time — the same `m_R + i·m_I` complex structure underlying both the complex-action/entropic-time complex action `S = S_R + i·S_I`
and the complex Einstein mass.

With `S_I = (Im E)·σ = m_I c²·σ` (`entropicActionEinstein`):

* the **entropic proper time** is `τ_ent = S_I/ℏ = m_I c² σ / ℏ` (`entropicProperTime_einstein`) — the complex-action/entropic-time
  entropic clock *is* the imaginary Einstein energy times proper time;
* the **path-integral damping** is `‖w‖ = exp(−m_I c² σ/ℏ)` (`einstein_entropic_damping`), driven by the
  imaginary mass `m_I`;
* the **reversible limit** `m_I = 0` gives `S_I = 0`, `‖w‖ = 1` (unitary) and `τ_ent = 0`
  (`reversible_einstein_unitary`) — the real standard Einstein equation (`m_I = 0` ⟹ `Im E = 0`), the
  oscillatory-only, dissipation-free case.

So reversible ⟺ real (standard) Einstein ⟺ unitary complex-action/entropic-time weight, and the entropic/dissipative sector is the
imaginary mass `m_I` driving both the GW entropic radiation and the path-integral damping — one `S_R + i·S_I`
decomposition across the gravity, complex-Einstein and complex-action/entropic-time layers.

* **§A — the entropic action from the imaginary Einstein energy** (`entropicActionEinstein`,
  `entropicActionEinstein_eq`, `entropicProperTime_einstein`).
* **§B — the entropic damping** (`einstein_entropic_damping`, `reversible_einstein_unitary`).
* **§C — the unification** (`entropic_complex_einstein_unification`).

## References

* Repo carriers: `PathIntegral.ComplexActionDampingCoercivity` (`entropicProperTime`, the damping bound),
  `ComplexEinstein.ComplexMassEinsteinEquations` (`complexEinsteinEnergy`, `Im E = m_I c²`),
  `Physlib.QFT.Wick.Consistency` (`complexActionWeight`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein

open Physlib.QFT.Wick.Consistency
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.Clock.Phase
open Physlib.QuantumMechanics.Clock.EntropicAgreement
open Physlib.Thermodynamics.SecondLaw


/-- **The entropic action from the imaginary Einstein energy** `S_I = (Im E)·σ = m_I c²·σ` — the imaginary
(entropic) part of the complex Einstein energy accumulated over proper time `σ`. -/
noncomputable def entropicActionEinstein (m_R m_I c σ : ℝ) : ℝ :=
  (complexEinsteinEnergy m_R m_I c).im * σ

/-- **`S_I = m_I c²·σ`** — the entropic action in terms of the imaginary mass (`complexEinsteinEnergy_im`). -/
lemma entropicActionEinstein_eq (m_R m_I c σ : ℝ) :
    entropicActionEinstein m_R m_I c σ = m_I * c ^ 2 * σ := by
  rw [entropicActionEinstein, complexEinsteinEnergy_im]

/-- **[The entropic clock is the imaginary Einstein energy] `τ_ent = m_I c² σ / ℏ`** — the complex-action/entropic-time entropic
proper time of the imaginary-Einstein-sourced action is the imaginary mass energy times proper time over `ℏ`. -/
lemma entropicProperTime_einstein (m_R m_I c σ hbar : ℝ) :
    entropicProperTime (entropicActionEinstein m_R m_I c σ) hbar = m_I * c ^ 2 * σ / hbar := by
  rw [entropicProperTime, entropicActionEinstein_eq]


/-- **[Entropic damping from the imaginary mass] `‖w‖ = exp(−m_I c² σ/ℏ)`** — the path-integral weight is
damped by the imaginary Einstein energy; a non-zero `m_I` (entropic/dissipative sector) suppresses the
amplitude. -/
lemma einstein_entropic_damping (S_R m_R m_I c σ hbar : ℝ) :
    ‖complexActionWeight S_R (entropicActionEinstein m_R m_I c σ) hbar‖
      = Real.exp (-(m_I * c ^ 2 * σ / hbar)) := by
  rw [norm_complexActionWeight, entropicActionEinstein_eq]

/-- **[Reversible ⟺ real Einstein ⟺ unitary] `m_I = 0 ⟹ ‖w‖ = 1`.** With no imaginary mass (the real standard
Einstein equation, `Im E = 0`) the entropic action vanishes and the complex-action/entropic-time weight is unitary — the
oscillatory-only, dissipation-free case. -/
lemma reversible_einstein_unitary (S_R m_R c σ hbar : ℝ) :
    ‖complexActionWeight S_R (entropicActionEinstein m_R 0 c σ) hbar‖ = 1 := by
  rw [entropicActionEinstein_eq, norm_complexActionWeight]; simp


/-- **[complex-action/entropic-time ↔ complex Einstein, unified] one `S_R + i·S_I` decomposition.** The complex-action/entropic-time entropic proper time
is the imaginary Einstein energy `m_I c² σ/ℏ`; the path-integral damping `‖w‖ = exp(−m_I c² σ/ℏ)` is driven by
the imaginary mass; and the reversible limit `m_I = 0` (the real standard Einstein equation) is the unitary
`‖w‖ = 1` case. The entropic/dissipative sector — the imaginary mass `m_I`, the GW entropic radiation, the
path-integral damping — is one and the same across the gravity, complex-Einstein and complex-action/entropic-time layers. -/
lemma entropic_complex_einstein_unification (S_R m_R m_I c σ hbar : ℝ) :
    entropicProperTime (entropicActionEinstein m_R m_I c σ) hbar = m_I * c ^ 2 * σ / hbar
      ∧ ‖complexActionWeight S_R (entropicActionEinstein m_R m_I c σ) hbar‖
          = Real.exp (-(m_I * c ^ 2 * σ / hbar))
      ∧ ‖complexActionWeight S_R (entropicActionEinstein m_R 0 c σ) hbar‖ = 1 :=
  ⟨entropicProperTime_einstein m_R m_I c σ hbar,
    einstein_entropic_damping S_R m_R m_I c σ hbar,
    reversible_einstein_unitary S_R m_R c σ hbar⟩

/-! ## D. Concrete physical-time identification

The preceding action is linear in the physical proper-time parameter `σ`.
Its positive imaginary energy therefore supplies a physical phase clock with
frequency `ω_I = m_I c² / ℏ`.  Unlike an agreement record, the constructions
below contain no field asserting the final time equality.
-/

/-- The physical phase clock carried by a strictly positive imaginary Einstein
energy. -/
noncomputable def imaginaryEinsteinPhaseClock
    (m_I c hbar : ℝ) (hE : 0 < m_I * c ^ 2) (hhbar : 0 < hbar) : PhaseClock where
  omega0 := m_I * c ^ 2 / hbar
  omega0_pos := div_pos hE hhbar

/-- The entropy-arrow worldline generated by the imaginary Einstein action.
Its dimensionless entropic phase is derived as `S_I / ℏ`; it is not declared
equal to physical time. -/
noncomputable def imaginaryEinsteinEntropyWorldline
    (m_R m_I c hbar : ℝ) (hE : 0 < m_I * c ^ 2) (hhbar : 0 < hbar) :
    EntropyArrowWorldline where
  ℏ := hbar
  ℏ_pos := hhbar
  S_I_along := entropicActionEinstein m_R m_I c
  τ_ent_along := fun σ =>
    entropicProperTime (entropicActionEinstein m_R m_I c σ) hbar
  τ_ent_eq := fun _ => rfl
  S_I_monotone := by
    intro σ₁ σ₂ hσ
    rw [entropicActionEinstein_eq, entropicActionEinstein_eq]
    exact mul_le_mul_of_nonneg_left hσ hE.le
  S_I_at_zero_nonneg := by
    rw [entropicActionEinstein_eq]
    simp

/-- The existing complex-Einstein imaginary action automatically satisfies the
operational clock calibration: `ΔS_I = ℏ ω_I Δσ`. -/
@[zil_level physical_theorem]
theorem imaginaryEinstein_entropicPhysicalClockCalibration
    (m_R m_I c hbar : ℝ) (hE : 0 < m_I * c ^ 2) (hhbar : 0 < hbar) :
    EntropicPhysicalClockCalibration
      (imaginaryEinsteinPhaseClock m_I c hbar hE hhbar)
      (imaginaryEinsteinEntropyWorldline m_R m_I c hbar hE hhbar)
      id := by
  constructor
  intro σ₁ σ₂
  simp only [imaginaryEinsteinEntropyWorldline, imaginaryEinsteinPhaseClock,
    id_eq, entropicActionEinstein_eq]
  field_simp [hhbar.ne']

/-- **Concrete demonstrated identification of entropic time with physical
proper time in the dissipative complex-Einstein sector.**

For positive imaginary Einstein energy, the entropic clock generated by
`S_I(σ) = m_I c² σ`, read at its derived frequency
`ω_I = m_I c²/ℏ`, returns exactly `σ₂ - σ₁`.

No premise states the desired equality.  The proof composes the existing
complex-Einstein action theorem with the operational entropic/phase-clock
identification.  The strict positivity is essential: at `m_I = 0` the
entropic clock freezes and cannot serve as a positive-frequency physical
clock, even though ordinary geometric time still exists. -/
@[zil_level physical_theorem]
theorem imaginaryEinstein_entropicTime_eq_physicalProperTime
    (m_R m_I c hbar : ℝ) (hE : 0 < m_I * c ^ 2) (hhbar : 0 < hbar)
    (σ₁ σ₂ : ℝ) :
    entropicPhysicalTimeAdvance
      (imaginaryEinsteinPhaseClock m_I c hbar hE hhbar)
      (imaginaryEinsteinEntropyWorldline m_R m_I c hbar hE hhbar)
      σ₁ σ₂ = σ₂ - σ₁ :=
  entropicPhysicalTimeAdvance_eq_physicalTime
    (imaginaryEinsteinPhaseClock m_I c hbar hE hhbar)
    (imaginaryEinsteinEntropyWorldline m_R m_I c hbar hE hhbar)
    id
    (imaginaryEinstein_entropicPhysicalClockCalibration m_R m_I c hbar hE hhbar)
    σ₁ σ₂

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.entropicProperTime_einstein where
  formalizes @ "claim:the-entropic-proper-time-tau-ent-equals-s-i-over-hbar-equals-the-imaginary-einstein-energy-m-I-c-squared-times-proper-time-over-hbar",
  supported_by @ "object:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexEinsteinEnergy"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.einstein_entropic_damping where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.entropicActionEinstein_eq",
  supported_by @ "lean:Physlib.QFT.Wick.Consistency.norm_complexActionWeight",
  formalizes @ "claim:the-path-integral-weight-is-damped-by-the-imaginary-einstein-energy-with-norm-equal-to-exp-minus-m-I-c-squared-sigma-over-hbar"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.reversible_einstein_unitary where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.entropicActionEinstein_eq",
  supported_by @ "lean:Physlib.QFT.Wick.Consistency.norm_complexActionWeight",
  formalizes @ "claim:the-reversible-limit-m-I-equals-zero-the-real-standard-einstein-equation-gives-a-unitary-path-integral-weight-of-norm-one"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.entropic_complex_einstein_unification where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.einstein_entropic_damping",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.entropicProperTime_einstein",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.reversible_einstein_unitary",
  formalizes @ "claim:the-complex-action-entropic-sector-and-the-complex-einstein-imaginary-mass-are-one-m-R-plus-i-m-I-decomposition-the-entropic-clock-is-the-imaginary-einstein-energy-the-damping-is-exp-minus-im-e-sigma-over-hbar-and-the-reversible-limit-is-unitary",
  requires @ "claim:the-entropic-proper-time-tau-ent-equals-s-i-over-hbar-equals-the-imaginary-einstein-energy-m-I-c-squared-times-proper-time-over-hbar"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.imaginaryEinstein_entropicPhysicalClockCalibration where
  formalizes @ "claim:the-existing-complex-einstein-imaginary-action-s-i-equals-m-i-c-squared-sigma-satisfies-delta-s-i-equals-hbar-omega-i-delta-sigma-at-the-derived-frequency-omega-i-equals-m-i-c-squared-over-hbar",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.entropicActionEinstein_eq",
  caveat @ "claim:this-is-the-dissipative-imaginary-energy-clock-calibration-not-a-derivation-of-imaginary-mass-from-standard-real-einstein-gravity"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.imaginaryEinstein_entropicTime_eq_physicalProperTime where
  formalizes @ "claim:in-the-positive-imaginary-energy-complex-einstein-sector-the-entropic-clock-generated-by-s-i-of-sigma-and-read-at-omega-i-returns-exactly-the-physical-proper-time-advance-sigma-two-minus-sigma-one",
  epistemic_status @ "ansatz-loaded",
  requires @ "claim:the-existing-complex-einstein-imaginary-action-s-i-equals-m-i-c-squared-sigma-satisfies-delta-s-i-equals-hbar-omega-i-delta-sigma-at-the-derived-frequency-omega-i-equals-m-i-c-squared-over-hbar",
  supported_by @ "lean:Physlib.QuantumMechanics.Clock.EntropicAgreement.entropicPhysicalTimeAdvance_eq_physicalTime",
  caveat @ "claim:exact-operational-identification-inside-the-complex-einstein-imaginary-energy-model;when-m-i-equals-zero-the-entropic-clock-is-frozen-and-does-not-replace-ordinary-geometric-time"

zil_file_contract physlib.entropicComplexEinstein where
  promises "Links complex-action entropic damping to the complex Einstein equation and constructs the corresponding operational clock. The imaginary action is S_I(sigma)=m_I c² sigma, the damping is exp(-m_I c² sigma/hbar), and the reversible m_I=0 limit is unitary. In the strictly positive imaginary-energy sector, the derived frequency omega_I=m_I c²/hbar and the constructed entropy worldline satisfy delta S_I=hbar omega_I delta sigma, so the independently defined phase-clock inverse proves that the entropic clock reads exactly the physical proper-time advance. The zero-imaginary-energy sector remains a frozen entropic clock and is not claimed to replace ordinary geometric time."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.entropicActionEinstein",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexEinsteinEnergy",
    "lean:Physlib.QuantumMechanics.Clock.EntropicAgreement.entropicPhysicalTimeAdvance_eq_physicalTime"]
  forbids_substitutes ["the path-integral construction of the complex-action weight and the entropic-proper-time clock, which are the cited complex-action-programme inputs",
    "any dynamical field equation, only the identification of the entropic damping with the imaginary Einstein energy is carried",
    "claiming the positive-frequency entropic clock exists in the reversible m_I equals zero sector",
    "promoting the model-specific positive-imaginary-energy identification into a universal claim that entropy alone defines physical time"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.entropicProperTime_einstein,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.einstein_entropic_damping,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.reversible_einstein_unitary,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.entropic_complex_einstein_unification,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.imaginaryEinstein_entropicPhysicalClockCalibration,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein.imaginaryEinstein_entropicTime_eq_physicalProperTime]

/- ZIL-END -/
