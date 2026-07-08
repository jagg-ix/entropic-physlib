/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.MatterFourMomentum
public import Physlib.QuantumMechanics.Schrodinger.MadelungPolarDecomposition
public import Physlib.QuantumMechanics.NonHermitian.WickRotation

/-!
# The complex matter energy density `T⁰⁰ = ρ_R + i ρ_I` (roadmap target A2)

This is target **A2** of the complex-Einstein-field-equation roadmap: the complex matter energy
density, the time–time component of the stress-energy that will source the complex Einstein
equations. It uses the **Madelung representation of the damped (non-Hermitian) parametric
oscillator** already in physlib's `NonHermitian.WickRotation`.

## What is used (no duplicated infrastructure)

We reuse the two existing physlib pieces, each from its canonical home — we do **not** duplicate the
Madelung structure (and deliberately avoid `WickRotation`'s own duplicate `MadelungWaveFunction` /
`madelungDensity`, taking only its damped-oscillator `complexEnergy`):

* the **Madelung representation** `ψ = R·exp(iS/ℏ)` with the Born density `ρ = R²`
  (`Schrodinger.MadelungPolarDecomposition`: `madelungDensity`, `madelungDensity_nonneg`) — the
  canonical Madelung infrastructure, the spatial weight of the energy density;
* the **damped oscillator** complex energy of the `H_C = H_R − iH_I` eigenstate, `E_C = E_R − iE_I`
  (`NonHermitian.WickRotation.complexEnergy`), `E_I` the damping; the evolution factors as a unitary
  phase times the entropic damping `e^{−E_I t/ℏ}`.

The complex matter energy density is the damped complex energy encoded in the Madelung density:

  `T⁰⁰ = E_C · ρ = (E_R − iE_I)·R² = E_R R² − i (E_I R²)`   (`complexMatterEnergyDensity`).

Its **real part** `ρ_R = E_R·ρ` is the ordinary energy density (with `E_R = m_R c²` from the complex
mass, `realEnergyDensity_from_complexMass`), and its **imaginary part** `−E_I·ρ` is the entropic /
dissipative energy density (`E_I = m_I c²`, the damping). The entropic magnitude is
**positive-semidefinite** `E_I·ρ ≥ 0` (`entropicEnergyDensity_nonneg`), matching the PSD condition on
the imaginary stress-energy (`reference tree ComplexStressEnergyBridge.imagPart`), and vanishes at the
reversible point `E_I = 0` (`complexMatterEnergyDensity_reversible`).

(The Madelung guidance velocity `v = ∇S/m` is the Schrödinger–Burgers velocity field; the exact
Madelung↔hydrodynamic/Navier–Stokes (vector Burgers) identification lives in `reference tree`'s
`BohmianQMBridge`, not as a standalone Lean Schrödinger–Burgers file. A separate Madelung polar
decomposition also lives in `Schrodinger.MadelungPolarDecomposition`.)

## Main results

* `complexMatterEnergyDensity`, `_re`, `_im` — `T⁰⁰ = E_C·ρ`, real and imaginary parts.
* `realEnergyDensity`, `entropicEnergyDensity`, `entropicEnergyDensity_nonneg` — `ρ_R`, `ρ_I ≥ 0`.
* `realEnergyDensity_from_complexMass` — `ρ_R` with `E_R = m_R c²` (the complex-mass rest energy).
* `entropicEnergyDensity_from_imaginaryMass` — `ρ_I` sourced by the imaginary mass `m_I`.
* `complexMatterEnergyDensity_reversible` — `E_I = 0 ⟹ T⁰⁰` real.
* `complexMatterEnergyDensity_source` — the bundled `T⁰⁰ = ρ_R + iρ_I` source data.

## References

* E. Madelung, *Z. Phys.* **40** (1927) 322 (polar form). K. Nagao, H. B. Nielsen (complex `H_C`).
* This development: `NonHermitian.WickRotation`, `ComplexEinstein.ComplexMassEinsteinEquations`,
  `GravitationalFieldEquations.MatterFourMomentum`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

-- Canonical Madelung infrastructure (`MadelungWaveFunction`, `madelungDensity`,
-- `madelungDensity_nonneg`); selectively take only the damped-oscillator `complexEnergy` from
-- `WickRotation` so we do **not** depend on its duplicate Madelung structure.
open Physlib.QuantumMechanics.Schrodinger
open Physlib.QuantumMechanics.NonHermitian.WickRotation (complexEnergy complexEnergy_at_E_I_zero)
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMatterEnergyDensity

/-! ## §A — the complex energy of the damped oscillator, in coordinates -/

/-- **Real part of the complex energy** `Re(E_R − iE_I) = E_R`. -/
theorem complexEnergy_re (E_R E_I : ℝ) : (complexEnergy E_R E_I).re = E_R := by
  unfold complexEnergy; simp

/-- **Imaginary part of the complex energy** `Im(E_R − iE_I) = −E_I` (the damping). -/
theorem complexEnergy_im (E_R E_I : ℝ) : (complexEnergy E_R E_I).im = -E_I := by
  unfold complexEnergy; simp

/-! ## §B — the complex matter energy density `T⁰⁰ = E_C · ρ` -/

/-- **The complex matter energy density** `T⁰⁰ = E_C · ρ`, the damped complex energy
`E_C = E_R − iE_I` encoded in the Madelung density `ρ = R²`. -/
def complexMatterEnergyDensity (ψ : MadelungWaveFunction) (E_R E_I : ℝ) : ℂ :=
  complexEnergy E_R E_I * (madelungDensity ψ : ℂ)

/-- **The real energy density** `ρ_R = E_R · ρ` (`Re T⁰⁰`). -/
theorem complexMatterEnergyDensity_re (ψ : MadelungWaveFunction) (E_R E_I : ℝ) :
    (complexMatterEnergyDensity ψ E_R E_I).re = E_R * madelungDensity ψ := by
  unfold complexMatterEnergyDensity
  rw [Complex.mul_re, complexEnergy_re, complexEnergy_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The imaginary (entropic) energy density** `Im T⁰⁰ = −E_I · ρ` (the dissipative `H_I` sector). -/
theorem complexMatterEnergyDensity_im (ψ : MadelungWaveFunction) (E_R E_I : ℝ) :
    (complexMatterEnergyDensity ψ E_R E_I).im = -E_I * madelungDensity ψ := by
  unfold complexMatterEnergyDensity
  rw [Complex.mul_im, complexEnergy_re, complexEnergy_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## §C — `ρ_R`, `ρ_I`, the entropic positivity, and the complex-mass source -/

/-- **The real energy density** `ρ_R = E_R · ρ` (`T_R`). -/
def realEnergyDensity (ψ : MadelungWaveFunction) (E_R : ℝ) : ℝ := E_R * madelungDensity ψ

/-- **The entropic energy density** `ρ_I = E_I · ρ` (`T_I`, the imaginary sector magnitude). -/
def entropicEnergyDensity (ψ : MadelungWaveFunction) (E_I : ℝ) : ℝ := E_I * madelungDensity ψ

/-- **The entropic energy density is positive-semidefinite** `ρ_I ≥ 0` (for `E_I ≥ 0`): the Madelung
density `ρ = R² ≥ 0` weighting a non-negative damping. Matches the PSD imaginary stress-energy. -/
theorem entropicEnergyDensity_nonneg (ψ : MadelungWaveFunction) (E_I : ℝ) (hE : 0 ≤ E_I) :
    0 ≤ entropicEnergyDensity ψ E_I :=
  mul_nonneg hE (madelungDensity_nonneg ψ)

/-- **The real energy density from the complex mass** `ρ_R = m_R c² · ρ`: the real part of the
complex-mass Einstein energy (`ComplexEinstein.ComplexMassEinsteinEquations.complexEinsteinEnergy`) weights the
Madelung density. -/
theorem realEnergyDensity_from_complexMass (ψ : MadelungWaveFunction) (m_R m_I c : ℝ) :
    realEnergyDensity ψ (complexEinsteinEnergy m_R m_I c).re = m_R * c ^ 2 * madelungDensity ψ := by
  unfold realEnergyDensity
  rw [complexEinsteinEnergy_re]

/-- **The entropic energy density is sourced by the imaginary mass** `m_I` (`E_I = m_I c²`), and is
PSD for `m_I ≥ 0`: the imaginary mass of the complex-mass Einstein energy feeds the entropic
stress. -/
theorem entropicEnergyDensity_from_imaginaryMass (ψ : MadelungWaveFunction) (m_I c : ℝ)
    (hm : 0 ≤ m_I) :
    0 ≤ entropicEnergyDensity ψ (m_I * c ^ 2) :=
  entropicEnergyDensity_nonneg ψ (m_I * c ^ 2) (mul_nonneg hm (sq_nonneg c))

/-- **The reversible limit is a real energy density** `E_I = 0 ⟹ T⁰⁰ = ρ_R` (no entropic part). -/
theorem complexMatterEnergyDensity_reversible (ψ : MadelungWaveFunction) (E_R : ℝ) :
    complexMatterEnergyDensity ψ E_R 0 = (realEnergyDensity ψ E_R : ℂ) := by
  unfold complexMatterEnergyDensity realEnergyDensity
  rw [complexEnergy_at_E_I_zero, ← Complex.ofReal_mul]

/-! ## §D — the bundled source data -/

/-- **The complex matter energy density as the complex-Einstein source** `T⁰⁰ = ρ_R + iρ_I`. For
`E_I ≥ 0`:

* the **real part** is `ρ_R = E_R·ρ` (ordinary energy density, `E_R = m_R c²`);
* the **imaginary part** is `−E_I·ρ` (entropic / dissipative, `E_I = m_I c²`, the damping);
* the entropic magnitude `E_I·ρ` is **positive-semidefinite**;
* at the reversible point `E_I = 0` the density is purely real.

This is the matter side of the complex Einstein equations (Phase A complete), built from the
Madelung density of the damped oscillator and its complex energy. -/
theorem complexMatterEnergyDensity_source (ψ : MadelungWaveFunction) (E_R E_I : ℝ) (hE : 0 ≤ E_I) :
    (complexMatterEnergyDensity ψ E_R E_I).re = E_R * madelungDensity ψ
      ∧ (complexMatterEnergyDensity ψ E_R E_I).im = -E_I * madelungDensity ψ
      ∧ 0 ≤ E_I * madelungDensity ψ
      ∧ complexMatterEnergyDensity ψ E_R 0 = (realEnergyDensity ψ E_R : ℂ) :=
  ⟨complexMatterEnergyDensity_re ψ E_R E_I, complexMatterEnergyDensity_im ψ E_R E_I,
   entropicEnergyDensity_nonneg ψ E_I hE, complexMatterEnergyDensity_reversible ψ E_R⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMatterEnergyDensity

end

end
