/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwGeneralisedPotential
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator
public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhComplexEinsteinFermion
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The 4D fermion's magnetic field and inverse-square law from the complex EFE

Five aspects tying together the electron arc — inverse-square (electric), magnetic (Aharonov–Bohm),
double-slit decoherence, Many-Interacting-Worlds, and the complex Einstein field equation — by *reusing* the
repo's canonical pieces (no re-derivation).

* **§1 — the inverse-square law links to MIW.**  The derived Newton/Coulomb field `newtonAcceleration = GM/r²`
  (`ComptonClock.EntropicNewtonConstantConvergence`) is degree-`−2` homogeneous, exactly matching the MIW
  interworld potential term `genInterworldTerm` (`SciamaAdSCPTMiwGeneralisedPotential`,
  `genInterworldTerm_inverse_square`): the fermion's inverse-square self-field and its many-interacting-worlds
  coupling are the same `λ⁻²` object (`newton_inverse_square_matches_miw`).

* **§2 — the magnetic Aharonov–Bohm phase drives the interference.**  A magnetic flux `Φ` rotates the Sorkin
  decoherence-functional off-diagonal by `e^{iΦ}` (`ab_phase_re`), so the double-slit fringe is
  `abFringe = 2v·Re(e^{iΦ}D) = 2vD₀cos Φ` (`abFringe_real`) — the flux **shifts** it.

* **§3 — transport decoherence damps that magnetic fringe.**  Gold's fast decoherence (smallest visibility
  `v = exp(−Γt)`, `SciamaAdSCPTTransportDecoherenceInterference`) damps the Aharonov–Bohm fringe most
  (`abFringe_gold_most_damped`): the magnetic flux and the `s–d`-scattering decoherence act on the one complex
  interference term.

* **§4 — the complex EFE sourced by the complex-mass Dirac fermion.**  Reusing
  `SciamaUnruhComplexEinsteinFermion.complexEinstein_from_dirac_fermion`: the fermion sources the complex EFE
  `𝒢 = κ(T + iS)` (`fermion_sources_complex_efe`) with the matter/real sector from the real mass and the
  entropic/imaginary sector from the imaginary mass — and the entropic (magnetic/decoherence) sector **vanishes
  for a real-mass fermion** (`fermion_real_mass_no_entropic`): dissipation needs the imaginary mass.

* **§5 — electric and magnetic in one complex invariant.**  The fermion's complex EM field
  (Riemann–Silberstein `EMFieldSuperoperator.sachsRiemannSilbersteinField = H − iE`) has squared components
  `Re(F²) = H² − E²` (the Lorentz scalar) and `Im(F²) = −2HE` (the `E·B` pseudoscalar)
  (`sachsField_sq_re`/`sachsField_sq_im`): the inverse-square electric field (`E`, §1/MIW) and the
  Aharonov–Bohm magnetic field (`H`, §2/§3/decoherence) are the two faces of one complex object — the
  electrogravitic reading of the complex EFE of §4.

Honest scope: exact identities (`λ⁻²` homogeneity, Aharonov–Bohm phase rotation, the squared-field invariants)
and reuse of the proven `newtonAcceleration`, `genInterworldTerm_inverse_square`, `interferenceVisibility`,
`sachsRiemannSilbersteinField`, and `complexEinstein_from_dirac_fermion`.  The `.re`/`.im` = electric/magnetic
and matter/entropic identifications are the electrogravitic reading of that complex EFE.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTFermionMagneticInverseSquareComplexEFE

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTMiwGeneralisedPotential
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTTransportDecoherenceInterference
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTRelativisticFermiConductivity
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicNewtonConstantConvergence
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMFieldSuperoperator
open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaUnruhComplexEinsteinFermion
open Physlib.QuantumMechanics.ComplexAction.Dirac.KleinGordonDiracFactorization
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations

/-! ## §1. The inverse-square law is the MIW interworld scaling -/

/-- **[The inverse-square field and the MIW interworld term share the `λ⁻²` scaling].**  The derived Newton /
Coulomb inverse-square field `GM/r²` and the Many-Interacting-Worlds interworld potential term both scale as
`λ⁻²` under `x → λx` — the fermion's inverse-square self-field and its many-worlds coupling are the same
degree-`−2` object. -/
theorem newton_inverse_square_matches_miw {lam : ℝ} (hlam : lam ≠ 0) {r den : ℝ} (hr : r ≠ 0) (hden : den ≠ 0)
    (G M num : ℝ) :
    newtonAcceleration G M (lam * r) = (1 / lam ^ 2) * newtonAcceleration G M r
      ∧ genInterworldTerm (lam * num) (lam * den) = (1 / lam ^ 2) * genInterworldTerm num den := by
  refine ⟨?_, genInterworldTerm_inverse_square hlam hden num⟩
  unfold newtonAcceleration
  field_simp

/-! ## §2. The magnetic Aharonov–Bohm phase drives the double-slit interference -/

/-- **[The Aharonov–Bohm phase rotates the off-diagonal] `Re(e^{iΦ}D) = cos Φ·Re D − sin Φ·Im D`.** -/
theorem ab_phase_re (Φ : ℝ) (D : ℂ) :
    (Complex.exp (Complex.I * (Φ : ℂ)) * D).re = Real.cos Φ * D.re - Real.sin Φ * D.im := by
  rw [show Complex.I * (Φ : ℂ) = (Φ : ℂ) * Complex.I by ring, Complex.exp_mul_I, Complex.mul_re]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add]

/-- The magnetic-flux-shifted, visibility-damped double-slit fringe `v · 2 Re(e^{iΦ}D)` (`v = exp(−Γt)`,
`Φ` the Aharonov–Bohm flux). -/
def abFringe (v Φ : ℝ) (D : ℂ) : ℝ := v * (2 * (Complex.exp (Complex.I * (Φ : ℂ)) * D).re)

/-- **[Magnetic flux shifts, visibility scales] `abFringe v Φ D₀ = 2vD₀ cos Φ`** for a real off-diagonal. -/
theorem abFringe_real (v Φ D0 : ℝ) : abFringe v Φ (D0 : ℂ) = 2 * v * D0 * Real.cos Φ := by
  unfold abFringe
  rw [ab_phase_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-! ## §3. Transport decoherence damps the magnetic fringe -/

/-- **[Gold damps the Aharonov–Bohm fringe most]** — for a constructive fringe (`D₀ > 0`, `cos Φ > 0`), gold's
smallest visibility (`interferenceVisibility_gold_least`) gives the smallest magnetic double-slit fringe: the
magnetic flux and the `s–d`-scattering decoherence act on one complex interference term. -/
theorem abFringe_gold_most_damped {prefactor t : ℝ} (hp : 0 < prefactor) (ht : 0 < t)
    {Φ D0 : ℝ} (hD : 0 < D0) (hcos : 0 < Real.cos Φ) :
    abFringe (interferenceVisibility prefactor t .gold) Φ (D0 : ℂ)
      < abFringe (interferenceVisibility prefactor t .silver) Φ (D0 : ℂ) := by
  rw [abFringe_real, abFringe_real]
  have hv := interferenceVisibility_gold_least hp ht
  have hvgs : interferenceVisibility prefactor t .gold < interferenceVisibility prefactor t .silver :=
    lt_trans hv.1 hv.2
  nlinarith [mul_pos (mul_pos (sub_pos.mpr hvgs) hD) hcos]

/-! ## §4. The complex EFE sourced by the complex-mass Dirac fermion -/

/-- **[The complex-mass Dirac fermion sources the complex EFE]** `𝒢 = κ(T + iS)` — real (matter) sector from the
real mass `Δ_R`, imaginary (entropic) sector from the imaginary mass `Δ_I` (reusing
`complexEinstein_from_dirac_fermion`). -/
theorem fermion_sources_complex_efe (Δ_R Δ_I vp κ : ℝ) :
    complexEinsteinFieldEquation (κ • diracHamiltonian Δ_R vp) (κ • diracHamiltonian Δ_I 0)
      (diracHamiltonian Δ_R vp) (diracHamiltonian Δ_I 0) κ :=
  complexEinstein_from_dirac_fermion Δ_R Δ_I vp κ (κ • diracHamiltonian Δ_R vp)
    (κ • diracHamiltonian Δ_I 0) rfl rfl

/-- The imaginary-mass Dirac Hamiltonian at zero imaginary mass is the zero matrix. -/
theorem diracHamiltonian_zero : diracHamiltonian 0 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diracHamiltonian]

/-- **[A real-mass fermion has no entropic sector]** — with `Δ_I = 0` the entropic (magnetic / decoherence)
curvature and stress both vanish, `𝒢 = κT` with no imaginary part: dissipation requires the imaginary mass. -/
theorem fermion_real_mass_no_entropic (Δ_R vp κ : ℝ) :
    complexEinsteinFieldEquation (κ • diracHamiltonian Δ_R vp) 0 (diracHamiltonian Δ_R vp) 0 κ := by
  have h := fermion_sources_complex_efe Δ_R 0 vp κ
  rw [diracHamiltonian_zero, smul_zero] at h
  exact h

/-! ## §5. Electric and magnetic in one complex invariant -/

/-- **[The complex EM field's scalar invariant] `Re(F²) = H² − E²`** — the Lorentz scalar `B² − E²`, from the
fermion's Riemann–Silberstein field `F = H − iE` (`sachsRiemannSilbersteinField`). -/
theorem sachsField_sq_re (E H : Fin 3 → ℝ) (k : Fin 3) :
    ((sachsRiemannSilbersteinField E H k) ^ 2).re = H k ^ 2 - E k ^ 2 := by
  rw [pow_two, Complex.mul_re, sachsRiemannSilbersteinField_re, sachsRiemannSilbersteinField_im]; ring

/-- **[The complex EM field's pseudoscalar invariant] `Im(F²) = −2HE`** — the parity-odd `E·B` invariant: the
inverse-square electric field `E` (§1/MIW) and the Aharonov–Bohm magnetic field `H` (§2/§3/decoherence) combine
in the one complex invariant of the fermion's field. -/
theorem sachsField_sq_im (E H : Fin 3 → ℝ) (k : Fin 3) :
    ((sachsRiemannSilbersteinField E H k) ^ 2).im = -2 * H k * E k := by
  rw [pow_two, Complex.mul_im, sachsRiemannSilbersteinField_re, sachsRiemannSilbersteinField_im]; ring

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTFermionMagneticInverseSquareComplexEFE

end
