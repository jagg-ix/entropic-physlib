/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass
meta import Zil

/-!
# Einstein's *rest* energy `E = mc²` with the Nagao–Nielsen complex mass

**Scope.** This file covers only the **rest energy** `E = mc²` (zero momentum, `p = 0`): there is no
momentum variable here. The *full* Einstein energy–momentum relation `E² = (pc)² + (mc²)²` — with the
`+(pc)²` term — and its consistency with the Dirac equation, the TDSE, and the TISE live in
`ComplexEinstein.FullEinsteinDispersionConsistency`, which uses this file's rest energy `mc²` as the `p = 0` term.

`Bogoliubov.DiracEinsteinMass` identified the gap `Δ` as Einstein's rest energy `mc²` for a *real*
mass. This file promotes the rest energy `E = mc²` to the **Nagao–Nielsen complex mass**
`m = m_R + i m_I` (arXiv:1304.4017 §5, 1902.01424) and shows the physical inertial mass is the
Nagao–Nielsen **effective mass** `m_eff = |m|²/Re m`.

## The complex Einstein energy

With a complex mass `m = m_R + i m_I`, Einstein's `E = mc²` gives a **complex rest energy**:

  `E = m c² = m_R c² + i (m_I c²)`   (`complexEinsteinEnergy`),

whose real part `m_R c²` is the ordinary rest energy and whose imaginary part `m_I c²` is the
entropic / dissipative energy (`H_I` sector). The reversible limit `m_I = 0` recovers the real
Einstein relation (`complexEinsteinEnergy_reversible`).

## The physical inertial mass is the effective mass `|m|²/Re m`

The real, physically observed inertial mass is the Nagao–Nielsen effective mass

  `m_eff = m_R + m_I²/m_R = (m_R² + m_I²)/m_R = |m|² / Re m`

(`effectiveMass_eq_complexMass_normSq_div`, where `|m|² = normSq(m_R + i m_I)`). The imaginary mass
`m_I` **raises** the Einstein rest energy above `m_R c²` (`effectiveEinsteinEnergy_ge`); it returns
to `m_R c²` exactly in the reversible limit `m_I = 0` (`effectiveEinsteinEnergy_reversible`).

## Main results

* `complexMass`, `complexMass_normSq` — the complex mass and its squared modulus `m_R² + m_I²`.
* `complexEinsteinEnergy`, `_re`, `_im`, `_reversible` — `E = mc²` with complex mass.
* `dirac_entropic_gap_eq_imaginary_einstein`, `reversible_no_entropic` — the imaginary rest-energy gap
  identities used by Dirac, electromagnetic, and complex-Einstein bridge modules.
* `effectiveMass_eq_complexMass_normSq_div` — `m_eff = |m|²/Re m` (Nagao–Nielsen Eq. 5.10).
* `effectiveEinsteinEnergy`, `_ge`, `_reversible`, `relativisticInertialMass_effectiveEinsteinEnergy`
  — the effective Einstein rest energy `m_eff c²`.
* `complexMass_einstein_equations` — the bundled complex `E = mc²`.

## References

* A. Einstein, Ann. Phys. 18 (1905) 639 (`E = mc²`); K. Nagao, H. B. Nielsen, arXiv:1304.4017 §5
  (complex mass `m_R + i m_I`, effective mass Eq. 5.10), arXiv:1902.01424.
* `Bogoliubov.DiracEinsteinMass`, `MassOrigin.BosonicInertialMass`, `PathIntegral.MomentumPathIntegral` (this development);
  `Complex.normSq_add_mul_I` (Mathlib).


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations


/-- **The Nagao–Nielsen complex mass** `m = m_R + i m_I` (real and imaginary mass). -/
def complexMass (m_R m_I : ℝ) : ℂ := (m_R : ℂ) + (m_I : ℂ) * Complex.I

@[simp] lemma complexMass_re (m_R m_I : ℝ) : (complexMass m_R m_I).re = m_R := by
  simp [complexMass]

@[simp] lemma complexMass_im (m_R m_I : ℝ) : (complexMass m_R m_I).im = m_I := by
  simp [complexMass]

/-- **The squared modulus of the complex mass** `|m|² = m_R² + m_I²`. -/
lemma complexMass_normSq (m_R m_I : ℝ) :
    Complex.normSq (complexMass m_R m_I) = m_R ^ 2 + m_I ^ 2 :=
  Complex.normSq_add_mul_I m_R m_I

/-- **The reversible limit is a real mass**: `m_I = 0 ⟹ m = m_R`. -/
lemma complexMass_reversible (m_R : ℝ) : complexMass m_R 0 = (m_R : ℂ) := by
  simp [complexMass]


/-- **The complex Einstein energy** `E = m c²` for a complex mass `m = m_R + i m_I`. -/
def complexEinsteinEnergy (m_R m_I c : ℝ) : ℂ := complexMass m_R m_I * ((c ^ 2 : ℝ) : ℂ)

/-- **The real part is the ordinary rest energy** `Re E = m_R c²`. -/
lemma complexEinsteinEnergy_re (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R m_I c).re = m_R * c ^ 2 := by
  unfold complexEinsteinEnergy
  rw [Complex.mul_re, complexMass_re, complexMass_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The imaginary part is the entropic / dissipative energy** `Im E = m_I c²` (the `H_I` sector). -/
lemma complexEinsteinEnergy_im (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R m_I c).im = m_I * c ^ 2 := by
  unfold complexEinsteinEnergy
  rw [Complex.mul_im, complexMass_re, complexMass_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **[Entropic gap = imaginary Einstein energy]** `m_I c² = Im(E)`. The
imaginary rest-energy gap used by the complex-mass Dirac and electromagnetic bridge
modules is exactly the imaginary part of `E = (m_R + i m_I)c²`. -/
lemma dirac_entropic_gap_eq_imaginary_einstein (m_R m_I c : ℝ) :
    (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im :=
  (complexEinsteinEnergy_im m_R m_I c).symm

/-- **The reversible limit is the real Einstein relation** `E = (m_R c² : ℝ)` (`m_I = 0`, no
imaginary energy). -/
lemma complexEinsteinEnergy_reversible (m_R c : ℝ) :
    complexEinsteinEnergy m_R 0 c = ((m_R * c ^ 2 : ℝ) : ℂ) := by
  unfold complexEinsteinEnergy complexMass
  rw [Complex.ofReal_zero, zero_mul, add_zero, ← Complex.ofReal_mul]

/-- **[Reversible limit has no imaginary Einstein energy].** At `m_I = 0`, the
imaginary part of the complex Einstein rest energy vanishes. -/
lemma reversible_no_entropic (m_R c : ℝ) :
    (complexEinsteinEnergy m_R 0 c).im = 0 := by
  rw [complexEinsteinEnergy_im]; ring


/-- **`m_eff = |m|²/Re m`** (Nagao–Nielsen Eq. 5.10): the physical inertial mass is the squared
modulus of the complex mass over its real part. -/
lemma effectiveMass_eq_complexMass_normSq_div (m_R m_I : ℝ) (hm_R : m_R ≠ 0) :
    effectiveMass m_R m_I = Complex.normSq (complexMass m_R m_I) / m_R := by
  rw [effectiveMass_eq_normSq_div m_R m_I hm_R, complexMass_normSq]

/-- **The effective Einstein rest energy** `E_eff = m_eff c²` (the energy of the physical inertial
mass). -/
def effectiveEinsteinEnergy (m_R m_I c : ℝ) : ℝ := effectiveMass m_R m_I * c ^ 2

/-- **`E_eff = |m|² c² / Re m`** — the effective Einstein rest energy from the complex mass. -/
lemma effectiveEinsteinEnergy_eq_normSq (m_R m_I c : ℝ) (hm_R : m_R ≠ 0) :
    effectiveEinsteinEnergy m_R m_I c = Complex.normSq (complexMass m_R m_I) * c ^ 2 / m_R := by
  unfold effectiveEinsteinEnergy
  rw [effectiveMass_eq_complexMass_normSq_div m_R m_I hm_R]
  ring

/-- **The imaginary mass raises the Einstein rest energy** `m_R c² ≤ m_eff c²`: dissipation
(`m_I ≠ 0`) adds inertia, increasing the rest energy above the bare `m_R c²`. -/
lemma effectiveEinsteinEnergy_ge (m_R m_I c : ℝ) (hm_R : 0 < m_R) :
    m_R * c ^ 2 ≤ effectiveEinsteinEnergy m_R m_I c := by
  unfold effectiveEinsteinEnergy
  nlinarith [effectiveMass_ge m_R m_I hm_R, sq_nonneg c]

/-- **The reversible limit is ordinary Einstein** `E_eff = m_R c²` (`m_I = 0`). -/
lemma effectiveEinsteinEnergy_reversible (m_R c : ℝ) (hm_R : m_R ≠ 0) :
    effectiveEinsteinEnergy m_R 0 c = m_R * c ^ 2 := by
  unfold effectiveEinsteinEnergy
  rw [show effectiveMass m_R 0 = m_R from (effectiveMass_eq_self_iff m_R 0 hm_R).mpr rfl]

/-- **The Einstein inertial mass of the effective rest energy is the effective mass**
`relativisticInertialMass (m_eff c²) c = m_eff` (`E_eff/c² = m_eff`, mass–energy equivalence). -/
lemma relativisticInertialMass_effectiveEinsteinEnergy (m_R m_I c : ℝ) (hc : c ≠ 0) :
    relativisticInertialMass (effectiveEinsteinEnergy m_R m_I c) c = effectiveMass m_R m_I := by
  unfold relativisticInertialMass effectiveEinsteinEnergy
  rw [mul_div_assoc, div_self (pow_ne_zero 2 hc), mul_one]


/-- **Einstein's mass–energy equations with the Nagao–Nielsen complex mass.** For `m_R > 0`,
`c ≠ 0`:

* `E = m c²` splits into the real rest energy `m_R c²` and the imaginary (entropic) energy `m_I c²`;
* the physical inertial mass is the Nagao–Nielsen effective mass `m_eff = |m|²/Re m`;
* the imaginary mass raises the rest energy, `m_R c² ≤ m_eff c²`, with equality in the reversible
  limit `m_I = 0`. -/
lemma complexMass_einstein_equations (m_R m_I c : ℝ) (hm_R : 0 < m_R) :
    (complexEinsteinEnergy m_R m_I c).re = m_R * c ^ 2
      ∧ (complexEinsteinEnergy m_R m_I c).im = m_I * c ^ 2
      ∧ effectiveMass m_R m_I = Complex.normSq (complexMass m_R m_I) / m_R
      ∧ m_R * c ^ 2 ≤ effectiveEinsteinEnergy m_R m_I c
      ∧ effectiveEinsteinEnergy m_R 0 c = m_R * c ^ 2 :=
  ⟨complexEinsteinEnergy_re m_R m_I c, complexEinsteinEnergy_im m_R m_I c,
   effectiveMass_eq_complexMass_normSq_div m_R m_I hm_R.ne',
   effectiveEinsteinEnergy_ge m_R m_I c hm_R,
   effectiveEinsteinEnergy_reversible m_R c hm_R.ne'⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

end

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexEinsteinEnergy_im where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexMass_im",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexMass_re",
  formalizes @ "claim:the-imaginary-part-of-the-complex-einstein-rest-energy-m-R-plus-i-m-I-times-c-squared-is-m-I-c-squared"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.dirac_entropic_gap_eq_imaginary_einstein where
  formalizes @ "claim:the-dirac-bogoliubov-entropic-gap-m-I-c-squared-equals-the-imaginary-einstein-energy-im-of-the-complex-rest-energy",
  supported_by @ "object:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.effectiveEinsteinEnergy_eq_normSq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.effectiveMass_eq_complexMass_normSq_div",
  formalizes @ "claim:the-nagao-nielsen-effective-einstein-rest-energy-is-the-complex-mass-norm-squared-times-c-squared-over-the-real-mass"

zil attach Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexMass_einstein_equations where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexEinsteinEnergy_im",
  formalizes @ "claim:the-complex-mass-einstein-rest-energy-has-real-part-m-R-c-squared-imaginary-part-m-I-c-squared-effective-mass-norm-squared-over-m-R-with-the-imaginary-mass-raising-the-rest-energy-above-m-R-c-squared-and-the-reversible-limit-recovering-the-real-relation",
  requires @ "claim:the-imaginary-part-of-the-complex-einstein-rest-energy-m-R-plus-i-m-I-times-c-squared-is-m-I-c-squared"

zil_file_contract physlib.complexMassEinsteinEquations where
  promises "Einstein's rest energy E = mc² promoted to the Nagao-Nielsen complex mass m = m_R + i m_I (arXiv:1304.4017, 1902.01424). The complex Einstein rest energy E = (m_R + i m_I) c² has real part m_R c² and imaginary part m_I c² (complexEinsteinEnergy_im), and that imaginary part is exactly the Dirac/Bogoliubov entropic gap (dirac_entropic_gap_eq_imaginary_einstein). The physical inertial mass is the Nagao-Nielsen effective mass |m|²/Re m, giving effective rest energy |m|² c²/m_R (effectiveEinsteinEnergy_eq_normSq); a nonzero imaginary mass raises the rest energy above the bare m_R c², and the reversible m_I = 0 limit recovers the real relation (complexMass_einstein_equations)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexMass",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexEinsteinEnergy"]
  forbids_substitutes ["the physical identification of m_I with a decay/dissipation rate and the Nagao-Nielsen non-Hermitian construction, which are the cited inputs",
    "any momentum-dependent energy-momentum relation, this file covers only the rest energy at p = 0"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexEinsteinEnergy_im,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.dirac_entropic_gap_eq_imaginary_einstein,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.effectiveEinsteinEnergy_eq_normSq,
    Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations.complexMass_einstein_equations]

/- ZIL-END -/
