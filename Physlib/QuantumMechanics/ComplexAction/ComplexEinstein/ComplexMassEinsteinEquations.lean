/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.DiracEinsteinMass
public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass

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
* `effectiveMass_eq_complexMass_normSq_div` — `m_eff = |m|²/Re m` (Nagao–Nielsen Eq. 5.10).
* `effectiveEinsteinEnergy`, `_ge`, `_reversible`, `relativisticInertialMass_effectiveEinsteinEnergy`
  — the effective Einstein rest energy `m_eff c²`.
* `complexMass_einstein_equations` — the bundled complex `E = mc²`.

## References

* A. Einstein, Ann. Phys. 18 (1905) 639 (`E = mc²`); K. Nagao, H. B. Nielsen, arXiv:1304.4017 §5
  (complex mass `m_R + i m_I`, effective mass Eq. 5.10), arXiv:1902.01424.
* `Bogoliubov.DiracEinsteinMass`, `MassOrigin.BosonicInertialMass`, `PathIntegral.MomentumPathIntegral` (this development);
  `Complex.normSq_add_mul_I` (Mathlib).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.MomentumPathIntegral
open Physlib.QuantumMechanics.ComplexAction.MassOrigin.BosonicInertialMass

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-! ## §A — the Nagao–Nielsen complex mass and its modulus -/

/-- **The Nagao–Nielsen complex mass** `m = m_R + i m_I` (real and imaginary mass). -/
def complexMass (m_R m_I : ℝ) : ℂ := (m_R : ℂ) + (m_I : ℂ) * Complex.I

@[simp] theorem complexMass_re (m_R m_I : ℝ) : (complexMass m_R m_I).re = m_R := by
  simp [complexMass]

@[simp] theorem complexMass_im (m_R m_I : ℝ) : (complexMass m_R m_I).im = m_I := by
  simp [complexMass]

/-- **The squared modulus of the complex mass** `|m|² = m_R² + m_I²`. -/
theorem complexMass_normSq (m_R m_I : ℝ) :
    Complex.normSq (complexMass m_R m_I) = m_R ^ 2 + m_I ^ 2 :=
  Complex.normSq_add_mul_I m_R m_I

/-- **The reversible limit is a real mass**: `m_I = 0 ⟹ m = m_R`. -/
theorem complexMass_reversible (m_R : ℝ) : complexMass m_R 0 = (m_R : ℂ) := by
  simp [complexMass]

/-! ## §B — Einstein's `E = mc²` with the complex mass -/

/-- **The complex Einstein energy** `E = m c²` for a complex mass `m = m_R + i m_I`. -/
def complexEinsteinEnergy (m_R m_I c : ℝ) : ℂ := complexMass m_R m_I * ((c ^ 2 : ℝ) : ℂ)

/-- **The real part is the ordinary rest energy** `Re E = m_R c²`. -/
theorem complexEinsteinEnergy_re (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R m_I c).re = m_R * c ^ 2 := by
  unfold complexEinsteinEnergy
  rw [Complex.mul_re, complexMass_re, complexMass_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The imaginary part is the entropic / dissipative energy** `Im E = m_I c²` (the `H_I` sector). -/
theorem complexEinsteinEnergy_im (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R m_I c).im = m_I * c ^ 2 := by
  unfold complexEinsteinEnergy
  rw [Complex.mul_im, complexMass_re, complexMass_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The reversible limit is the real Einstein relation** `E = (m_R c² : ℝ)` (`m_I = 0`, no
imaginary energy). -/
theorem complexEinsteinEnergy_reversible (m_R c : ℝ) :
    complexEinsteinEnergy m_R 0 c = ((m_R * c ^ 2 : ℝ) : ℂ) := by
  unfold complexEinsteinEnergy complexMass
  rw [Complex.ofReal_zero, zero_mul, add_zero, ← Complex.ofReal_mul]

/-! ## §C — the physical inertial mass is the effective mass `|m|²/Re m` -/

/-- **`m_eff = |m|²/Re m`** (Nagao–Nielsen Eq. 5.10): the physical inertial mass is the squared
modulus of the complex mass over its real part. -/
theorem effectiveMass_eq_complexMass_normSq_div (m_R m_I : ℝ) (hm_R : m_R ≠ 0) :
    effectiveMass m_R m_I = Complex.normSq (complexMass m_R m_I) / m_R := by
  rw [effectiveMass_eq_normSq_div m_R m_I hm_R, complexMass_normSq]

/-- **The effective Einstein rest energy** `E_eff = m_eff c²` (the energy of the physical inertial
mass). -/
def effectiveEinsteinEnergy (m_R m_I c : ℝ) : ℝ := effectiveMass m_R m_I * c ^ 2

/-- **`E_eff = |m|² c² / Re m`** — the effective Einstein rest energy from the complex mass. -/
theorem effectiveEinsteinEnergy_eq_normSq (m_R m_I c : ℝ) (hm_R : m_R ≠ 0) :
    effectiveEinsteinEnergy m_R m_I c = Complex.normSq (complexMass m_R m_I) * c ^ 2 / m_R := by
  unfold effectiveEinsteinEnergy
  rw [effectiveMass_eq_complexMass_normSq_div m_R m_I hm_R]
  ring

/-- **The imaginary mass raises the Einstein rest energy** `m_R c² ≤ m_eff c²`: dissipation
(`m_I ≠ 0`) adds inertia, increasing the rest energy above the bare `m_R c²`. -/
theorem effectiveEinsteinEnergy_ge (m_R m_I c : ℝ) (hm_R : 0 < m_R) :
    m_R * c ^ 2 ≤ effectiveEinsteinEnergy m_R m_I c := by
  unfold effectiveEinsteinEnergy
  nlinarith [effectiveMass_ge m_R m_I hm_R, sq_nonneg c]

/-- **The reversible limit is ordinary Einstein** `E_eff = m_R c²` (`m_I = 0`). -/
theorem effectiveEinsteinEnergy_reversible (m_R c : ℝ) (hm_R : m_R ≠ 0) :
    effectiveEinsteinEnergy m_R 0 c = m_R * c ^ 2 := by
  unfold effectiveEinsteinEnergy
  rw [show effectiveMass m_R 0 = m_R from (effectiveMass_eq_self_iff m_R 0 hm_R).mpr rfl]

/-- **The Einstein inertial mass of the effective rest energy is the effective mass**
`relativisticInertialMass (m_eff c²) c = m_eff` (`E_eff/c² = m_eff`, mass–energy equivalence). -/
theorem relativisticInertialMass_effectiveEinsteinEnergy (m_R m_I c : ℝ) (hc : c ≠ 0) :
    relativisticInertialMass (effectiveEinsteinEnergy m_R m_I c) c = effectiveMass m_R m_I := by
  unfold relativisticInertialMass effectiveEinsteinEnergy
  rw [mul_div_assoc, div_self (pow_ne_zero 2 hc), mul_one]

/-! ## §D — the bundled complex Einstein mass–energy equations -/

/-- **Einstein's mass–energy equations with the Nagao–Nielsen complex mass.** For `m_R > 0`,
`c ≠ 0`:

* `E = m c²` splits into the real rest energy `m_R c²` and the imaginary (entropic) energy `m_I c²`;
* the physical inertial mass is the Nagao–Nielsen effective mass `m_eff = |m|²/Re m`;
* the imaginary mass raises the rest energy, `m_R c² ≤ m_eff c²`, with equality in the reversible
  limit `m_I = 0`. -/
theorem complexMass_einstein_equations (m_R m_I c : ℝ) (hm_R : 0 < m_R) :
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
