/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The complex Einstein energy and entropic reversibility

The bridge from the entropic-dynamics quantum sector to general relativity. Promoting the mass to a **complex**
quantity `m = m_R + i m_I` — a real, inertial part `m_R` and an imaginary, entropic/dissipative part `m_I` —
gives the complex Einstein energy `E = m c²`, whose real part is the ordinary rest energy `m_R c²` and whose
imaginary part `m_I c²` is the entropic (dissipative) sector. The Einstein relation is **reversible** exactly when
the entropic sector vanishes:

`Im E = 0  ⟺  m_I = 0`,

mirroring, on the gravity side, the vanishing of entropy production at the Gibbs equilibrium of the
entropic-dynamics probability flow.

References: entropic gravity / complex-mass reconstruction. No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.GeneralRelativity.ComplexEinstein

/-- **The complex Einstein energy** `E = (m_R + i m_I) c²` — the energy of a complex mass, with real rest energy
`m_R c²` and imaginary entropic/dissipative energy `m_I c²`. -/
noncomputable def complexEinsteinEnergy (m_R m_I c : ℝ) : ℂ :=
  ((m_R : ℂ) + (m_I : ℂ) * Complex.I) * ((c ^ 2 : ℝ) : ℂ)

/-- **The real (inertial) Einstein energy** `Re E = m_R c²`. -/
theorem complexEinsteinEnergy_re (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R m_I c).re = m_R * c ^ 2 := by
  simp only [complexEinsteinEnergy, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re]
  ring

/-- **The imaginary (entropic) Einstein energy** `Im E = m_I c²`. -/
theorem complexEinsteinEnergy_im (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R m_I c).im = m_I * c ^ 2 := by
  simp only [complexEinsteinEnergy, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
    Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re]
  ring

/-- **Complex-Einstein reversibility is the vanishing entropic energy** `Im E = 0 ⟺ m_I = 0`. The imaginary
(entropic/dissipative) part of the complex Einstein energy vanishes exactly when the mass is reversible — the
real, non-dissipative Einstein relation, the gravity-side counterpart of the Gibbs equilibrium. -/
theorem reversible_iff_entropicEnergy_zero (m_R m_I c : ℝ) (hc : c ≠ 0) :
    (complexEinsteinEnergy m_R m_I c).im = 0 ↔ m_I = 0 := by
  rw [complexEinsteinEnergy_im, mul_eq_zero]
  simp [pow_eq_zero_iff, hc]

end Physlib.GeneralRelativity.ComplexEinstein

end
