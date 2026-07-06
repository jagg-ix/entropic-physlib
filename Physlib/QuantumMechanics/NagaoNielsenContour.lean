/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Physlib.GeneralRelativity.ComplexEinstein

/-!
# The Nagao–Nielsen convergence cone is the mass-shell Minkowski form

In the Nagao–Nielsen complex-coordinate formalism the coordinate and momentum are complex; the smeared complex
delta function converges only where

`L(q) ≡ (Re q)² − (Im q)² > 0`,

a Minkowski `(1,1)` quadratic form on the complex plane — the "timelike" steepest-descent region. Identifying the
energy–momentum coordinate `q = E/c + i·p` (with `E = √((mc²)² + (pc)²)` the Einstein energy), this convergence
form is exactly the real mass-shell `(E/c)² − p² = (mc)²`: the Nagao–Nielsen convergence cone on the complexified
coordinate and the relativistic mass-shell on real spacetime are one and the same `(1,1)` Minkowski structure. On
a complex mass `m = m_R + i m_I`, only the real part `m_R` enters this invariant (`ComplexEinstein`), the imaginary
`m_I` being the non-geometric entropic damping.

References: K. Nagao, H.B. Nielsen, arXiv:1304.4017 (§2). No new axioms.
-/

set_option autoImplicit false

open Physlib.GeneralRelativity.ComplexEinstein

@[expose] public section

namespace Physlib.QuantumMechanics.NagaoNielsenContour

/-! ## The convergence cone -/

/-- **The Nagao–Nielsen convergence quadratic form** `L(q) = (Re q)² − (Im q)²` — a Minkowski `(1,1)` form on the
complexified coordinate, whose positivity is the condition for the smeared complex delta to converge. -/
def nnLorentzForm (q : ℂ) : ℝ := q.re ^ 2 - q.im ^ 2

/-- **The convergence form is the real part of the square** `L(q) = Re(q²)`. -/
theorem nnLorentzForm_eq_re_sq (q : ℂ) : nnLorentzForm q = (q ^ 2).re := by
  unfold nnLorentzForm
  rw [pow_two q, Complex.mul_re]; ring

/-- **The Nagao–Nielsen convergence condition** `L(q) > 0` — the "timelike" region of the `(1,1)` cone. -/
def nnConverges (q : ℂ) : Prop := 0 < nnLorentzForm q

/-! ## The cone is the mass-shell -/

/-- **The Einstein energy** `E = √((mc²)² + (pc)²)`. -/
noncomputable def einsteinEnergy (m c p : ℝ) : ℝ := Real.sqrt ((m * c ^ 2) ^ 2 + (p * c) ^ 2)

/-- **The relativistic mass-shell** `(E/c)² − p² = (mc)²`. -/
theorem einstein_massShell (m c p : ℝ) (hc : c ≠ 0) :
    (einsteinEnergy m c p / c) ^ 2 - p ^ 2 = (m * c) ^ 2 := by
  unfold einsteinEnergy
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

/-- **The energy–momentum complex coordinate** `q = E/c + i·p`. -/
noncomputable def energyMomentumComplex (m c p : ℝ) : ℂ := ⟨einsteinEnergy m c p / c, p⟩

/-- **The convergence form of the energy–momentum coordinate is the mass-shell** `L(E/c + i·p) = (mc)²`: the
complex-coordinate cone evaluated on `q = E/c + i·p` is exactly the real Lorentz invariant `(E/c)² − p² = (mc)²`.
The steepest-descent cone is the forward mass-shell. -/
theorem nnLorentzForm_energyMomentum (m c p : ℝ) (hc : c ≠ 0) :
    nnLorentzForm (energyMomentumComplex m c p) = (m * c) ^ 2 := by
  unfold nnLorentzForm energyMomentumComplex
  exact einstein_massShell m c p hc

/-- **The contour converges iff the particle is massive** `nnConverges ↔ mc ≠ 0` — the `(1,1)` convergence cone is
precisely the forward mass-shell. -/
theorem nnConverges_energyMomentum_iff (m c p : ℝ) (hc : c ≠ 0) :
    nnConverges (energyMomentumComplex m c p) ↔ m * c ≠ 0 := by
  unfold nnConverges
  rw [nnLorentzForm_energyMomentum m c p hc]
  constructor
  · intro h heq; rw [heq] at h; norm_num at h
  · intro h; positivity

/-! ## The complex-Einstein real/imaginary split (only the real mass enters the shell) -/

/-- **The mass-shell-carrying rest energy is the real Einstein energy** `Re E_C = m_R c²` — only `m_R` gives the
ordinary rest energy protected by the real Lorentz geometry. -/
theorem massShell_real_rest_energy (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R m_I c).re = m_R * c ^ 2 :=
  complexEinsteinEnergy_re m_R m_I c

/-- **The imaginary part is the non-geometric entropic damping** `Im E_C = m_I c²` — the dissipative energy carried
by the complex action, never entering the Minkowski mass-shell invariant. -/
theorem entropicDamping_imaginary_rest_energy (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R m_I c).im = m_I * c ^ 2 :=
  complexEinsteinEnergy_im m_R m_I c

end Physlib.QuantumMechanics.NagaoNielsenContour

end
