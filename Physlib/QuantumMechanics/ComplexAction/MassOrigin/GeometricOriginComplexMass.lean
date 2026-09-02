/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MassOrigin.GeometricOriginOfMass
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-!
# The geometric origin of mass complexified: the Nagao–Nielsen complex mass is the complex Hessian

Links the geometric origin of mass (`MassOrigin.GeometricOriginOfMass`, `m² = V''(v₀)`) to the **Nagao–Nielsen
complex mass** (`ComplexEinstein.ComplexMassEinsteinEquations`, `complexMass m_R m_I = m_R + i m_I`). Complexifying the
symmetry-breaking potential to the complex-action/entropic-time complex action (a *real* reversible coupling `a_R` plus an
*imaginary* entropic coupling `a_I`), the **complex mass-squared is the complex Hessian at the vacuum**:

  `m_C² = V_R''(v₀) + i V_I''(v₀) = complexMass (8 a_R v₀²) (8 a_I v₀²)`   (`complexGeometricMassSq`),

so the two sectors of the Nagao–Nielsen complex mass are the curvatures of the two action sectors:

* the **real part** `Re m_C² = 8 a_R v₀² = V_R''(v₀)` is the **reversible** geometric mass² — the curvature of
  the real symmetry-breaking potential (`complexGeometricMassSq_re`);
* the **imaginary part** `Im m_C² = 8 a_I v₀² = V_I''(v₀)` is the **entropic** mass² — the curvature of the
  imaginary/entropic potential, the Nagao–Nielsen `m_I` sector (`complexGeometricMassSq_im`).

The Nagao–Nielsen **Feynman–Kac convergence** `Im m_C² > 0` (`momentum_integral_converges_iff`) holds
**iff the entropic coupling is positive** `a_I > 0` (`complexGeometricMassSq_im_pos_iff`): the imaginary
geometric curvature is the Euclidean damping. At `a_I = 0` (no entropic coupling) the complex mass is real
(`complexGeometricMassSq_reversible`), the reversible geometric mass.

So the geometric origin of mass extends to the complex action: the Nagao–Nielsen complex mass-squared is the
complex Hessian of the complex-action/entropic-time symmetry-breaking potential at the vacuum — real curvature = reversible mass,
imaginary curvature = entropic mass, with positivity the convergence condition.

* **§A — the complex mass-squared as the complex Hessian** (`complexGeometricMassSq`,
  `complexGeometricMassSq_re`, `complexGeometricMassSq_im`).
* **§B — convergence and the reversible limit** (`complexGeometricMassSq_im_pos_iff`,
  `complexGeometricMassSq_reversible`, `geometric_origin_complex_mass`).

## References

* The Nagao–Nielsen complex action / complex mass `m = m_R + i m_I` (`Im m > 0` convergence); the
  Landau–Ginzburg curvature origin of mass. Carriers: `MassOrigin.GeometricOriginOfMass` (`vacuumMassSq`, `vacuumMassSq_eq`),
  `ComplexEinstein.ComplexMassEinsteinEquations` (`complexMass`, `complexMass_reversible`), `PathIntegral.MomentumPathIntegral`
  (`momentum_integral_converges_iff`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.MassOrigin.GeometricOriginComplexMass

open Physlib.QuantumMechanics.ComplexAction.MassOrigin.GeometricOriginOfMass
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations


/-- **The complex (Nagao–Nielsen) mass-squared** `m_C² = V_R''(v₀) + i V_I''(v₀)` — the complex Hessian of
the complex-action/entropic-time symmetry-breaking potential at the vacuum, with the real reversible coupling `a_R` and the
imaginary entropic coupling `a_I`. It *is* the Nagao–Nielsen complex mass `complexMass` of the two
curvatures. -/
noncomputable def complexGeometricMassSq (a_R a_I v₀ : ℝ) : ℂ :=
  complexMass (vacuumMassSq a_R v₀) (vacuumMassSq a_I v₀)

/-- **[Real part = reversible geometric mass²] `Re m_C² = 8 a_R v₀² = V_R''(v₀)`.** -/
lemma complexGeometricMassSq_re (a_R a_I v₀ : ℝ) :
    (complexGeometricMassSq a_R a_I v₀).re = 8 * a_R * v₀ ^ 2 := by
  rw [complexGeometricMassSq]
  simp only [complexMass, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, zero_mul, add_zero]
  rw [vacuumMassSq_eq]

/-- **[Imaginary part = entropic geometric mass²] `Im m_C² = 8 a_I v₀² = V_I''(v₀)`** — the Nagao–Nielsen
entropic mass sector. -/
lemma complexGeometricMassSq_im (a_R a_I v₀ : ℝ) :
    (complexGeometricMassSq a_R a_I v₀).im = 8 * a_I * v₀ ^ 2 := by
  rw [complexGeometricMassSq]
  simp only [complexMass, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, mul_zero, mul_one, zero_add, add_zero]
  rw [vacuumMassSq_eq]


/-- **[Nagao–Nielsen convergence ⟺ positive entropic coupling] `Im m_C² > 0 ⟺ a_I > 0`.** The Feynman–Kac /
Euclidean damping condition `Im m > 0` of the Nagao–Nielsen complex mass holds exactly when the entropic
coupling is positive — the imaginary geometric curvature `V_I''(v₀) = 8 a_I v₀²` is the damping. -/
lemma complexGeometricMassSq_im_pos_iff (a_R a_I v₀ : ℝ) (hv : v₀ ≠ 0) :
    0 < (complexGeometricMassSq a_R a_I v₀).im ↔ 0 < a_I := by
  rw [complexGeometricMassSq_im]
  have hv2 : (0 : ℝ) < v₀ ^ 2 := by positivity
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [hv2, h, hc]
  · intro h; positivity

/-- **[Reversible limit] at `a_I = 0` the complex mass is real.** With no entropic coupling the
Nagao–Nielsen complex mass-squared reduces to the reversible geometric mass² `V_R''(v₀)`
(`complexMass_reversible`). -/
lemma complexGeometricMassSq_reversible (a_R v₀ : ℝ) :
    complexGeometricMassSq a_R 0 v₀ = (vacuumMassSq a_R v₀ : ℂ) := by
  rw [complexGeometricMassSq, show vacuumMassSq 0 v₀ = 0 from by rw [vacuumMassSq_eq]; ring,
    complexMass_reversible]

/-- **[The geometric origin of mass, complexified to the Nagao–Nielsen complex mass].** Complexifying the
symmetry-breaking potential (real coupling `a_R`, imaginary entropic coupling `a_I`):

* the complex mass-squared is the complex Hessian, with **real part** the reversible geometric mass²
  `Re m_C² = 8 a_R v₀²` and **imaginary part** the entropic mass² `Im m_C² = 8 a_I v₀²`;
* the Nagao–Nielsen Feynman–Kac convergence `Im m_C² > 0` holds iff the entropic coupling `a_I > 0`;
* at `a_I = 0` the complex mass is real — the reversible geometric mass.

The Nagao–Nielsen complex mass-squared is the complex Hessian of the complex-action/entropic-time symmetry-breaking potential at
the vacuum: real curvature = reversible mass, imaginary curvature = entropic mass. -/
lemma geometric_origin_complex_mass (a_R a_I v₀ : ℝ) (hv : v₀ ≠ 0) :
    (complexGeometricMassSq a_R a_I v₀).re = 8 * a_R * v₀ ^ 2
      ∧ (complexGeometricMassSq a_R a_I v₀).im = 8 * a_I * v₀ ^ 2
      ∧ (0 < (complexGeometricMassSq a_R a_I v₀).im ↔ 0 < a_I)
      ∧ complexGeometricMassSq a_R 0 v₀ = (vacuumMassSq a_R v₀ : ℂ) :=
  ⟨complexGeometricMassSq_re a_R a_I v₀, complexGeometricMassSq_im a_R a_I v₀,
    complexGeometricMassSq_im_pos_iff a_R a_I v₀ hv, complexGeometricMassSq_reversible a_R v₀⟩

end Physlib.QuantumMechanics.ComplexAction.MassOrigin.GeometricOriginComplexMass

end
