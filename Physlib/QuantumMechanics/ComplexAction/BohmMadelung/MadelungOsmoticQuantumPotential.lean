/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Madelung complex velocity and the osmotic (Burgers) form of the quantum potential

Formalizes the genuine, exact algebraic kernel of the Schrödinger–Burgers / Madelung structure of
Büyükaşık–Pashaev (*J. Math. Phys.* **51** (2010) 122108): the **complex velocity** `V = v + iu` of the
damped parametric quantum fluid, and the identity expressing the **Bohm quantum potential** in
**osmotic-velocity (Burgers) form**.

For the Madelung representation `Ψ = √ρ · e^{iS/ħ}` of the damped parametric oscillator (mass `μ`), the
Schrödinger–Burgers complex velocity is `V = v + iu` (`complexVelocity`), with `v = (1/μ)∂_q S` the
**current** velocity (real part) and `u = (ħ/μ)·(∂_q√ρ)/√ρ` the **osmotic** velocity (imaginary part). The
osmotic velocity's spatial derivative is the quotient-rule expression (`osmoticVelocity_hasDerivAt`), and
the Bohm quantum potential `Q = −(ħ²/2μ)·(∂²_q√ρ)/√ρ` is *exactly*

  `Q = −(μ/2)·u² − (ħ/2)·∂_q u`   (`osmoticQuantumPotential_eq_bohm`),

the Burgers/osmotic form — the quantum potential as a dissipative term in the complex velocity field.

* **§A — the Schrödinger–Burgers complex velocity** (`complexVelocity`, `complexVelocity_re/_im`).
* **§B — the osmotic velocity and its derivative** (`osmoticVelocity_hasDerivAt`).
* **§C — the osmotic (Burgers) form of the quantum potential** (`osmoticQuantumPotential`,
  `osmoticQuantumPotential_eq_bohm`).

## References

* Ş. A. Büyükaşık, O. K. Pashaev, *J. Math. Phys.* 51 (2010) 122108 (Madelung representation, complex
  velocity `V = v + iu`, Schrödinger–Burgers equations). The osmotic form of the Bohm quantum potential
  `Q = −½μu² − ½ħ u'`.

No additional assumptions.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungOsmoticQuantumPotential

/-! ## §A — the Schrödinger–Burgers complex velocity `V = v + iu` -/

/-- **The Schrödinger–Burgers complex velocity** `V = v + iu` — the damped quantum fluid's complex
velocity, current velocity `v` (real) plus osmotic velocity `u` (imaginary). -/
def complexVelocity (v u : ℝ) : ℂ := (v : ℂ) + (u : ℂ) * Complex.I

/-- **[Real part is the current velocity] `Re V = v`.** -/
@[simp] theorem complexVelocity_re (v u : ℝ) : (complexVelocity v u).re = v := by
  simp [complexVelocity]

/-- **[Imaginary part is the osmotic velocity] `Im V = u`.** -/
@[simp] theorem complexVelocity_im (v u : ℝ) : (complexVelocity v u).im = u := by
  simp [complexVelocity]

/-! ## §B — the osmotic velocity and its spatial derivative -/

/-- **[The osmotic velocity's derivative] `∂_q[(ħ/μ)(g/R)] = (ħ/μ)·(g'R − gR')/R²`.** The osmotic velocity
`u = (ħ/μ)·(∂_q√ρ)/√ρ` (here `R = √ρ`, `g = ∂_q√ρ`) is differentiable with the quotient-rule derivative —
the `∂_q u` appearing in the Burgers form of the quantum potential. -/
theorem osmoticVelocity_hasDerivAt (ħ μ : ℝ) (R g : ℝ → ℝ) (Rd gd q : ℝ)
    (hR : HasDerivAt R Rd q) (hg : HasDerivAt g gd q) (hRq : R q ≠ 0) :
    HasDerivAt (fun x => ħ / μ * (g x / R x))
      (ħ / μ * ((gd * R q - g q * Rd) / R q ^ 2)) q :=
  (hg.div hR hRq).const_mul (ħ / μ)

/-! ## §C — the osmotic (Burgers) form of the quantum potential -/

/-- **The osmotic (Burgers) form of the quantum potential** `Q = −(μ/2)u² − (ħ/2)·u'` — the Bohm quantum
potential as a dissipative term in the complex velocity field (osmotic velocity `u`, its derivative
`u'`). -/
noncomputable def osmoticQuantumPotential (μ ħ u u' : ℝ) : ℝ := -(μ / 2) * u ^ 2 - (ħ / 2) * u'

/-- **[The osmotic form is the Bohm quantum potential] `−(μ/2)u² − (ħ/2)u' = −(ħ²/2μ)·(∂²√ρ)/√ρ`.** With
the osmotic velocity `u = (ħ/μ)·R'/R` and its quotient-rule derivative `u' = (ħ/μ)(R''/R − (R'/R)²)`
(`R = √ρ`), the Burgers/osmotic form of the quantum potential equals the standard Bohm quantum potential
`−(ħ²/2μ)·R''/R`. -/
theorem osmoticQuantumPotential_eq_bohm (μ ħ Rval Rd Rdd : ℝ) (hR : Rval ≠ 0) (hμ : μ ≠ 0) :
    osmoticQuantumPotential μ ħ (ħ / μ * (Rd / Rval)) (ħ / μ * (Rdd / Rval - (Rd / Rval) ^ 2))
      = -(ħ ^ 2 / (2 * μ)) * (Rdd / Rval) := by
  unfold osmoticQuantumPotential
  field_simp
  ring

/-- **[The Madelung complex velocity and osmotic quantum potential, assembled].** The Schrödinger–Burgers
complex velocity `V = v + iu` has current velocity `v` (real) and osmotic velocity `u` (imaginary); and
the Bohm quantum potential, written in osmotic (Burgers) form `−(μ/2)u² − (ħ/2)u'`, equals the standard
`−(ħ²/2μ)·R''/R`. The quantum potential is the dissipative term of the complex velocity field. -/
theorem madelung_complexVelocity_osmotic (v u μ ħ Rval Rd Rdd : ℝ) (hR : Rval ≠ 0) (hμ : μ ≠ 0) :
    (complexVelocity v u).re = v
      ∧ (complexVelocity v u).im = u
      ∧ osmoticQuantumPotential μ ħ (ħ / μ * (Rd / Rval)) (ħ / μ * (Rdd / Rval - (Rd / Rval) ^ 2))
          = -(ħ ^ 2 / (2 * μ)) * (Rdd / Rval) :=
  ⟨complexVelocity_re v u, complexVelocity_im v u,
    osmoticQuantumPotential_eq_bohm μ ħ Rval Rd Rdd hR hμ⟩

end Physlib.QuantumMechanics.ComplexAction.BohmMadelung.MadelungOsmoticQuantumPotential

end
