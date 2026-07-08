/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Units.InformationDimensionCollision
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The intrinsically complex (graded) action resolves `action = angular momentum`

In the Nagao–Nielsen **Complex Action Theory** (complex-action) the action is intrinsically
**complex**, `S = S_R + i·S_I`. This is introduced in §1 (Introduction), Prog. Theor.
Phys. **126**(6), p. 1021–1022: the path-integral integrand `exp(i S/ℏ)` is complex,
so `S` may be complex (complex-action vs the real-action theory RAT). The formal real/imaginary
split `S = Re_{} S + i·Im_{} S` is the *modified real/imaginary parts* of §2.3,
Eqs (2.8)–(2.14), p. 1025–1026 (`{}`-real (2.13), purely `{}`-imaginary (2.14)); the
non-hermitian operators with complex eigenvalues are §2.1, Eqs (2.1)–(2.3), p. 1024.

**complex-action is the scalar reading.** In complex-action the phase `i S/ℏ` must be dimensionless, so the
complex action is an **action-dimensioned scalar**: both `S_R` and `S_I` encode `E·T`.
That is exactly the *scalar reading* below — to which the no-go (`scalar_action_noGo`)
applies, so the complex-action action is dimensionally indistinguishable from angular momentum.

Here we instead read the action **graded**: `S_R` on the mechanical action axis `E·T`,
`S_I` on the **information** axis `I𝓭` — a genuine direct sum of two dimensional axes,
not a single homogeneous scalar. **This dimensional/information-graded reading is an
addition beyond Nagao–Nielsen complex-action**, not part of their formulation; it is what resolves
the `action = angular momentum` collision the scalar complex-action reading cannot.

## Why the imaginary unit is dimensionless — two agreeing reasons

The imaginary unit `i` is dimensionless, `[i] = 1`, for two independent reasons that
agree:

* **Algebraic** (the mathematical backstop, `dimensionless_of_sq_one`): `i² = −1` is
  dimensionless, so `[i]² = 1`, and in the rational-exponent dimension group that forces
  `[i] = 1` (`q + q = 0 ⟹ q = 0`).
* **Informational** (the physical content): the imaginary axis is information, and the
  information dimension is a *count* — its quantum is the **pure real `ln 2`**, the
  Landauer minimum (proven minimal in `DiscreteEntropicClock`, `landauerFloor = ln 2`).

Because the information quantum is `informationQuantum = ln 2`, a dimensionless *number*
(a count of nats), the imaginary unit — which advances the imaginary action by one such
quantum — has no dimensional exponent: `[i] = 1`. The dimension `I𝓭` is encoded in
the imaginary *action* `S_I` (`imaginaryAction_dim`), not by the *unit* `i`
(`imaginaryUnit_dim`); these are distinct (`imaginaryUnit_dim_ne_imaginaryAction_dim`).
That is precisely the special character of `[I]`: alone among the base dimensions it has
a proven minimal quantum that is a pure number.

## How the collision is resolved — one coordinate of the dimension vector

Dimensions are 6-tuples `⟨length, time, mass, charge, temperature, information⟩`.

**The collision (scalar reading).** Both quantities have the *same* vector:
```
  angular momentum  = r × p = M·L²·T⁻¹ = ⟨2, −1, 1, 0, 0, 0⟩
  action (scalar)   =   E·T = M·L²·T⁻¹ = ⟨2, −1, 1, 0, 0, 0⟩      ← information = 0
```
Identical ⇒ they collide (`scalarAction_collides_angularMomentum`).

**The resolution (graded reading).** The graded complex action puts its two parts on
*different* axes — `S_R` on `E·T` and `S_I` on the information axis `I𝓭` — so the full
action occupies both, giving it a *nonzero information coordinate*:
```
  complex action    = ⟨2, −1, 1, 0, 0, 1⟩      ← information = 1
  angular momentum  = ⟨2, −1, 1, 0, 0, 0⟩      ← information = 0
                                          ↑
                            differ in exactly ONE coordinate
```
The information coordinate is `1` for the action but `0` for purely-mechanical angular
momentum. One coordinate differs ⇒ the vectors are distinct
(`complexAction_ne_angularMomentum`); the Lean proof projects the assumed equality onto
the information axis (`congrArg Dimension.information`) and derives `1 = 0`.

**Why the scalar reading could not do this.** Homogeneity of `S_R + i·S_I` forces `S_I`
to share `S_R`'s dimension `E·T`, so the action never leaves the mechanical axes
(information stays `0`) and collides. The graded reading lets `S_I` live on its own
information axis; what permits that — without `i` having to bridge `E·T` and `I` — is
that **`i` is dimensionless** (it merely marks the imaginary direction), for the two
agreeing reasons above.

**In one sentence.** The collision is resolved because the imaginary action `S_I`
includes the information dimension `[I]`, giving the complex action a nonzero information
coordinate (`1`) that angular momentum lacks (`0`) — the two vectors, identical on the
mechanical axes, now differ on the information axis.

## References

* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys.
  **126**(6) (2011) 1021–1049, doi:10.1143/PTP.126.1021. The complex action
  `S = S_R + i·S_I`: §1 (Introduction), p. 1021–1022 (`exp(i S/ℏ)` complex ⟹ `S`
  complex). Formal real/imaginary split `Re_{} S`, `Im_{} S`: §2.3, Eqs (2.8)–(2.14),
  p. 1025–1026. Non-hermitian `q̂_new, p̂_new` with `[q̂_new, p̂_new] = iℏ`: §2.1,
  Eqs (2.1)–(2.3), p. 1024.
* K. Nagao, H. B. Nielsen, *Momentum relation and classical limit in the
  future-not-included complex action theory*, PTEP **2018**(1) 013B02,
  doi:10.1093/ptep/ptx176.
* L. Brillouin, *Science and Information Theory* (1956); R. Landauer, *Irreversibility
  and heat generation in the computing process* (1961) — the information dimension `[I]`
  and the floor `ln 2`.
-/

set_option autoImplicit false

open Dimension Physlib.Units.InformationDimensionCollision

@[expose] public section

namespace Physlib.Units.ComplexActionDimension

/-- **The information (Landauer) quantum**: the minimal information value, a *pure
positive real* `ln 2`. Proven minimal in `DiscreteEntropicClock`
(`landauerFloor = ln 2`). Being a count of nats, it is dimensionless as a *value*; its
*dimension* is the information axis `I𝓭`. This is the reason the imaginary unit is
dimensionless. -/
noncomputable def informationQuantum : ℝ := Real.log 2

theorem informationQuantum_pos : 0 < informationQuantum :=
  Real.log_pos (by norm_num)

/-- **Algebraic corroboration that `[i] = 1`.** Any dimension squaring to the unit *is*
the unit: `d·d = 1 ⟹ d = 1`. So the bare constraint `[i]² = 1` (from `i² = −1`
dimensionless) independently forces `[i] = 1` — the rational exponents are torsion-free
(`q + q = 0 ⟹ q = 0`). This agrees with the informational reason; the informational one
includes the physics, this is the mathematical backstop. -/
theorem dimensionless_of_sq_one (d : Dimension) (h : d * d = 1) : d = 1 := by
  have e : ∀ q : ℚ, q + q = 0 → q = 0 := fun q hq => by linarith
  ext
  · exact e _ (by have := congrArg Dimension.length h; simpa using this)
  · exact e _ (by have := congrArg Dimension.time h; simpa using this)
  · exact e _ (by have := congrArg Dimension.mass h; simpa using this)
  · exact e _ (by have := congrArg Dimension.charge h; simpa using this)
  · exact e _ (by have := congrArg Dimension.temperature h; simpa using this)
  · exact e _ (by have := congrArg Dimension.information h; simpa using this)

/-- The imaginary action `S_I` is intrinsically **informational**: `[S_I] = I𝓭`. -/
def imaginaryAction_dim : Dimension := I𝓭

/-- **The imaginary unit is dimensionless**, `[i] = 1` — because its quantum is the pure
real `informationQuantum = ln 2`. The dimension `I𝓭` sits on the imaginary action, not
on the unit. -/
def imaginaryUnit_dim : Dimension := 1

/-- The dimensionless imaginary unit is distinct from the informational imaginary axis:
`[i] = 1 ≠ I𝓭 = [S_I]`. The unit includes the dimensionless value `ln 2`; the action
includes the dimension `[I]`. -/
theorem imaginaryUnit_dim_ne_imaginaryAction_dim :
    imaginaryUnit_dim ≠ imaginaryAction_dim := by
  rw [imaginaryUnit_dim, imaginaryAction_dim]
  exact fun h => I𝓭_ne_one h.symm

/-- The homogeneous-scalar reading of the action: both parts on the mechanical axis,
`[S] = E·T`. -/
def scalarAction_dim : Dimension := energy_dim * T𝓭

/-- **Scalar reading: the collision stands.** `[E·T] = M·L²·T⁻¹ =` angular momentum. -/
theorem scalarAction_collides_angularMomentum :
    scalarAction_dim = angularMomentum_dim := by
  unfold scalarAction_dim
  ext <;> norm_num [energy_dim, angularMomentum_dim]

/-! ## No-go theorem for the scalar reading

Under the scalar reading the imaginary part is **dimensionally inert**: homogeneity plus
a dimensionless imaginary unit force `[S_I] = [S_R]`, so no information can enter and the
action is locked onto the mechanical axis. Hence it can never be distinguished from
angular momentum — the collision is unavoidable. -/

/-- **The scalar imaginary action is forced to be mechanical.** Homogeneity
`[S_R] = [i·S_I]` with mechanical real part `[S_R] = E·T` and a dimensionless imaginary
unit (`imag·imag = 1`, i.e. `i² = −1`) forces `[S_I] = E·T`. The imaginary action cannot
occupy any other axis. -/
theorem scalar_imaginary_inert {imag S_I : Dimension}
    (hi : imag * imag = 1) (hhom : energy_dim * T𝓭 = imag * S_I) :
    S_I = energy_dim * T𝓭 := by
  rw [dimensionless_of_sq_one imag hi, one_mul] at hhom
  exact hhom.symm

/-- **The scalar imaginary action records zero information**: `[S_I].information = 0`.
Information is dimensionally barred from a scalar action. -/
theorem scalar_imaginary_information_zero {imag S_I : Dimension}
    (hi : imag * imag = 1) (hhom : energy_dim * T𝓭 = imag * S_I) :
    S_I.information = 0 := by
  rw [scalar_imaginary_inert hi hhom]; simp [energy_dim]

/-- **No-go (collision is unavoidable).** There is no scalar complex action with a
mechanical real part `E·T` and a dimensionless imaginary unit that differs from angular
momentum: homogeneity collapses the whole action onto `E·T = M·L²·T⁻¹`, identical to
angular momentum. -/
theorem scalar_action_noGo :
    ¬ ∃ actionDim imag S_I : Dimension,
        imag * imag = 1
      ∧ actionDim = energy_dim * T𝓭
      ∧ actionDim = imag * S_I
      ∧ actionDim ≠ angularMomentum_dim := by
  rintro ⟨actionDim, imag, S_I, _, hreal, _, hne⟩
  exact hne (hreal.trans scalarAction_collides_angularMomentum)

/-- **No-go (information cannot enter a scalar action).** There is no dimensionless
imaginary unit making the scalar action homogeneous with an *informational* imaginary
part `[S_I] = E·T·I`: it would require `[i] = I⁻¹`, contradicting `[i] = 1`. The
information dimension is available only to the graded (non-scalar) action — which is
exactly why the graded reading resolves the collision. -/
theorem scalar_no_informational_imaginary :
    ¬ ∃ imag : Dimension, imag * imag = 1 ∧
      imag * (energy_dim * T𝓭 * I𝓭) = energy_dim * T𝓭 := by
  rintro ⟨imag, hsq, hhom⟩
  rw [dimensionless_of_sq_one imag hsq, one_mul] at hhom
  exact I𝓭_ne_one (mul_left_cancel (a := energy_dim * T𝓭) (by rw [mul_one]; exact hhom))

/-- **The graded complex action**: real part `E·T`, imaginary part `I𝓭`. Its dimensional
content has a nonzero information exponent. -/
def complexAction_dim : Dimension := energy_dim * T𝓭 * imaginaryAction_dim

/-- **`action = angular momentum` is resolved.** The two dimension vectors are identical
on the mechanical axes but differ on the **information** coordinate: the graded complex
action has information exponent `1` (encoded in `S_I`), angular momentum has `0`. One
coordinate differs, so the dimensions are distinct. The proof projects the assumed
equality onto the information axis and derives `1 = 0`. -/
theorem complexAction_ne_angularMomentum :
    complexAction_dim ≠ angularMomentum_dim := by
  intro h
  have := congrArg Dimension.information h
  simp [complexAction_dim, imaginaryAction_dim, energy_dim, angularMomentum_dim] at this

end Physlib.Units.ComplexActionDimension

end
