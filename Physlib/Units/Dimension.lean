/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Physical dimensions with an information base `[I]`, and the scalar-action no-go

The dimensional-analysis system extended with an independent **information dimension** `[I]` (bits / nats /
qubits) beyond the ISO/ISQ basis `{L, T, M, C, Θ}`. A `Dimension` is a tuple of rational exponents forming a
commutative group under multiplication (exponent addition).

**Why `[I]`.** The ISO basis has no slot to distinguish a *dimensionless count of information* from a generic
dimensionless ratio — the Brillouin (1956) / Landauer (1961) / Bennett (1982) gap. With `I𝓭` an independent base,
`[k_B] = E·Θ⁻¹·I⁻¹`, Boltzmann entropy `[S] = I`, and `S/ℏ` becomes a *typed* dimensionless ratio.

**The no-go.** The information dimension is dimensionally **barred from a scalar action**: for a complex action
`S = S_R + i S_I` read as an ordinary scalar (`[i]` dimensionless, `i² = −1`), homogeneity `[S_R] = [i·S_I]` forces
`[S_I] = [S_R] = E·T`, which collides with angular momentum, and *no* dimensionless `[i]` can carry an
informational imaginary part `[S_I] = E·T·I` (it would require `[i] = I⁻¹`, contradicting `[i] = 1`). Information
can enter only the *graded* (non-scalar) action — the dimensional root of why the entropic/complex action is
graded.

References: L. Brillouin (1956); R. Landauer (1961); C.H. Bennett (1982). No new axioms.
-/

set_option autoImplicit false

namespace Physlib.Units

@[expose] public section

/-- A physical **dimension**: rational exponents of the base dimensions, including an information base `[I]`. -/
structure Dimension where
  /-- The length dimension. -/
  length : ℚ
  /-- The time dimension. -/
  time : ℚ
  /-- The mass dimension. -/
  mass : ℚ
  /-- The charge dimension. -/
  charge : ℚ
  /-- The temperature dimension. -/
  temperature : ℚ
  /-- The information dimension (bits / nats / qubits). -/
  information : ℚ := 0

namespace Dimension

@[ext]
lemma ext {d1 d2 : Dimension} (h1 : d1.length = d2.length) (h2 : d1.time = d2.time)
    (h3 : d1.mass = d2.mass) (h4 : d1.charge = d2.charge) (h5 : d1.temperature = d2.temperature)
    (h6 : d1.information = d2.information) : d1 = d2 := by
  cases d1; cases d2; congr

instance : Mul Dimension where
  mul d1 d2 := ⟨d1.length + d2.length, d1.time + d2.time, d1.mass + d2.mass, d1.charge + d2.charge,
    d1.temperature + d2.temperature, d1.information + d2.information⟩

@[simp] lemma length_mul (d1 d2 : Dimension) : (d1 * d2).length = d1.length + d2.length := rfl
@[simp] lemma time_mul (d1 d2 : Dimension) : (d1 * d2).time = d1.time + d2.time := rfl
@[simp] lemma mass_mul (d1 d2 : Dimension) : (d1 * d2).mass = d1.mass + d2.mass := rfl
@[simp] lemma charge_mul (d1 d2 : Dimension) : (d1 * d2).charge = d1.charge + d2.charge := rfl
@[simp] lemma temperature_mul (d1 d2 : Dimension) :
    (d1 * d2).temperature = d1.temperature + d2.temperature := rfl
@[simp] lemma information_mul (d1 d2 : Dimension) :
    (d1 * d2).information = d1.information + d2.information := rfl

instance : One Dimension where one := ⟨0, 0, 0, 0, 0, 0⟩

@[simp] lemma one_length : (1 : Dimension).length = 0 := rfl
@[simp] lemma one_time : (1 : Dimension).time = 0 := rfl
@[simp] lemma one_mass : (1 : Dimension).mass = 0 := rfl
@[simp] lemma one_charge : (1 : Dimension).charge = 0 := rfl
@[simp] lemma one_temperature : (1 : Dimension).temperature = 0 := rfl
@[simp] lemma one_information : (1 : Dimension).information = 0 := rfl

instance : CommGroup Dimension where
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  inv d := ⟨-d.length, -d.time, -d.mass, -d.charge, -d.temperature, -d.information⟩
  inv_mul_cancel a := by ext <;> simp
  mul_comm a b := by ext <;> simp <;> ring

/-! ## The base dimensions (including information `[I]`) -/

/-- Length `[L]`. -/
def L𝓭 : Dimension := ⟨1, 0, 0, 0, 0, 0⟩
/-- Time `[T]`. -/
def T𝓭 : Dimension := ⟨0, 1, 0, 0, 0, 0⟩
/-- Mass `[M]`. -/
def M𝓭 : Dimension := ⟨0, 0, 1, 0, 0, 0⟩
/-- Charge `[C]`. -/
def C𝓭 : Dimension := ⟨0, 0, 0, 1, 0, 0⟩
/-- Temperature `[Θ]`. -/
def Θ𝓭 : Dimension := ⟨0, 0, 0, 0, 1, 0⟩
/-- **Information `[I]`** (bits / nats / qubits) — the independent base beyond the ISO/ISQ set. -/
def I𝓭 : Dimension := ⟨0, 0, 0, 0, 0, 1⟩

/-- Energy `[E] = M·L²·T⁻²`. -/
def energy_dim : Dimension := ⟨2, -2, 1, 0, 0, 0⟩
/-- Angular momentum `[M·L²·T⁻¹]`. -/
def angularMomentum_dim : Dimension := ⟨2, -1, 1, 0, 0, 0⟩

/-- **The information dimension is not dimensionless** `I𝓭 ≠ 1`. -/
theorem I𝓭_ne_one : I𝓭 ≠ 1 := by
  intro h
  have := congrArg Dimension.information h
  simp [I𝓭] at this

/-- **A dimension with `d² = 1` is dimensionless** `d² = 1 ⟹ d = 1` — the exponents are torsion-free rationals, so
`2·(exponent) = 0` forces every exponent to vanish. -/
theorem dimensionless_of_sq_one (d : Dimension) (h : d * d = 1) : d = 1 := by
  have hl : d.length + d.length = 0 := by simpa using congrArg Dimension.length h
  have ht : d.time + d.time = 0 := by simpa using congrArg Dimension.time h
  have hm : d.mass + d.mass = 0 := by simpa using congrArg Dimension.mass h
  have hc : d.charge + d.charge = 0 := by simpa using congrArg Dimension.charge h
  have hT : d.temperature + d.temperature = 0 := by simpa using congrArg Dimension.temperature h
  have hi : d.information + d.information = 0 := by simpa using congrArg Dimension.information h
  ext <;> simp only [one_length, one_time, one_mass, one_charge, one_temperature, one_information]
  all_goals linarith

/-! ## The scalar-action no-go: information is barred from a scalar action -/

/-- **The scalar action collides with angular momentum** `[E·T] = M·L²·T⁻¹`. -/
theorem scalarAction_collides_angularMomentum : energy_dim * T𝓭 = angularMomentum_dim := by
  ext
  all_goals simp only [energy_dim, T𝓭, angularMomentum_dim, length_mul, time_mul, mass_mul,
    charge_mul, temperature_mul, information_mul]
  all_goals norm_num

/-- **The scalar imaginary action is forced to be mechanical** `[S_I] = E·T`. Homogeneity `[S_R] = [i·S_I]` with a
mechanical real part `E·T` and a dimensionless imaginary unit (`i² = −1`, `[i]` dimensionless) forces
`[S_I] = E·T`. -/
theorem scalar_imaginary_inert {imag S_I : Dimension} (hi : imag * imag = 1)
    (hhom : energy_dim * T𝓭 = imag * S_I) : S_I = energy_dim * T𝓭 := by
  rw [dimensionless_of_sq_one imag hi, one_mul] at hhom
  exact hhom.symm

/-- **The scalar imaginary action carries zero information** `[S_I].information = 0` — information is dimensionally
barred from a scalar action. -/
theorem scalar_imaginary_information_zero {imag S_I : Dimension} (hi : imag * imag = 1)
    (hhom : energy_dim * T𝓭 = imag * S_I) : S_I.information = 0 := by
  rw [scalar_imaginary_inert hi hhom]
  simp [energy_dim, T𝓭]

/-- **No-go (the collision is unavoidable).** There is no scalar complex action with a mechanical real part `E·T`
and a dimensionless imaginary unit that differs from angular momentum: homogeneity collapses the whole action onto
`E·T = M·L²·T⁻¹`, identical to angular momentum. -/
theorem scalar_action_noGo :
    ¬ ∃ actionDim imag S_I : Dimension,
        imag * imag = 1 ∧ actionDim = energy_dim * T𝓭 ∧ actionDim = imag * S_I
          ∧ actionDim ≠ angularMomentum_dim := by
  rintro ⟨actionDim, imag, S_I, _, hreal, _, hne⟩
  exact hne (hreal.trans scalarAction_collides_angularMomentum)

/-- **No-go (information cannot enter a scalar action).** There is no dimensionless imaginary unit making the
scalar action homogeneous with an *informational* imaginary part `[S_I] = E·T·I`: it would require `[i] = I⁻¹`,
contradicting `[i] = 1`. The information dimension is available only to the graded (non-scalar) action. -/
theorem scalar_no_informational_imaginary :
    ¬ ∃ imag : Dimension, imag * imag = 1 ∧ imag * (energy_dim * T𝓭 * I𝓭) = energy_dim * T𝓭 := by
  rintro ⟨imag, hsq, hhom⟩
  rw [dimensionless_of_sq_one imag hsq, one_mul] at hhom
  exact I𝓭_ne_one (mul_left_cancel (a := energy_dim * T𝓭) (by rw [mul_one]; exact hhom))

end Dimension

end

end Physlib.Units
