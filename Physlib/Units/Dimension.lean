/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
/-!

# Dimension

In this module we define the type `Dimension` which records the dimension
of a physical quantity.

-/

@[expose] public section

open NNReal

/-!

## Defining dimensions

-/

/-- The foundational dimensions.
  Defined in the order ⟨length, time, mass, charge, temperature, information⟩.

  The `information` slot tracks the dimension of *information content*
  (Shannon entropy, bits, qubits) as a primitive base, independent of
  thermodynamic temperature. Without it the SI/ISQ basis cannot
  distinguish dimensionless ratios from genuinely dimensionless
  information measures — the Brillouin (1956) / Landauer (1961)
  argument. Boltzmann's constant `k_B` then has dimension
  `[E·Θ⁻¹·I⁻¹]` (energy per temperature per nat). -/
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
lemma ext {d1 d2 : Dimension}
    (h1 : d1.length = d2.length)
    (h2 : d1.time = d2.time)
    (h3 : d1.mass = d2.mass)
    (h4 : d1.charge = d2.charge)
    (h5 : d1.temperature = d2.temperature)
    (h6 : d1.information = d2.information) :
    d1 = d2 := by
  cases d1
  cases d2
  congr

instance : Mul Dimension where
  mul d1 d2 := ⟨d1.length + d2.length,
    d1.time + d2.time,
    d1.mass + d2.mass,
    d1.charge + d2.charge,
    d1.temperature + d2.temperature,
    d1.information + d2.information⟩

@[simp]
lemma time_mul (d1 d2 : Dimension) :
    (d1 * d2).time = d1.time + d2.time := rfl

@[simp]
lemma length_mul (d1 d2 : Dimension) :
    (d1 * d2).length = d1.length + d2.length := rfl

@[simp]
lemma mass_mul (d1 d2 : Dimension) :
    (d1 * d2).mass = d1.mass + d2.mass := rfl

@[simp]
lemma charge_mul (d1 d2 : Dimension) :
    (d1 * d2).charge = d1.charge + d2.charge := rfl

@[simp]
lemma temperature_mul (d1 d2 : Dimension) :
    (d1 * d2).temperature = d1.temperature + d2.temperature := rfl

@[simp]
lemma information_mul (d1 d2 : Dimension) :
    (d1 * d2).information = d1.information + d2.information := rfl

instance : One Dimension where
  one := ⟨0, 0, 0, 0, 0, 0⟩

@[simp]
lemma one_length : (1 : Dimension).length = 0 := rfl
@[simp]
lemma one_time : (1 : Dimension).time = 0 := rfl

@[simp]
lemma one_mass : (1 : Dimension).mass = 0 := rfl

@[simp]
lemma one_charge : (1 : Dimension).charge = 0 := rfl

@[simp]
lemma one_temperature : (1 : Dimension).temperature = 0 := rfl

@[simp]
lemma one_information : (1 : Dimension).information = 0 := rfl

instance : CommGroup Dimension where
  mul_assoc a b c := by
    ext
    all_goals
      simp only [length_mul, time_mul, mass_mul, charge_mul, temperature_mul,
        information_mul]
      ring
  one_mul a := by
    ext
    all_goals
      simp
  mul_one a := by
    ext
    all_goals
      simp
  inv d := ⟨-d.length, -d.time, -d.mass, -d.charge, -d.temperature, -d.information⟩
  inv_mul_cancel a := by
    ext
    all_goals simp
  mul_comm a b := by
    ext
    all_goals
      simp only [length_mul, time_mul, mass_mul, charge_mul, temperature_mul,
        information_mul]
      ring

@[simp]
lemma inv_length (d : Dimension) : d⁻¹.length = -d.length := rfl

@[simp]
lemma inv_time (d : Dimension) : d⁻¹.time = -d.time := rfl

@[simp]
lemma inv_mass (d : Dimension) : d⁻¹.mass = -d.mass := rfl

@[simp]
lemma inv_charge (d : Dimension) : d⁻¹.charge = -d.charge := rfl

@[simp]
lemma inv_temperature (d : Dimension) : d⁻¹.temperature = -d.temperature := rfl

@[simp]
lemma inv_information (d : Dimension) : d⁻¹.information = -d.information := rfl

@[simp]
lemma div_length (d1 d2 : Dimension) : (d1 / d2).length = d1.length - d2.length := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

@[simp]
lemma div_time (d1 d2 : Dimension) : (d1 / d2).time = d1.time - d2.time := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

@[simp]
lemma div_mass (d1 d2 : Dimension) : (d1 / d2).mass = d1.mass - d2.mass := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

@[simp]
lemma div_charge (d1 d2 : Dimension) : (d1 / d2).charge = d1.charge - d2.charge := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

@[simp]
lemma div_temperature (d1 d2 : Dimension) :
    (d1 / d2).temperature = d1.temperature - d2.temperature := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

@[simp]
lemma div_information (d1 d2 : Dimension) :
    (d1 / d2).information = d1.information - d2.information := by
  rw [div_eq_mul_inv, information_mul, inv_information]
  ring

@[simp]
lemma npow_length (d : Dimension) (n : ℕ) : (d ^ n).length = n • d.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, length_mul, ih, succ_nsmul]

@[simp]
lemma npow_time (d : Dimension) (n : ℕ) : (d ^ n).time = n • d.time := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, time_mul, ih, succ_nsmul]

@[simp]
lemma npow_mass (d : Dimension) (n : ℕ) : (d ^ n).mass = n • d.mass := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mass_mul, ih, succ_nsmul]

@[simp]
lemma npow_charge (d : Dimension) (n : ℕ) : (d ^ n).charge = n • d.charge := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, charge_mul, ih, succ_nsmul]

@[simp]
lemma npow_temperature (d : Dimension) (n : ℕ) : (d ^ n).temperature = n • d.temperature := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, temperature_mul, ih, succ_nsmul]

@[simp]
lemma npow_information (d : Dimension) (n : ℕ) :
    (d ^ n).information = n • d.information := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [@pow_add]
    simp [ih]
    ring

instance : Pow Dimension ℚ where
  pow d n := ⟨d.length * n, d.time * n, d.mass * n, d.charge * n, d.temperature * n,
    d.information * n⟩

@[simp]
lemma qpow_length (d : Dimension) (n : ℚ) : (d ^ n).length = d.length * n := rfl

@[simp]
lemma qpow_time (d : Dimension) (n : ℚ) : (d ^ n).time = d.time * n := rfl

@[simp]
lemma qpow_mass (d : Dimension) (n : ℚ) : (d ^ n).mass = d.mass * n := rfl

@[simp]
lemma qpow_charge (d : Dimension) (n : ℚ) : (d ^ n).charge = d.charge * n := rfl

@[simp]
lemma qpow_temperature (d : Dimension) (n : ℚ) :
    (d ^ n).temperature = d.temperature * n := rfl

@[simp]
lemma qpow_information (d : Dimension) (n : ℚ) :
    (d ^ n).information = d.information * n := rfl

/-- The dimension corresponding to length. -/
def L𝓭 : Dimension := ⟨1, 0, 0, 0, 0, 0⟩

@[simp]
lemma L𝓭_length : L𝓭.length = 1 := by rfl

@[simp]
lemma L𝓭_time : L𝓭.time = 0 := by rfl

@[simp]
lemma L𝓭_mass : L𝓭.mass = 0 := by rfl

@[simp]
lemma L𝓭_charge : L𝓭.charge = 0 := by rfl

@[simp]
lemma L𝓭_temperature : L𝓭.temperature = 0 := by rfl

@[simp]
lemma L𝓭_information : L𝓭.information = 0 := by rfl

/-- The dimension corresponding to time. -/
def T𝓭 : Dimension := ⟨0, 1, 0, 0, 0, 0⟩

@[simp]
lemma T𝓭_length : T𝓭.length = 0 := by rfl

@[simp]
lemma T𝓭_time : T𝓭.time = 1 := by rfl

@[simp]
lemma T𝓭_mass : T𝓭.mass = 0 := by rfl

@[simp]
lemma T𝓭_charge : T𝓭.charge = 0 := by rfl

@[simp]
lemma T𝓭_temperature : T𝓭.temperature = 0 := by rfl

@[simp]
lemma T𝓭_information : T𝓭.information = 0 := by rfl

/-- The dimension corresponding to mass. -/
def M𝓭 : Dimension := ⟨0, 0, 1, 0, 0, 0⟩

/-- The dimension corresponding to charge. -/
def C𝓭 : Dimension := ⟨0, 0, 0, 1, 0, 0⟩

/-- The dimension corresponding to temperature. -/
def Θ𝓭 : Dimension := ⟨0, 0, 0, 0, 1, 0⟩

/-- The dimension corresponding to information (bits / nats / qubits).

Justification: the ISO/ISQ basis `{L, T, M, C, Θ}` has no slot to
distinguish a *dimensionless count of information* (a number of bits,
nats, or qubits) from a generic dimensionless ratio. This is the
Brillouin (1956) / Landauer (1961) / Bennett (1982) gap: Shannon
entropy `H = − Σ pᵢ log pᵢ` and Boltzmann entropy `S = k_B ln Ω`
should be the same physical quantity (Boltzmann's `k_B` converts
between them), but in the SI basis they are forced to share a slot
with all other dimensionless numbers.

With `I𝓭` as an independent base, `[k_B] = E·Θ⁻¹·I⁻¹`,
`[S_Boltzmann] = I`, and `S/ℏ` becomes a *typed* dimensionless ratio
(both numerator and denominator encode `I`). -/
def I𝓭 : Dimension := ⟨0, 0, 0, 0, 0, 1⟩

@[simp] lemma M𝓭_length      : M𝓭.length      = 0 := rfl
@[simp] lemma M𝓭_time        : M𝓭.time        = 0 := rfl
@[simp] lemma M𝓭_mass        : M𝓭.mass        = 1 := rfl
@[simp] lemma M𝓭_charge      : M𝓭.charge      = 0 := rfl
@[simp] lemma M𝓭_temperature : M𝓭.temperature = 0 := rfl
@[simp] lemma M𝓭_information : M𝓭.information = 0 := rfl

@[simp] lemma C𝓭_length      : C𝓭.length      = 0 := rfl
@[simp] lemma C𝓭_time        : C𝓭.time        = 0 := rfl
@[simp] lemma C𝓭_mass        : C𝓭.mass        = 0 := rfl
@[simp] lemma C𝓭_charge      : C𝓭.charge      = 1 := rfl
@[simp] lemma C𝓭_temperature : C𝓭.temperature = 0 := rfl
@[simp] lemma C𝓭_information : C𝓭.information = 0 := rfl

@[simp] lemma Θ𝓭_length      : Θ𝓭.length      = 0 := rfl
@[simp] lemma Θ𝓭_time        : Θ𝓭.time        = 0 := rfl
@[simp] lemma Θ𝓭_mass        : Θ𝓭.mass        = 0 := rfl
@[simp] lemma Θ𝓭_charge      : Θ𝓭.charge      = 0 := rfl
@[simp] lemma Θ𝓭_temperature : Θ𝓭.temperature = 1 := rfl
@[simp] lemma Θ𝓭_information : Θ𝓭.information = 0 := rfl

@[simp] lemma I𝓭_length      : I𝓭.length      = 0 := rfl
@[simp] lemma I𝓭_time        : I𝓭.time        = 0 := rfl
@[simp] lemma I𝓭_mass        : I𝓭.mass        = 0 := rfl
@[simp] lemma I𝓭_charge      : I𝓭.charge      = 0 := rfl
@[simp] lemma I𝓭_temperature : I𝓭.temperature = 0 := rfl
@[simp] lemma I𝓭_information : I𝓭.information = 1 := rfl

end Dimension
