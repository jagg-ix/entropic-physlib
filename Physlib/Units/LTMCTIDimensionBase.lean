/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Units.LTMCTDimensionBase

/-!

# The information-extended dimension basis

`LTMCTIDimensionBase` is PhysLib's default basis `LTMCTDimensionBase` — length, time,
mass, charge, temperature — extended by a sixth generator, **information** `[I]`,
tracking information content (Shannon entropy, bits, nats, qubits) as a base dimension
independent of thermodynamic temperature.

The physical claim, due to Brillouin (1956) and Landauer (1961), is that without `[I]`
the SI/ISQ basis cannot separate a genuinely dimensionless ratio from an information
measure. With `[I]` independent, Boltzmann's constant carries `[E·Θ⁻¹·I⁻¹]` — energy
per temperature per nat — rather than `[E·Θ⁻¹]`.

This module gives `Dimension LTMCTIDimensionBase` the same concrete API that
`Physlib.Units.LTMCTDimensionBase` gives the five-base default:

* the `ofLTMCTI` constructor from six exponents, with its exponent simp lemmas; and
* the named generators `L𝓭`, `T𝓭`, `M𝓭`, `C𝓭`, `Θ𝓭`, `I𝓭`, shown to be the generic
  `single` base vectors.

Exponents are read with the generic `Dimension.exponent` projection —
`d.exponent .information` — rather than named `.length`/`.time`/… accessors, because
those names belong to the five-base default in the `Dimension` namespace and cannot be
overloaded for a second basis.

The two bases are related by the maps in `Physlib.Units.InformationDimensionCollision`:
an `Embedding` of the five-base into this one (faithful — no information is invented),
and the lossy `Projection` back (which is exactly the collapse the Brillouin/Landauer
argument is about).

-/

@[expose] public section

/-- The information-extended basis of base dimensions — `length`, `time`, `mass`,
  `charge`, `temperature`, `information`. This is `LTMCTDimensionBase` plus an
  independent information axis `[I]`. -/
inductive LTMCTIDimensionBase where
  /-- The length base dimension. -/
  | length
  /-- The time base dimension. -/
  | time
  /-- The mass base dimension. -/
  | mass
  /-- The charge base dimension. -/
  | charge
  /-- The temperature base dimension. -/
  | temperature
  /-- The information base dimension (bits / nats / qubits). -/
  | information
deriving DecidableEq

instance : Fintype LTMCTIDimensionBase where
  elems := {.length, .time, .mass, .charge, .temperature, .information}
  complete := fun x => by cases x <;> decide

namespace Dimension

namespace LTMCTI

/-! ## The constructor from six exponents -/

/-- Build a `LTMCTIDimensionBase` dimension from its six exponents, in the order
  `⟨length, time, mass, charge, temperature, information⟩`. -/
def ofLTMCTI (length time mass charge temperature information : ℚ) :
    Dimension LTMCTIDimensionBase :=
  ⟨fun
    | .length => length
    | .time => time
    | .mass => mass
    | .charge => charge
    | .temperature => temperature
    | .information => information⟩

@[simp]
lemma ofLTMCTI_length (l t m c θ i : ℚ) :
    (ofLTMCTI l t m c θ i).exponent .length = l := rfl

@[simp]
lemma ofLTMCTI_time (l t m c θ i : ℚ) :
    (ofLTMCTI l t m c θ i).exponent .time = t := rfl

@[simp]
lemma ofLTMCTI_mass (l t m c θ i : ℚ) :
    (ofLTMCTI l t m c θ i).exponent .mass = m := rfl

@[simp]
lemma ofLTMCTI_charge (l t m c θ i : ℚ) :
    (ofLTMCTI l t m c θ i).exponent .charge = c := rfl

@[simp]
lemma ofLTMCTI_temperature (l t m c θ i : ℚ) :
    (ofLTMCTI l t m c θ i).exponent .temperature = θ := rfl

@[simp]
lemma ofLTMCTI_information (l t m c θ i : ℚ) :
    (ofLTMCTI l t m c θ i).exponent .information = i := rfl

/-- Two dimensions over this basis agree exactly when all six exponents agree. -/
lemma ext_six {d1 d2 : Dimension LTMCTIDimensionBase}
    (hl : d1.exponent .length = d2.exponent .length)
    (ht : d1.exponent .time = d2.exponent .time)
    (hm : d1.exponent .mass = d2.exponent .mass)
    (hc : d1.exponent .charge = d2.exponent .charge)
    (hθ : d1.exponent .temperature = d2.exponent .temperature)
    (hi : d1.exponent .information = d2.exponent .information) : d1 = d2 := by
  ext b
  cases b <;> assumption

/-! ## The named generators

Each generator is the generic `single` base vector at its axis, so it carries exponent
`1` on its own axis and `0` elsewhere. -/

/-- The length base dimension `[L]`. -/
def L𝓭 : Dimension LTMCTIDimensionBase := ofLTMCTI 1 0 0 0 0 0
/-- The time base dimension `[T]`. -/
def T𝓭 : Dimension LTMCTIDimensionBase := ofLTMCTI 0 1 0 0 0 0
/-- The mass base dimension `[M]`. -/
def M𝓭 : Dimension LTMCTIDimensionBase := ofLTMCTI 0 0 1 0 0 0
/-- The charge base dimension `[C]`. -/
def C𝓭 : Dimension LTMCTIDimensionBase := ofLTMCTI 0 0 0 1 0 0
/-- The temperature base dimension `[Θ]`. -/
def Θ𝓭 : Dimension LTMCTIDimensionBase := ofLTMCTI 0 0 0 0 1 0
/-- The information base dimension `[I]` — the axis this basis adds. -/
def I𝓭 : Dimension LTMCTIDimensionBase := ofLTMCTI 0 0 0 0 0 1

/-! Unfolding lemmas: each generator is its `ofLTMCTI` tuple, so `simp` reduces a
generator's exponent on any concrete axis via the `ofLTMCTI_*` lemmas. -/

@[simp] lemma L𝓭_def : L𝓭 = ofLTMCTI 1 0 0 0 0 0 := rfl
@[simp] lemma T𝓭_def : T𝓭 = ofLTMCTI 0 1 0 0 0 0 := rfl
@[simp] lemma M𝓭_def : M𝓭 = ofLTMCTI 0 0 1 0 0 0 := rfl
@[simp] lemma C𝓭_def : C𝓭 = ofLTMCTI 0 0 0 1 0 0 := rfl
@[simp] lemma Θ𝓭_def : Θ𝓭 = ofLTMCTI 0 0 0 0 1 0 := rfl
@[simp] lemma I𝓭_def : I𝓭 = ofLTMCTI 0 0 0 0 0 1 := rfl

lemma L𝓭_eq_single : L𝓭 = single .length := by
  ext b; cases b <;> simp [L𝓭, ofLTMCTI, single_exponent]

lemma T𝓭_eq_single : T𝓭 = single .time := by
  ext b; cases b <;> simp [T𝓭, ofLTMCTI, single_exponent]

lemma M𝓭_eq_single : M𝓭 = single .mass := by
  ext b; cases b <;> simp [M𝓭, ofLTMCTI, single_exponent]

lemma C𝓭_eq_single : C𝓭 = single .charge := by
  ext b; cases b <;> simp [C𝓭, ofLTMCTI, single_exponent]

lemma Θ𝓭_eq_single : Θ𝓭 = single .temperature := by
  ext b; cases b <;> simp [Θ𝓭, ofLTMCTI, single_exponent]

lemma I𝓭_eq_single : I𝓭 = single .information := by
  ext b; cases b <;> simp [I𝓭, ofLTMCTI, single_exponent]

/-! Each generator's exponent on each axis: `1` on its own axis, `0` elsewhere. -/

@[simp] lemma L𝓭_length : L𝓭.exponent .length = 1 := rfl
@[simp] lemma L𝓭_time : L𝓭.exponent .time = 0 := rfl
@[simp] lemma L𝓭_mass : L𝓭.exponent .mass = 0 := rfl
@[simp] lemma L𝓭_charge : L𝓭.exponent .charge = 0 := rfl
@[simp] lemma L𝓭_temperature : L𝓭.exponent .temperature = 0 := rfl
@[simp] lemma L𝓭_information : L𝓭.exponent .information = 0 := rfl

@[simp] lemma T𝓭_length : T𝓭.exponent .length = 0 := rfl
@[simp] lemma T𝓭_time : T𝓭.exponent .time = 1 := rfl
@[simp] lemma T𝓭_mass : T𝓭.exponent .mass = 0 := rfl
@[simp] lemma T𝓭_charge : T𝓭.exponent .charge = 0 := rfl
@[simp] lemma T𝓭_temperature : T𝓭.exponent .temperature = 0 := rfl
@[simp] lemma T𝓭_information : T𝓭.exponent .information = 0 := rfl

@[simp] lemma M𝓭_length : M𝓭.exponent .length = 0 := rfl
@[simp] lemma M𝓭_time : M𝓭.exponent .time = 0 := rfl
@[simp] lemma M𝓭_mass : M𝓭.exponent .mass = 1 := rfl
@[simp] lemma M𝓭_charge : M𝓭.exponent .charge = 0 := rfl
@[simp] lemma M𝓭_temperature : M𝓭.exponent .temperature = 0 := rfl
@[simp] lemma M𝓭_information : M𝓭.exponent .information = 0 := rfl

@[simp] lemma C𝓭_length : C𝓭.exponent .length = 0 := rfl
@[simp] lemma C𝓭_time : C𝓭.exponent .time = 0 := rfl
@[simp] lemma C𝓭_mass : C𝓭.exponent .mass = 0 := rfl
@[simp] lemma C𝓭_charge : C𝓭.exponent .charge = 1 := rfl
@[simp] lemma C𝓭_temperature : C𝓭.exponent .temperature = 0 := rfl
@[simp] lemma C𝓭_information : C𝓭.exponent .information = 0 := rfl

@[simp] lemma Θ𝓭_length : Θ𝓭.exponent .length = 0 := rfl
@[simp] lemma Θ𝓭_time : Θ𝓭.exponent .time = 0 := rfl
@[simp] lemma Θ𝓭_mass : Θ𝓭.exponent .mass = 0 := rfl
@[simp] lemma Θ𝓭_charge : Θ𝓭.exponent .charge = 0 := rfl
@[simp] lemma Θ𝓭_temperature : Θ𝓭.exponent .temperature = 1 := rfl
@[simp] lemma Θ𝓭_information : Θ𝓭.exponent .information = 0 := rfl

@[simp] lemma I𝓭_length : I𝓭.exponent .length = 0 := rfl
@[simp] lemma I𝓭_time : I𝓭.exponent .time = 0 := rfl
@[simp] lemma I𝓭_mass : I𝓭.exponent .mass = 0 := rfl
@[simp] lemma I𝓭_charge : I𝓭.exponent .charge = 0 := rfl
@[simp] lemma I𝓭_temperature : I𝓭.exponent .temperature = 0 := rfl
@[simp] lemma I𝓭_information : I𝓭.exponent .information = 1 := rfl

/-! ## Relating the two bases

`toLTMCTI` includes the five-base default into this one; it is injective, so the
five-base dimensional algebra re-expresses faithfully here. -/

/-- The inclusion of base dimensions `LTMCTDimensionBase → LTMCTIDimensionBase`. -/
def base : LTMCTDimensionBase → LTMCTIDimensionBase
  | .length => .length
  | .time => .time
  | .mass => .mass
  | .charge => .charge
  | .temperature => .temperature

lemma base_injective : Function.Injective base := by
  intro a b h
  cases a <;> cases b <;> simp_all [base]

/-- The five-base default embeds faithfully in the information-extended basis: a
  dimension that mentions no information is carried across with every exponent
  preserved. -/
def embedding : Embedding LTMCTDimensionBase LTMCTIDimensionBase :=
  Embedding.ofBasis base base_injective

end LTMCTI

end Dimension
