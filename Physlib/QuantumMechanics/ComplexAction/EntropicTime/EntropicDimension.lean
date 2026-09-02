/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.Units.LTMCTIDimensionBase
public import Mathlib.Tactic.NormNum

/-!
# Entropic-time dimensions: framework vs SI null

The Phase E `Discriminator` module argued informally that the
narrow universality of Planckian dissipation across material
classes favours the entropic-time framework over a dimensional-
analysis null hypothesis.  This module *formalises* the
dimensional content of that distinction using physlib's six-base
`Dimension LTMCTIDimensionBase` algebra `(L, T, M, C, Θ, I)`.

## The two dimensional conventions

**Null (standard SI/ISQ) convention.**  Five base dimensions
`{L, T, M, C, Θ}`; information is not a base.  Boltzmann's
constant has dimensions `[k_B] = E·Θ⁻¹`.  The only combination
of `{ℏ, k_B, T}` with dimension `[T]` is `β := ℏ/(k_B·T)`, with
`[β] = T`.  Under this null, dimensional analysis predicts that
any natural time scale at temperature `T` is of order `ℏ/(k_B·T)`
up to a dimensionless O(1) prefactor — but the prefactor is
unconstrained by dimensional analysis alone (Sedov 1959 §I.4).

**Framework convention** (Brillouin 1956; Landauer 1961;
Bennett 1982).  Six base dimensions `{L, T, M, C, Θ, I}`;
information `[I]` is an independent base, with Shannon entropy
`H = −Σ pᵢ log pᵢ` having dimension `[I]` and Boltzmann's
constant having dimensions `[k_B] = E·Θ⁻¹·I⁻¹` (the constant
that converts between dimensionless Shannon information and
thermodynamic entropy).  Under this convention,
`[k_B·T] = E·I⁻¹` and `[β] = ℏ/(k_B·T) = (E·T)/(E·I⁻¹) = T·I`
— the Planckian period carries an `I`-component.

## The dimensional discriminator

Under the null, the Planckian period is **dimensionally
indistinguishable** from any other natural time scale built
from `{ℏ, k_B, T}`.  It carries no information signature.

Under the framework, the Planckian period has dimension `T·I`,
so it is **dimensionally distinguishable** from a pure time
scale.  Any quantity that an empirical observation identifies
with `β` (e.g. a transport scattering time `τ_tr` in a strange
metal) must, under the framework convention, have the same
`T·I` dimension — equivalently, must be interpreted as the
inverse of an `[I⁻¹·T⁻¹]` rate, i.e., entropy-production per
unit time.

This is the dimensional reason the framework's narrow-
universality observation (Phase E) is non-trivial: under the
null there is no constraint beyond O(1); under the framework
the O(1) prefactor is the conversion factor between thermal
energy per nat and the system's actual entropy-production
rate, which is bounded by thermodynamic second-law arguments
(Planckian saturation; Hartnoll 2015).

## What this module proves

* `kB_dim_null` and `kB_dim_framework` — the two conventions
  for `[k_B]`, with explicit `Dimension LTMCTIDimensionBase`-valued definitions.
* `planckianPeriod_dim_null = T𝓭` (pure time, no `I`-component).
* `planckianPeriod_dim_framework = T𝓭 * I𝓭` (carries `I`).
* `planckianPeriod_dim_framework_div_null = I𝓭` — the
  dimensional discriminator: the two conventions differ
  exactly by an `I𝓭` factor on the Planckian period.
* `null_planckianPeriod_information_zero` and
  `framework_planckianPeriod_information_nonzero` — the
  presence or absence of an `[I]`-component is the
  framework-vs-null witness.
* `entropy_action_ratio_dim` — under the framework's
  Bender-style identity `τ_ent := S_I/ℏ` with `S_I` carrying
  action dimension `[E·T]`, the ratio is dimensionless (a
  count, not a physical time).  This is the convention used
  in `Physlib.Thermodynamics.SecondLaw`.

## References

* Brillouin, L. (1956), *Science and Information Theory*,
  Academic Press.  Argues that Shannon entropy and
  thermodynamic entropy should share a dimensional slot via
  `k_B`.
* Landauer, R. (1961), *Irreversibility and Heat Generation
  in the Computing Process*, IBM J. Res. Dev. **5**, 183-191.
  Information has physical dimensions; erasure costs `k_B·T·ln 2`.
* Bennett, C. H. (1982), *The thermodynamics of computation
  — a review*, Int. J. Theor. Phys. **21**, 905-940.
  Consolidates the information-dimensional argument.
* Sedov, L. I. (1959), *Similarity and Dimensional Methods in
  Mechanics*, Academic Press.  §I.4 on dimensional analysis
  limits (the "Π-theorem prefactor problem").
* Hartnoll, S. A. (2015), *Theory of universal incoherent
  metallic transport*, Nature Physics **11**, 54-61.
  Planckian saturation as a second-law upper bound.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDimension

open Dimension.LTMCTI


/-- **Energy dimension** in SI base units: `[E] = M·L²·T⁻²`. -/
def E𝓭 : Dimension LTMCTIDimensionBase := M𝓭 * L𝓭^(2 : ℚ) * T𝓭^(-2 : ℚ)

/-- **Action dimension**: `[ℏ] = E·T = M·L²·T⁻¹`. -/
def ℏ_dim : Dimension LTMCTIDimensionBase := E𝓭 * T𝓭

/-- **Null-convention Boltzmann constant**: `[k_B] = E·Θ⁻¹`. -/
def kB_dim_null : Dimension LTMCTIDimensionBase := E𝓭 * Θ𝓭⁻¹

/-- **Framework-convention Boltzmann constant**: `[k_B] = E·Θ⁻¹·I⁻¹`.
The Brillouin/Landauer/Bennett convention where `k_B` is the
conversion factor between dimensionless information `I` and
thermodynamic entropy `E·Θ⁻¹`. -/
def kB_dim_framework : Dimension LTMCTIDimensionBase := E𝓭 * Θ𝓭⁻¹ * I𝓭⁻¹


/-- **Null-convention Planckian period dimension**:
`[β_null] = [ℏ/(k_B·T)] = (E·T)/(E·Θ⁻¹·Θ) = T`. -/
def planckianPeriod_dim_null : Dimension LTMCTIDimensionBase := ℏ_dim / (kB_dim_null * Θ𝓭)

/-- **The null Planckian period is pure time** —
`[β_null] = T𝓭`. -/
lemma planckianPeriod_dim_null_eq_T :
    planckianPeriod_dim_null = T𝓭 := by
  unfold planckianPeriod_dim_null ℏ_dim kB_dim_null E𝓭
  ext b <;> cases b <;> simp <;>
    ring

/-- **Under the null, the Planckian period has zero
`I`-component** — information is dimensionally invisible. -/
lemma null_planckianPeriod_information_zero :
    planckianPeriod_dim_null.exponent .information = 0 := by
  rw [planckianPeriod_dim_null_eq_T]
  exact T𝓭_information


/-- **Framework-convention Planckian period dimension**:
`[β_framework] = [ℏ/(k_B·T)] = (E·T)/(E·Θ⁻¹·I⁻¹·Θ) = T·I`. -/
def planckianPeriod_dim_framework : Dimension LTMCTIDimensionBase :=
  ℏ_dim / (kB_dim_framework * Θ𝓭)

/-- **The framework Planckian period carries an
`I`-component** — `[β_framework] = T𝓭 · I𝓭`. -/
lemma planckianPeriod_dim_framework_eq_T_I :
    planckianPeriod_dim_framework = T𝓭 * I𝓭 := by
  unfold planckianPeriod_dim_framework ℏ_dim kB_dim_framework E𝓭
  ext b <;> cases b <;> simp <;>
    ring

/-- **The framework Planckian period has nonzero
`I`-component** — equal to 1. -/
lemma framework_planckianPeriod_information_one :
    planckianPeriod_dim_framework.exponent .information = 1 := by
  rw [planckianPeriod_dim_framework_eq_T_I]
  simp

/-- **The framework Planckian period has time-component 1**. -/
lemma framework_planckianPeriod_time_one :
    planckianPeriod_dim_framework.exponent .time = 1 := by
  rw [planckianPeriod_dim_framework_eq_T_I]
  simp


/-- **Dimensional discriminator** — the framework Planckian
period and the null Planckian period differ exactly by an
`I𝓭` factor.

This is the formal statement of the framework-vs-null
dimensional distinction: any empirical observable identified
with the Planckian period inherits an `I`-component under the
framework and not under the null.  An experimenter measuring
`τ_tr` and finding `τ_tr ≈ ℏ/(k_B·T)` cannot, on dimensional
grounds alone, decide which convention is correct.  But any
*theoretical* prediction for the O(1) prefactor must align
the `I`-content on both sides; a framework that ignores `[I]`
has nothing to constrain that prefactor with. -/
lemma planckianPeriod_dim_framework_eq_null_mul_I :
    planckianPeriod_dim_framework =
      planckianPeriod_dim_null * I𝓭 := by
  rw [planckianPeriod_dim_framework_eq_T_I,
      planckianPeriod_dim_null_eq_T]

/-- **The two conventions are inequivalent dimensional
algebras** — they assign different dimensions to the Planckian
period.

Specifically, `(framework β).exponent .information = 1` while
`(null β).exponent .information = 0`, so the two `Dimension LTMCTIDimensionBase` values are
distinct. -/
lemma planckianPeriod_dim_framework_ne_null :
    planckianPeriod_dim_framework ≠ planckianPeriod_dim_null := by
  intro h
  have h1 : planckianPeriod_dim_framework.exponent .information = 1 :=
    framework_planckianPeriod_information_one
  have h2 : planckianPeriod_dim_null.exponent .information = 0 :=
    null_planckianPeriod_information_zero
  rw [h] at h1
  rw [h2] at h1
  exact (one_ne_zero h1.symm).elim

/-!

`Physlib.Thermodynamics.SecondLaw.EntropyArrowWorldline` uses
the convention `τ_ent_along(t) := S_I_along(t) / ℏ` where
`S_I_along` is the **imaginary action** along the worldline
(Bender 2008).  In Bender's complex-action framing, `S_I` is
literally an action — it has dimension `[E·T]` — so `τ_ent`
is **dimensionless**: a unitless count of how many ℏ-quanta
of imaginary action have accumulated.

This is a different convention from the Brillouin/Landauer
`[S_Shannon] = I` reading: under Bender's framing the Lean
quantity `S_I_along` carries action dimension, with the
information content recovered as `S_I/(k_B·T)` (which has
dimension `I` under the framework convention). -/

/-- **Bender imaginary-action dimension**: `[S_I] = [E·T]`
(same as `ℏ`).  Bender 2008 framing. -/
def benderS_I_dim : Dimension LTMCTIDimensionBase := ℏ_dim

/-- **Bender entropic time is dimensionless** under the
Bender convention `S_I = imaginary action`, since
`[S_I/ℏ] = (E·T)/(E·T) = 1`. -/
lemma benderTauEnt_dim_dimensionless :
    benderS_I_dim / ℏ_dim = 1 := by
  unfold benderS_I_dim
  simp

/-- **Brillouin/Landauer entropy dimension**: `[S_Boltzmann] = I`
(dimensionless count of microstates).  This is a *different*
convention from Bender's `S_I = imaginary action`; the two
share the symbol `S` but track different physical quantities
(the Boltzmann S is a count; the Bender S_I is an action). -/
def brillouinS_dim : Dimension LTMCTIDimensionBase := I𝓭

/-- **Action-to-information ratio dimension**: dividing Bender's
`S_I` (action, dimension `E·T`) by `k_B·T` (energy per nat,
dimension `E·I⁻¹` in the framework convention) gives
dimension `[E·T] / [E·I⁻¹] = T·I`.

That is, the natural "framework-convention dimensionless count
of nats accumulated per ℏ-quantum" sits at dimension `T·I`,
matching the framework Planckian-period dimension exactly.
This is why the Bender `S_I/ℏ` interpretation and the
Brillouin Planckian-period interpretation are dimensionally
compatible under the framework. -/
lemma benderS_I_div_kT_dim_eq_T_mul_I :
    benderS_I_dim / (kB_dim_framework * Θ𝓭) = T𝓭 * I𝓭 := by
  unfold benderS_I_dim ℏ_dim kB_dim_framework E𝓭
  ext b <;> cases b <;> simp <;>
    ring

/-!

The Phase-E `Discriminator` module observed that the measured
Planckian ratios cluster in a narrow window across material
classes.  This module establishes that the framework's
prediction is **dimensionally non-trivial** — there is an
`I`-component to the Planckian period that the null does not
account for.  The empirical narrowness is then evidence for
that `I`-component existing in nature, not a coincidence of
microscopic details.

The two key theorems are:

* `planckianPeriod_dim_framework_eq_null_mul_I` —
  `[β]_framework = [β]_null · [I]`.  Under the framework
  convention, the Planckian period gains an `I`-component
  exactly.
* `benderS_I_div_kT_dim_eq_T_mul_I` —
  `[S_I/(k_B·T)]_framework = [T·I]`.  Bender's imaginary
  action divided by the framework-convention thermal energy
  also lands at dimension `T·I`, matching the framework
  Planckian period.  The two routes (Planckian via
  `{ℏ, k_B, T}` and Bender via `{S_I, k_B, T}`) are
  dimensionally consistent under the framework.

The honest reading: physlib's six-base `Dimension LTMCTIDimensionBase` framework
makes the framework-vs-null distinction algebraically explicit
and verifiable.  Whether *Nature* uses the framework convention
or the null convention is an empirical question that this
module does not resolve — it provides the typed scaffold that
makes the question precise. -/

/-! ### The interface basis is independent, so every conversion is unique -/

/-- Newton's constant as a dimension vector, `L³T⁻²M⁻¹`. -/
def G_dim : Dimension LTMCTIDimensionBase := L𝓭 ^ (3 : ℚ) * T𝓭 ^ (-2 : ℚ) * M𝓭⁻¹

/-- The speed of light as a dimension vector, `LT⁻¹`. -/
def c_dim : Dimension LTMCTIDimensionBase := L𝓭 * T𝓭⁻¹

/-- **The four interface constants are dimensionally independent.**  If a product
`ℏ^x k_B^y c^z G^w` is dimensionless then every exponent vanishes.

This is the uniqueness theorem behind the whole conversion layer.  `#zil_unify_mediator`
finds the object bridging two carriers by solving their dimensional defect over exactly this
basis; independence says that when such a solution exists it is **the only one**.  So the
mediating definitions the program discovered — the Compton temperature, the SI
Gibbons–Hawking temperature, the entropic potential scale — are not conventions chosen among
alternatives: each is the unique conversion between its two sectors.

The same fact fixes the information typing.  Since `k_B` is the only basis element carrying
temperature and the remaining three are independent across length, time and mass, an
assignment of information charge to the basis is determined by where a single nat is placed;
placing it on `G` (Newton's constant as area per bit) therefore fixes the charge of every
carrier expressible in the basis, with no freedom left over. -/
theorem interfaceConstants_independent (x y z w : ℚ)
    (h : ℏ_dim ^ x * kB_dim_framework ^ y * c_dim ^ z * G_dim ^ w = 1) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  have hL := congrArg (fun d => d.exponent .length) h
  have hT := congrArg (fun d => d.exponent .time) h
  have hM := congrArg (fun d => d.exponent .mass) h
  have hΘ := congrArg (fun d => d.exponent .temperature) h
  simp [ℏ_dim, kB_dim_framework, c_dim, G_dim, E𝓭, L𝓭, T𝓭, M𝓭, Θ𝓭, I𝓭] at hL hT hM hΘ
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDimension
