/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import QuantumInfo.Entropy.EntropicProperTime
public import Physlib.SpaceAndTime.SpaceTime.Lapse
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
public import Physlib.Units.Dimension
public import Physlib.Units.ComplexActionDimension
public import Physlib.SpaceAndTime.TolmanScaling

/-!

# Entropic proper time — dimensional lift and spacetime coupling

`QuantumInfo.Finite.entropicProperTime ρ σ = qRelativeEnt ρ σ` is a
dimensionless `ENNReal`. This module lifts it to a metric time via a
positive scale of dimension `T`,

The previous additive form `τ_total = τ_geom + D(ρ‖σ)` was dimensionally
inconsistent (a length/time added to a dimensionless number). The corrected
form is `τ_total = τ_geom + (ℏ/(k_B T_∞)) · D(ρ‖σ)`.

defines the metric **relative-entropy time** `(ℏ/(k_B T_∞)) · D(ρ‖σ)`,
and equips it with a `TolmanScaling`-style lapse redshift on a
`Lapse sd`. The combined observable

  `τ_total := τ_geom + (ℏ/(k_B T_∞)) · D(ρ‖σ)`

(`totalProperTimeMetric` below) is dimensionally consistent — both
summands include the dimension of time.

## Source and equation map

* H. Umegaki, *Conditional expectation in an operator algebra. IV. Entropy and information*,
  Kodai Mathematical Seminar Reports 14 (1962), 59-85, doi:10.2996/kmj/1138844604:
  finite quantum relative entropy `D(ρ‖σ) = Tr(ρ(log ρ - log σ))`.
* H. Araki, *Relative Entropy of States of von Neumann Algebras*, Publications of the
  Research Institute for Mathematical Sciences 11 (1976), 809-833,
  doi:10.2977/prims/1195191148: modular relative entropy and its finite-dimensional
  logarithmic specialization.
* A. Connes and C. Rovelli, *Von Neumann algebra automorphisms and time-thermodynamics
  relation in generally covariant quantum theories*, Classical and Quantum Gravity 11
  (1994), 2899-2918, doi:10.1088/0264-9381/11/12/007: thermal-time motivation via
  state-dependent modular flow. This module keeps the more modest finite-state scalar
  `D(ρ‖σ)` and does not assert a Tomita-Takesaki identification.
* R. C. Tolman, *On the Weight of Heat and Thermal Equilibrium in General Relativity*,
  Physical Review 35 (1930), 904-924, doi:10.1103/PhysRev.35.904; and R. C. Tolman
  with P. Ehrenfest, *Temperature Equilibrium in a Static Gravitational Field*, Physical
  Review 36 (1930), 1791-1798, doi:10.1103/PhysRev.36.1791: lapse-redshift law
  `O_loc(x) * N(x) = O_∞`.
* C. Rovelli and M. Smerlak, *Thermal time and Tolman-Ehrenfest effect: temperature as
  the speed of time*, Classical and Quantum Gravity 28 (2011), 075007,
  doi:10.1088/0264-9381/28/7/075007: thermal-time/Tolman relation used as motivation
  for redshifting clock rates.

The Lean statements correspond to these equations:

* `entropicGap ρ σ = (D(ρ‖σ)).toReal`;
* `entropicProperTimeMetric U ρ σ = (ℏ/(k_B T_∞)) * D(ρ‖σ)`;
* `totalProperTimeMetric = τ_geom + (ℏ/(k_B T_∞)) * D(ρ‖σ)`;
* `totalProperTimeMetric_at_frozen`: when `ρ = σ`, `D(ρ‖ρ)=0`, so the total time
  reduces to the geometric interval;
* `entropicProperTimeLocalMetric_tolman`: `τ_ent,loc(x) * N(x) = τ_ent,∞`.
* `entropicProperTime_no_scalar_complex_action_with_information`: a scalar complex action
  with dimensionless `i` cannot identify an informational imaginary part
  `E·T·I` with the mechanical action dimension `E·T`; the independent `[I]` axis is
  therefore part of the dimensional data, not optional decoration.
-/

@[expose] public section

noncomputable section

namespace QuantumInfo.Finite

open Physlib.SpaceTime Dimension Lorentz Vector Real

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {sd : ℕ}

/-! ## A. Unit data -/

/-- Physical unit data converting dimensionless relative entropy into a metric
time via the scale `ℏ / (k_B · T_∞)`. -/
structure EntropicTimeUnits where
  /-- Reduced Planck constant. -/
  hbar : ℝ
  /-- Boltzmann constant. -/
  kB : ℝ
  /-- Reference temperature. -/
  T_inf : ℝ
  /-- `ℏ > 0`. -/
  hbar_pos : 0 < hbar
  /-- `k_B > 0`. -/
  kB_pos : 0 < kB
  /-- `T_∞ > 0`. -/
  T_inf_pos : 0 < T_inf

namespace EntropicTimeUnits

/-- The time scale `ℏ / (k_B · T_∞)`. -/
def scale (U : EntropicTimeUnits) : ℝ :=
  U.hbar / (U.kB * U.T_inf)

/-- The time scale is strictly positive. -/
theorem scale_pos (U : EntropicTimeUnits) : 0 < U.scale := by
  unfold scale
  exact div_pos U.hbar_pos (mul_pos U.kB_pos U.T_inf_pos)

end EntropicTimeUnits

/-! ## B. Dimensionless gap and metric lift -/

/-- The dimensionless entropic gap `D(ρ‖σ)` as a real number. -/
def entropicGap (ρ σ : MState d) : ℝ :=
  (entropicProperTime ρ σ).toReal

@[simp] theorem entropicGap_self (ρ : MState d) :
    entropicGap ρ ρ = 0 := by
  unfold entropicGap
  rw [entropicProperTime_self]
  simp

theorem entropicGap_nonneg (ρ σ : MState d) :
    0 ≤ entropicGap ρ σ :=
  ENNReal.toReal_nonneg

/-- The **metric entropic proper time** `τ_ent := (ℏ/(k_B T_∞)) · D(ρ‖σ)`. -/
def entropicProperTimeMetric
    (U : EntropicTimeUnits) (ρ σ : MState d) : ℝ :=
  U.scale * entropicGap ρ σ

@[simp] theorem entropicProperTimeMetric_self
    (U : EntropicTimeUnits) (ρ : MState d) :
    entropicProperTimeMetric U ρ ρ = 0 := by
  unfold entropicProperTimeMetric
  rw [entropicGap_self]
  ring

/-- **Non-negativity of the metric entropic proper time**: a positive
scale times a non-negative `entropicGap` is non-negative.

Does not prove: discreteness of values; minimum nonzero step;
uniqueness of `τ_ent`; equality to physical proper time.
The same conclusion holds for `σ := ρ` (gap is `0`).
-/
theorem entropicProperTimeMetric_nonneg
    (U : EntropicTimeUnits) (ρ σ : MState d) :
    0 ≤ entropicProperTimeMetric U ρ σ := by
  unfold entropicProperTimeMetric
  exact mul_nonneg U.scale_pos.le (entropicGap_nonneg ρ σ)

/-! ## C. Geometric interval and total proper time -/

/-- The **geometric Minkowski interval** between events `q` and `p`:
`√⟪p−q, p−q⟫ₘ`. This is the bare geometric part of the total proper time;
in the entropic-time framework it is *not* the primitive but the frozen-LRF residue of
`totalProperTimeMetric`. Declared here so that `totalProperTimeMetric`
is self-contained; `Physlib.Relativity.Special.ProperTime` defines
`SpaceTime.properTime` as the frozen-extraction of `totalProperTimeMetric`
via this value. -/
def geometricInterval {sd : ℕ} (q p : SpaceTime sd) : ℝ :=
  √⟪p - q, p - q⟫ₘ

/-- **Total proper time** with the dimensionally-correct entropic lift:
`τ_total = τ_geom + (ℏ/(k_B T_∞)) · D(ρ‖σ)`.

In the entropic-time inversion this is the **primitive observable**; the
geometric Minkowski interval emerges as its frozen-LRF residue
(see `totalProperTimeMetric_at_frozen`). -/
def totalProperTimeMetric
    (U : EntropicTimeUnits)
    (q p : SpaceTime sd) (ρ σ : MState d) : ℝ :=
  geometricInterval q p + entropicProperTimeMetric U ρ σ

/-- At the Frozen-LRF (`ρ = σ`), the total proper time reduces to the
bare geometric Minkowski interval. **The entropic-time load-bearing claim**:
the geometric "proper time" is a side-effect of total proper time at
zero relative entropy. -/
theorem totalProperTimeMetric_at_frozen
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d) :
    totalProperTimeMetric U q p ρ ρ = geometricInterval q p := by
  unfold totalProperTimeMetric
  rw [entropicProperTimeMetric_self]
  ring

/-! ## D. Local lapse form (metric) -/

/-- **Local-frame metric entropic time** at event `x`, redshifted by the lapse:
`τ_ent_loc = τ_ent / N(x)`, built on the dimensionally-correct metric time. -/
def entropicProperTimeLocalMetric
    (U : EntropicTimeUnits) (L : Lapse sd) (ρ σ : MState d) (x : SpaceTime sd) : ℝ :=
  entropicProperTimeMetric U ρ σ / L.N x

/-- Local Tolman invariant: `τ_ent_loc(x) · N(x) = τ_ent`. -/
theorem entropicProperTimeLocalMetric_tolman
    (U : EntropicTimeUnits) (L : Lapse sd) (ρ σ : MState d) (x : SpaceTime sd) :
    entropicProperTimeLocalMetric U L ρ σ x * L.N x =
      entropicProperTimeMetric U ρ σ :=
  div_mul_cancel₀ _ (L.N_pos x).ne'

/-- Frozen-LRF: the local metric entropic time vanishes at every event. -/
@[simp] theorem entropicProperTimeLocalMetric_self
    (U : EntropicTimeUnits) (L : Lapse sd) (ρ : MState d) (x : SpaceTime sd) :
    entropicProperTimeLocalMetric U L ρ ρ x = 0 := by
  unfold entropicProperTimeLocalMetric
  rw [entropicProperTimeMetric_self]
  simp

/-- Unit-lapse limit: the local metric entropic time equals the asymptotic
metric entropic time. -/
theorem entropicProperTimeLocalMetric_unit_lapse
    (U : EntropicTimeUnits) (ρ σ : MState d) (x : SpaceTime sd) :
    entropicProperTimeLocalMetric U (Lapse.unit (d := sd)) ρ σ x =
      entropicProperTimeMetric U ρ σ := by
  unfold entropicProperTimeLocalMetric
  rw [Lapse.unit_N, div_one]

/-- **Metric entropic proper time as a Tolman-scaled observable** over a lapse:
the asymptotic value is `τ_ent = (ℏ/(k_B T_∞))·D(ρ‖σ)`, with the redshift law
held as a structure field rather than a hidden definition. -/
def entropicProperTimeTolmanScaling
    (U : EntropicTimeUnits) (L : Lapse sd) (ρ σ : MState d) : TolmanScaling sd where
  L := L
  asymptotic := entropicProperTimeMetric U ρ σ
  localValue := fun x => entropicProperTimeMetric U ρ σ / L.N x
  law := fun x => div_mul_cancel₀ _ (L.N_pos x).ne'

/-- The Tolman-instance local value is exactly `entropicProperTimeLocalMetric`. -/
@[simp] theorem entropicProperTimeTolmanScaling_localValue
    (U : EntropicTimeUnits) (L : Lapse sd) (ρ σ : MState d) (x : SpaceTime sd) :
    (entropicProperTimeTolmanScaling U L ρ σ).localValue x =
      entropicProperTimeLocalMetric U L ρ σ x :=
  rfl

/-- The local metric entropic time satisfies the Tolman invariant (named to
state the law explicitly). -/
theorem entropicProperTimeLocalMetric_satisfies_tolman
    (U : EntropicTimeUnits) (L : Lapse sd) (ρ σ : MState d) (x : SpaceTime sd) :
    entropicProperTimeLocalMetric U L ρ σ x * L.N x =
      entropicProperTimeMetric U ρ σ :=
  (entropicProperTimeTolmanScaling U L ρ σ).law x

/-! ## E. Complex proper time (metric) -/

/-- **Complex proper time**: real part the geometric Minkowski interval,
imaginary part the dimensionally-scaled metric entropic proper time. -/
def complexProperTimeMetric
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ σ : MState d) : ℂ :=
  ⟨geometricInterval q p, entropicProperTimeMetric U ρ σ⟩

theorem complexProperTimeMetric_at_frozen
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ : MState d) :
    complexProperTimeMetric U q p ρ ρ = (geometricInterval q p : ℂ) := by
  apply Complex.ext
  · show geometricInterval q p = geometricInterval q p; rfl
  · show entropicProperTimeMetric U ρ ρ = 0
    rw [entropicProperTimeMetric_self]

@[simp] theorem complexProperTimeMetric_re
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ σ : MState d) :
    (complexProperTimeMetric U q p ρ σ).re = geometricInterval q p := rfl

@[simp] theorem complexProperTimeMetric_im
    (U : EntropicTimeUnits) (q p : SpaceTime sd) (ρ σ : MState d) :
    (complexProperTimeMetric U q p ρ σ).im = entropicProperTimeMetric U ρ σ := rfl

/-! ## F. Dimensional tag -/

/-- **No-go link to the unit layer.** A scalar complex action with dimensionless `i`
cannot absorb an informational imaginary part into the mechanical action dimension:
`[i] = 1` and `[i*S_I] = E*T` force `[S_I] = E*T`, not `E*T*I`.
Thus the entropic-time scale relies on the independent information axis `[I]` already
installed in `Dimension`. -/
theorem entropicProperTime_no_scalar_complex_action_with_information :
    ¬ ∃ imag : Dimension, imag * imag = 1 ∧
      imag * (Physlib.Units.InformationDimensionCollision.energy_dim * T𝓭 * I𝓭) =
        Physlib.Units.InformationDimensionCollision.energy_dim * T𝓭 :=
  Physlib.Units.ComplexActionDimension.scalar_no_informational_imaginary

/-- The entropic time scale `ℏ/(k_B T_∞)` includes the dimension of **time**:
`[ℏ/(k_B T_∞)] = (M·L²·T⁻¹)/((M·L²·T⁻²·Θ⁻¹)·Θ) = T`. -/
theorem entropicTimeScale_dimension :
    (M𝓭 * L𝓭 ^ (2 : ℚ) * T𝓭 ^ (-1 : ℚ))
        / ((M𝓭 * L𝓭 ^ (2 : ℚ) * T𝓭 ^ (-2 : ℚ) * Θ𝓭 ^ (-1 : ℚ)) * Θ𝓭)
      = T𝓭 := by
  ext
  all_goals simp <;> ring_nf

end QuantumInfo.Finite

end
