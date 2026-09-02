/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.ClassicalMechanics.HerglotzLazoContact
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

meta import Zil

/-!
# Herglotz-type action-dependent gravity

Wazny–Csillag–Pinto–Harko, *Herglotz-type f(R,T) gravity* (arXiv:2511.16304): the
gravitational action is made to depend on its own accumulated value, so the Herglotz
variational principle replaces Hamilton's.  Two sections:

* `FieldEquations` — the covariant field equations carrying the Herglotz tensor
  `H_{μν}` at general `f`, their reductions to `f(R,T)`, Lazo and Einstein gravity, the
  trace and traceless forms, and the balance current, with conservation holding exactly
  when the Herglotz tensor is divergence-free.
* `OrbitTests` — the orbital consequences: the exact apsidal advance with Einstein's
  coefficient as its derivative at zero, restated through the Planck and Compton
  lengths and the holographic bit count; the Herglotz extra advance with its two-orbit
  exclusion; light deflection and the chromatic Herglotz correction.

The mechanics beneath is `ClassicalMechanics.HerglotzLazoContact`; the cosmological
face is the Herglotz section of `Cosmology.FLRW.Dynamics`.
-/

@[expose] public section

noncomputable section

namespace Relativity.SemiClassical.HerglotzGravity

section FieldEquations

/-!
# The covariant field equations of Herglotz-type `f(R,T)` gravity

Wazny–Csillag–Pinto–Harko (arXiv:2511.16304), §3: varying
`𝓛 = f(R,T) + λ_μ s^μ + F·𝓛_m` under the Herglotz principle gives

  `f_R·R_μν − ½f·g_μν + (g_μν□ − ∇_μ∇_ν)f_R + H_μν
      = (F/2)·T_μν − f_T·(T_μν + Θ_μν)`,

with `H_μν` the Herglotz tensor built from the one-form `λ_μ`.  This module carries the
system at the level the repository's field-equation modules use: the equation as a
pointwise proposition over supplied tensor data, with the derivative-built objects
(`∇_μ∇_ν f_R`, `□f_R`, `H_μν`, `Θ_μν`) entering as data.  The theorems are the paper's
exact algebraic content:

* the three reductions of the paper's remarks — standard `f(R,T)` at vanishing Herglotz
  field, Lazo's nonconservative gravity at `f = R`, and **the Einstein equation** at
  both (`einstein_reduction`, meeting the Clausius route
  `einstein_from_clausius` from the thermodynamic side);
* the **trace equation** (paper Eq. 40): contracting with the inverse metric under the
  natural trace data (`tr g = 4`, `tr Ric = R`, `tr ∇∇f_R = □f_R`) gives
  `f_R·R − 2f + 3□f_R + H = (F/2)T − f_T(T + Θ)` (`trace_equation`);
* the **traceless form** (paper Eq. 41), derived from the field equation and its trace
  by an exact linear combination (`traceless_form`) — the form whose `00`-component
  drives the paper's Newtonian limit and hence the perihelion and deflection results of
  the `OrbitTests` section below.

**Honest layering.**  Formalized: the field-equation system and its algebraic
consequences with derivative-built tensors as data; the balance current `J_ν` and the
conservation constraint (§C), with the covariant divergence entering as a linear-map
datum carrying the Bianchi and Leibniz properties — the same apparatus as
`einstein_from_clausius_with_local_cosmological_constancy`; and the weighted-variation
integrating factor of the Herglotz `δ`-calculus
(`ClassicalMechanics.weighted_variation_deriv`).  Not formalized: the full
field-theoretic `e^{−φ}√−g` variation (the repository's variational-derivative
framework `HasVarGradient`, used by the electromagnetic Lagrangian modules, is the
natural carrier for it), and non-constant couplings in the balance.  The cosmological
reduction of this system at `f = R` is `Cosmology.FLRW.Dynamics`; the
mechanics beneath is `ClassicalMechanics.HerglotzLazoContact`.
-/

/-- **The data of Herglotz-type `f(R,T)` gravity at a point**: metric, inverse metric,
Ricci tensor, stress tensor, the variation tensor `Θ_μν`, the Herglotz tensor `H_μν`,
the Hessian `∇_μ∇_ν f_R`, and the scalars `R, f, f_R, f_T, F, □f_R`.  Derivative-built
objects enter as data, as in the repository's other field-equation modules. -/
structure HerglotzFRTData (ι : Type*) [Fintype ι] where
  /-- The metric `g_μν`. -/
  g : ι → ι → ℝ
  /-- The inverse metric `g^μν`, used for traces. -/
  gInv : ι → ι → ℝ
  /-- The Ricci tensor `R_μν`. -/
  Ric : ι → ι → ℝ
  /-- The matter stress tensor `T_μν`. -/
  T : ι → ι → ℝ
  /-- The variation tensor `Θ_μν = g^{αβ}δT_{αβ}/δg^{μν}`. -/
  Θ : ι → ι → ℝ
  /-- The Herglotz tensor `H_μν`, built from the one-form `λ_μ`. -/
  H : ι → ι → ℝ
  /-- The Hessian `∇_μ∇_ν f_R`. -/
  ddfR : ι → ι → ℝ
  /-- The Ricci scalar `R`. -/
  R : ℝ
  /-- The value `f(R,T)`. -/
  f : ℝ
  /-- The partial `f_R`. -/
  fR : ℝ
  /-- The partial `f_T`. -/
  fT : ℝ
  /-- The matter coupling `F`. -/
  F : ℝ
  /-- The box `□f_R = g^{μν}∇_μ∇_ν f_R`. -/
  boxfR : ℝ

namespace HerglotzFRTData

variable {ι : Type*} [Fintype ι] (D : HerglotzFRTData ι)

/-- The `g`-trace of a two-index object: `tr X = Σ g^{μν} X_{μν}`. -/
def gTrace (X : ι → ι → ℝ) : ℝ := ∑ μ, ∑ ν, D.gInv μ ν * X μ ν

/-- **The covariant field equation of Herglotz-type `f(R,T)` gravity**
(paper Eq. 38):

  `f_R·R_μν − ½f·g_μν + (g_μν·□f_R − ∇_μ∇_ν f_R) + H_μν
      = (F/2)T_μν − f_T(T_μν + Θ_μν)`. -/
def FieldEquation : Prop := ∀ μ ν,
  D.fR * D.Ric μ ν - (1 / 2) * D.f * D.g μ ν
      + (D.g μ ν * D.boxfR - D.ddfR μ ν) + D.H μ ν
    = (D.F / 2) * D.T μ ν - D.fT * (D.T μ ν + D.Θ μ ν)

/-- **Remark 1 — standard `f(R,T)` gravity at vanishing Herglotz field**: with
`H_μν = 0` the system is Harko's `f(R,T)` field equation. -/
theorem frt_reduction (hH : ∀ μ ν, D.H μ ν = 0) :
    D.FieldEquation ↔ ∀ μ ν,
      D.fR * D.Ric μ ν - (1 / 2) * D.f * D.g μ ν
          + (D.g μ ν * D.boxfR - D.ddfR μ ν)
        = (D.F / 2) * D.T μ ν - D.fT * (D.T μ ν + D.Θ μ ν) := by
  unfold FieldEquation
  constructor <;> intro h μ ν <;> have h' := h μ ν <;> rw [hH μ ν] at * <;> linarith [h']

/-- **Remark 2 — Lazo's nonconservative gravity at `f = R`**: with `f = R`, `f_R = 1`
(so the Hessian and box vanish), and `f_T = 0`, `F = 16π`, the system is
`R_μν − ½R·g_μν + H_μν = 8π·T_μν`. -/
theorem lazo_reduction (hf : D.f = D.R) (hfR : D.fR = 1) (hfT : D.fT = 0)
    (hF : D.F = 16 * Real.pi) (hdd : ∀ μ ν, D.ddfR μ ν = 0) (hbox : D.boxfR = 0) :
    D.FieldEquation ↔ ∀ μ ν,
      D.Ric μ ν - (1 / 2) * D.R * D.g μ ν + D.H μ ν
        = 8 * Real.pi * D.T μ ν := by
  unfold FieldEquation
  constructor <;> intro h μ ν <;> have h' := h μ ν <;>
    rw [hf, hfR, hfT, hF, hdd μ ν, hbox] at * <;> linarith [h']

/-- **Remark 3 — the Einstein equation**: at vanishing Herglotz field, `f = R`, and
`F = 16π`, the system is `R_μν − ½R·g_μν = 8π·T_μν` — the same equation the
thermodynamic route reaches through the Clausius derivation
(`einstein_from_clausius`); the dissipative variational route and the entropic route
meet at the same field equation. -/
theorem einstein_reduction (hf : D.f = D.R) (hfR : D.fR = 1) (hfT : D.fT = 0)
    (hF : D.F = 16 * Real.pi) (hdd : ∀ μ ν, D.ddfR μ ν = 0) (hbox : D.boxfR = 0)
    (hH : ∀ μ ν, D.H μ ν = 0) :
    D.FieldEquation ↔ ∀ μ ν,
      D.Ric μ ν - (1 / 2) * D.R * D.g μ ν = 8 * Real.pi * D.T μ ν := by
  rw [D.lazo_reduction hf hfR hfT hF hdd hbox]
  constructor <;> intro h μ ν <;> have h' := h μ ν <;> rw [hH μ ν] at * <;>
    linarith [h']

/-- **The trace equation** (paper Eq. 40): contracting the field equation with the
inverse metric, under the natural trace data (`tr g = 4`, `tr Ric = R`,
`tr ∇∇f_R = □f_R`),

  `f_R·R − 2f + 3·□f_R + H = (F/2)·T − f_T·(T + Θ)`

with `H, T, Θ` the traces. -/
theorem trace_equation (hEq : D.FieldEquation) (htrg : D.gTrace D.g = 4)
    (htrRic : D.gTrace D.Ric = D.R) (htrdd : D.gTrace D.ddfR = D.boxfR) :
    D.fR * D.R - 2 * D.f + 3 * D.boxfR + D.gTrace D.H
      = (D.F / 2) * D.gTrace D.T - D.fT * (D.gTrace D.T + D.gTrace D.Θ) := by
  have hsum : (∑ μ, ∑ ν, D.gInv μ ν *
      (D.fR * D.Ric μ ν - (1 / 2) * D.f * D.g μ ν
        + (D.g μ ν * D.boxfR - D.ddfR μ ν) + D.H μ ν))
      = ∑ μ, ∑ ν, D.gInv μ ν *
        ((D.F / 2) * D.T μ ν - D.fT * (D.T μ ν + D.Θ μ ν)) :=
    Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by rw [hEq μ ν]
  have hL : (∑ μ, ∑ ν, D.gInv μ ν *
      (D.fR * D.Ric μ ν - (1 / 2) * D.f * D.g μ ν
        + (D.g μ ν * D.boxfR - D.ddfR μ ν) + D.H μ ν))
      = D.fR * D.gTrace D.Ric - (1 / 2) * D.f * D.gTrace D.g
        + D.boxfR * D.gTrace D.g - D.gTrace D.ddfR + D.gTrace D.H := by
    unfold gTrace
    calc (∑ μ, ∑ ν, D.gInv μ ν *
        (D.fR * D.Ric μ ν - (1 / 2) * D.f * D.g μ ν
          + (D.g μ ν * D.boxfR - D.ddfR μ ν) + D.H μ ν))
        = ∑ μ, ∑ ν, (D.fR * (D.gInv μ ν * D.Ric μ ν)
            - (1 / 2) * D.f * (D.gInv μ ν * D.g μ ν)
            + D.boxfR * (D.gInv μ ν * D.g μ ν)
            - D.gInv μ ν * D.ddfR μ ν + D.gInv μ ν * D.H μ ν) :=
          Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
      _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hR : (∑ μ, ∑ ν, D.gInv μ ν *
      ((D.F / 2) * D.T μ ν - D.fT * (D.T μ ν + D.Θ μ ν)))
      = (D.F / 2) * D.gTrace D.T - D.fT * (D.gTrace D.T + D.gTrace D.Θ) := by
    unfold gTrace
    calc (∑ μ, ∑ ν, D.gInv μ ν *
        ((D.F / 2) * D.T μ ν - D.fT * (D.T μ ν + D.Θ μ ν)))
        = ∑ μ, ∑ ν, ((D.F / 2) * (D.gInv μ ν * D.T μ ν)
            - D.fT * (D.gInv μ ν * D.T μ ν)
            - D.fT * (D.gInv μ ν * D.Θ μ ν)) :=
          Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring
      _ = _ := by
          simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring
  rw [hL, hR, htrg, htrRic, htrdd] at hsum
  linarith [hsum]

/-- **The traceless form** (paper Eq. 41): the field equation minus a quarter of its
trace times the metric — the form whose `00`-component drives the Newtonian limit,
hence the perihelion and light-deflection results.  Derived from the field equation and
the trace equation by an exact pointwise linear combination. -/
theorem traceless_form (hEq : D.FieldEquation) (htrg : D.gTrace D.g = 4)
    (htrRic : D.gTrace D.Ric = D.R) (htrdd : D.gTrace D.ddfR = D.boxfR) :
    ∀ μ ν,
      D.fR * (D.Ric μ ν - (1 / 4) * D.R * D.g μ ν)
          + ((1 / 4) * D.g μ ν * D.boxfR - D.ddfR μ ν)
          + (D.H μ ν - (1 / 4) * D.gTrace D.H * D.g μ ν)
        = (D.F / 2) * (D.T μ ν - (1 / 4) * D.gTrace D.T * D.g μ ν)
          - D.fT * ((D.T μ ν + D.Θ μ ν)
              - (1 / 4) * (D.gTrace D.T + D.gTrace D.Θ) * D.g μ ν) := by
  intro μ ν
  have htr := D.trace_equation hEq htrg htrRic htrdd
  linear_combination hEq μ ν - (D.g μ ν / 4) * htr

end HerglotzFRTData

/-! ### §C — the balance current: the divergence of the field equation

The covariant divergence enters as a linear-map datum with the Bianchi and Leibniz
properties as hypotheses — the same apparatus
`einstein_from_clausius_with_local_cosmological_constancy` uses.  At constant
couplings (the regime of the paper's Newtonian limit and linear cosmological model),
applying the divergence to the field equation yields the paper's balance (Eq. 47):

  `(F/2 + f_T)·∇^μT_μν = ∇^μH_μν − ½f_T·∇_νT + f_T·∇^μΞ_μν`,

with `Ξ` the matter-Lagrangian remainder of `Θ = −2T + Ξ`.  Conservation of the
energy–momentum tensor is then *equivalent* to the Herglotz tensor being
divergence-free when `f_T = 0` — the paper's constraint on the Herglotz field. -/

/-- **The balance current** (paper Eq. 47 at constant couplings): applying a
divergence operator with the contracted-Bianchi property (`∇^μR_μν = ½∇_νR`), the
metric Leibniz rule, and the chain rule for `f(R,T)` to the constant-`f_R` field
equation gives

  `(F/2 + f_T)·(Div T) = Div H − ½f_T·gradT + f_T·(Div Ξ)`.

The energy–momentum tensor fails to be conserved by exactly the Herglotz drain and the
matter-coupling terms. -/
theorem balance_current {ι : Type*} [Fintype ι]
    (Div : (ι → ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (Ric T Θ Ξ H g : ι → ι → ℝ) (gradR gradT gradf : ι → ℝ)
    (fR fT F f : ℝ)
    (hFieldEq : (fun μ ν => fR * Ric μ ν - (1 / 2) * (f * g μ ν) + H μ ν)
      = fun μ ν => (F / 2) * T μ ν - fT * (T μ ν + Θ μ ν))
    (hDivRic : Div Ric = (1 / 2 : ℝ) • gradR)
    (hDivfg : Div (fun μ ν => f * g μ ν) = gradf)
    (hgradf : gradf = fR • gradR + fT • gradT)
    (hΘ : Θ = fun μ ν => -2 * T μ ν + Ξ μ ν) :
    (F / 2 + fT) • Div T
      = Div H - ((1 / 2) * fT) • gradT + fT • Div Ξ := by
  have hEq' : fR • Ric - (1 / 2 : ℝ) • (fun μ ν => f * g μ ν) + H
      = (F / 2) • T - fT • T - fT • Θ := by
    funext μ ν
    have h := congrFun (congrFun hFieldEq μ) ν
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
    linarith [h]
  have hD := congrArg Div hEq'
  simp only [map_add, map_sub, map_smul] at hD
  rw [hDivRic, hDivfg, hgradf] at hD
  have hΘfun : Θ = (-2 : ℝ) • T + Ξ := by
    rw [hΘ]
    funext μ ν
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hΘfun, map_add, map_smul] at hD
  linear_combination (norm := module) -hD

/-- **Conservation is equivalent to a divergence-free Herglotz tensor** at `f_T = 0`
(paper's conservation constraint): given the balance, `Div T = 0 ↔ Div H = 0`. -/
theorem conservation_iff_herglotz_divergence_free {ι : Type*} [Fintype ι]
    (DivT DivH : ι → ℝ) (F : ℝ) (hF : F ≠ 0)
    (hbal : (F / 2) • DivT = DivH) :
    DivT = 0 ↔ DivH = 0 := by
  constructor
  · intro h
    rw [h, smul_zero] at hbal
    exact hbal.symm
  · intro h
    rw [h] at hbal
    have hF2 : (F / 2 : ℝ) ≠ 0 := by
      intro h0
      exact hF (by linarith [h0])
    exact (smul_eq_zero.mp hbal).resolve_left hF2

end FieldEquations

section OrbitTests

/-!
# The perihelion advance through the zero-point length

Einstein's Mercury result: the relativistic orbit's radial oscillation runs slightly
slower than its angular revolution, so the perihelion advances by
`δφ ≈ 6πGM/(c²p)` per orbit (`p` the semi-latus rectum).  This module carries the
calculational core and its holographic re-expression.

* **§A — the radial oscillator and the exact advance.**  The linearized radial equation
  around the circular orbit is a harmonic oscillator with squared frequency `1 − ε`;
  `orbitOscillator_solution` verifies the closed-form solution, and the apsidal advance
  per revolution is the exact `Δφ(ε) = 2π/√(1−ε) − 2π` (`apsidalAdvance`).  Einstein
  kept the first order; here the closed form carries all orders of the small-oscillation
  step, and `apsidalAdvance_hasDerivAt_zero` shows **Einstein's coefficient is the
  derivative at zero**: `Δφ′(0) = π`, so `δφ ≈ π·ε`.
* **§B — the parameter and its faces.**  `einsteinPrecessionParameter = 6G²M²/(c²h²)`;
  it equals `6·λ_g/p` with `λ_g = GM/c²` the gravitational length
  (`einsteinParameter_eq_grav_over_latus`), and through the zero-point identity
  `λ_C·λ_g = ℓ_P²` (`compton_grav_product_eq_planckSq`) it becomes

  `ε = 6·ℓ_P²/(λ_C(M)·p)`

  (`einsteinParameter_planck_compton`) — **the Mercury advance measures the Planck area
  against the source's Compton wavelength times the orbit size**.  In the nat ladder
  this is the `−1`-nat rung read as twice the `−½`-rung minus the `0`-rung.  The bit
  face (`einsteinParameter_bitCount`): with the orbit screen Planck-tiled,
  `ε = 24π·(p/λ_C)/N` — a ratio of two counts, the orbit size in source-Compton units
  over the screen's bit count, the same bookkeeping as
  `inverseSquare_R_only_through_bits`.

**Honest layering, with its search.**  Formalized: the oscillator solution, the exact
advance and its linearization derivative, and the parameter identities.  Not
formalized: the Schwarzschild geodesic equation and the relativistic Binet equation
`u″ + u = GM/h² + 3GMu²/c²` whose circular-orbit linearization *supplies* `ε = 6G²M²/(c²h²)`
— searched (`perihelion`/`binet`/`geodesic orbit`): the repository has no orbit
mechanics; the closest holographic route is statements 17–18 of the relational ledger
(Komar screen energy and the Clausius derivation of the Einstein equation,
`einstein_from_clausius`), which take screen thermodynamics to the field equation but
not yet from the field equation to geodesics.  The elliptic-integral exact advance
beyond the small-oscillation step is likewise open.  Same number as Einstein where the
chains meet; the additions are the all-orders closed form of the oscillation step and
the zero-point/bit re-expression of the parameter.
-/

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity

/-! ### §A — the radial oscillator and the exact advance -/

/-- **The linearized radial orbit equation has the shifted-oscillator closed form**:
`u(φ) = K/(1−ε) + A·cos(√(1−ε)·φ)` satisfies `u″ + (1−ε)u = K`.  The angular period of
the radial oscillation is `2π/√(1−ε)` — longer than the revolution's `2π`, which is the
perihelion advance. -/
theorem orbitOscillator_solution (K A ε φ : ℝ) (hε : ε < 1) :
    deriv (deriv (fun x => K / (1 - ε) + A * Real.cos (Real.sqrt (1 - ε) * x))) φ
        + (1 - ε) * (K / (1 - ε) + A * Real.cos (Real.sqrt (1 - ε) * φ)) = K := by
  set ω := Real.sqrt (1 - ε) with hω
  have hω2 : ω ^ 2 = 1 - ε := Real.sq_sqrt (by linarith)
  have hlin : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ω * y) ω x := fun x => by
    simpa using (hasDerivAt_id x).const_mul ω
  have h1 : ∀ x : ℝ, HasDerivAt (fun y => K / (1 - ε) + A * Real.cos (ω * y))
      (-(A * ω) * Real.sin (ω * x)) x := by
    intro x
    have h := (((Real.hasDerivAt_cos (ω * x)).comp x (hlin x)).const_mul A).const_add
      (K / (1 - ε))
    refine h.congr_deriv ?_
    ring
  have h2 : ∀ x : ℝ, HasDerivAt (fun y => -(A * ω) * Real.sin (ω * y))
      (-(A * ω ^ 2) * Real.cos (ω * x)) x := by
    intro x
    have h := ((Real.hasDerivAt_sin (ω * x)).comp x (hlin x)).const_mul (-(A * ω))
    refine h.congr_deriv ?_
    ring
  have hdf : deriv (fun x => K / (1 - ε) + A * Real.cos (ω * x))
      = fun x => -(A * ω) * Real.sin (ω * x) := funext fun x => (h1 x).deriv
  rw [hdf, (h2 φ).deriv, hω2]
  have hne : (1 : ℝ) - ε ≠ 0 := by linarith
  field_simp
  try ring

/-- **The apsidal advance per revolution, exact in the oscillation step**:
`Δφ(ε) = 2π/√(1−ε) − 2π`. -/
def apsidalAdvance (ε : ℝ) : ℝ := 2 * Real.pi / Real.sqrt (1 - ε) - 2 * Real.pi

/-- **Einstein's coefficient is the derivative at zero**: `Δφ′(0) = π`, so the
first-order advance is `π·ε` — with `ε = 6G²M²/(c²h²)` this is Einstein's
`δφ = 6πGM/(c²p)`.  The closed form carries every higher order of the oscillation
step; Einstein's 1915 computation is its linearization. -/
theorem apsidalAdvance_hasDerivAt_zero : HasDerivAt apsidalAdvance Real.pi 0 := by
  have hinner : HasDerivAt (fun ε : ℝ => 1 - ε) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hs := (Real.hasDerivAt_sqrt (by norm_num : (1 : ℝ) - 0 ≠ 0)).comp 0 hinner
  have hne : Real.sqrt (1 - (0 : ℝ)) ≠ 0 := by
    rw [show (1 : ℝ) - 0 = 1 from by ring, Real.sqrt_one]
    norm_num
  have hinv := hs.inv hne
  have h := (hinv.const_mul (2 * Real.pi)).sub_const (2 * Real.pi)
  unfold apsidalAdvance
  have hfun : (fun ε : ℝ => 2 * Real.pi * (Real.sqrt (1 - ε))⁻¹ - 2 * Real.pi)
      = fun ε : ℝ => 2 * Real.pi / Real.sqrt (1 - ε) - 2 * Real.pi := by
    funext ε
    rw [div_eq_mul_inv]
  rw [← hfun]
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [show (1 : ℝ) - 0 = 1 from by ring, Real.sqrt_one]
  ring

/-! ### §B — Einstein's parameter and its zero-point and bit faces -/

/-- **Einstein's precession parameter** `ε = 6G²M²/(c²h²)`, `h` the specific angular
momentum of the orbit. -/
def einsteinPrecessionParameter (G M c h : ℝ) : ℝ :=
  6 * G ^ 2 * M ^ 2 / (c ^ 2 * h ^ 2)

/-- **The parameter is six gravitational lengths per semi-latus rectum**:
`ε = 6·λ_g/p` with `λ_g = GM/c²` and `p = h²/(GM)`. -/
theorem einsteinParameter_eq_grav_over_latus (G M c h : ℝ)
    (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) (hh : h ≠ 0) :
    einsteinPrecessionParameter G M c h
      = 6 * gravitationalLength M G c / (h ^ 2 / (G * M)) := by
  unfold einsteinPrecessionParameter gravitationalLength
  field_simp
  try ring

/-- **The Mercury parameter through the zero-point length**: using
`λ_C·λ_g = ℓ_P²` (`compton_grav_product_eq_planckSq`),

  `ε = 6·ℓ_P²/(λ_C(M)·p)`

— the perihelion advance measures the Planck area against the source's Compton
wavelength times the orbit's semi-latus rectum.  Einstein's `6πGM/(c²p)` is
`6π·ℓ_P²/(λ_C·p)`: a purely quantum–informational reading of a classical orbit
number. -/
theorem einsteinParameter_planck_compton (G M c h ħ : ℝ)
    (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) (hh : h ≠ 0) (hħ : ħ ≠ 0) :
    einsteinPrecessionParameter G M c h
      = 6 * planckLengthSq G ħ c
          / (comptonWavelength M c ħ * (h ^ 2 / (G * M))) := by
  unfold einsteinPrecessionParameter planckLengthSq comptonWavelength
  field_simp
  try ring

/-- **The bit face of the parameter**: Planck-tiling the orbit screen
(`N = 4πp²/ℓ_P²`) gives

  `ε = 24π·(p/λ_C)/N`

— a ratio of two counts: the orbit size in source-Compton units over the screen's bit
count.  The same bookkeeping by which distance enters the inverse-square law only
through bits carries the relativistic correction too. -/
theorem einsteinParameter_bitCount (G M c ħ p : ℝ)
    (hG : G ≠ 0) (hM : M ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hp : p ≠ 0) :
    6 * planckLengthSq G ħ c / (comptonWavelength M c ħ * p)
      = 24 * Real.pi * (p / comptonWavelength M c ħ)
          / (4 * Real.pi * p ^ 2 / planckLengthSq G ħ c) := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold planckLengthSq comptonWavelength
  field_simp
  try ring

/-! ### §C — the Herglotz extension: dissipative gravity's exact extra advance

Wazny–Csillag–Pinto–Harko, *Herglotz-type `f(R,T)` gravity* (arXiv:2511.16304): the
non-conservation of the energy–momentum tensor in `f(R,T)` gravity read as dissipation,
by formulating the theory through the Herglotz action-dependent variational principle.
The mechanics underneath is the repository's own carrier: the Herglotz–Lazo contact
slice `L_eff = L_R − ρ·s` (`ClassicalMechanics.HerglotzContactSlice`), whose damped
oscillator (`dampedOscillatorContactSlice`) is the paper's Eq. (13) example.  In the
Newtonian limit the paper's Herglotz vector `ψ = 3ψ₀/2r²` corrects the potential to
`Φ = −GM/r + GMψ₀/2r² − …`, and the Laplace–Runge–Lenz integral of the extra
acceleration gives the exact extra apsidal advance per orbit,

  `Δφ_E = π(ψ₀/p)² − π(ψ₀/p)`,

formalized below from the trigonometric power integrals.  Beyond the paper's
single-planet bound, the closed form yields an exclusion the paper does not state: the
extra advance vanishes only at `ψ₀ = 0` or at the single orbit `p = ψ₀`, so **two
orbits of different size with no anomalous advance force `ψ₀ = 0` exactly**
(`herglotz_two_orbit_exclusion`). -/

/-- `∫₀^{2π} (α·cosθ + β·cos²θ + γ·cos³θ) dθ = β·π` — odd cosine powers average out
over a revolution; the square leaves `π`. -/
theorem cos_polynomial_integral (α β γ : ℝ) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        (α * Real.cos θ + β * Real.cos θ ^ 2 + γ * Real.cos θ ^ 3))
      = β * Real.pi := by
  have hFTC : ∀ θ : ℝ, HasDerivAt
      (fun x => α * Real.sin x + β * (x / 2 + Real.sin (2 * x) / 4)
        + γ * (Real.sin x - Real.sin x ^ 3 / 3))
      (α * Real.cos θ + β * Real.cos θ ^ 2 + γ * Real.cos θ ^ 3) θ := by
    intro θ
    have hsin : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    have h2x : HasDerivAt (fun x : ℝ => Real.sin (2 * x))
        (Real.cos (2 * θ) * 2) θ := (Real.hasDerivAt_sin (2 * θ)).comp θ hlin
    have hsin3 : HasDerivAt (fun x : ℝ => Real.sin x ^ 3)
        (3 * Real.sin θ ^ 2 * Real.cos θ) θ := by
      have h := (Real.hasDerivAt_sin θ).pow 3
      refine h.congr_deriv ?_
      push_cast
      ring
    have h := ((hsin.const_mul α).add
      ((((hasDerivAt_id θ).div_const 2).add (h2x.div_const 4)).const_mul β)).add
      ((hsin.sub (hsin3.div_const 3)).const_mul γ)
    refine h.congr_deriv ?_
    rw [Real.cos_two_mul, Real.sin_sq]
    ring
  have hcont : Continuous fun θ : ℝ =>
      α * Real.cos θ + β * Real.cos θ ^ 2 + γ * Real.cos θ ^ 3 := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hFTC θ) (hcont.intervalIntegrable _ _)]
  have h4π : Real.sin (2 * (2 * Real.pi)) = 0 := by
    rw [show 2 * (2 * Real.pi) = 2 * Real.pi + 2 * Real.pi from by ring,
      Real.sin_add, Real.sin_two_pi, Real.cos_two_pi]
    ring
  rw [Real.sin_two_pi, h4π]
  simp
  try ring

/-- **The Herglotz extra advance, exactly** (arXiv:2511.16304, the perihelion
integral): the Laplace–Runge–Lenz integral of the extra acceleration over one
revolution evaluates in closed form to

  `Δφ_E = π·ψ₀²·(GM/L²)² − π·ψ₀·(GM/L²) = π(ψ₀/p)² − π(ψ₀/p)`,

with `p = L²/GM` the semi-latus rectum. -/
theorem herglotzAdvance_integral (GM A L ψ₀ : ℝ) (hA : A ≠ 0) (hL : L ≠ 0) :
    (GM * ψ₀ / A) * ∫ θ in (0:ℝ)..(2 * Real.pi),
        (((ψ₀ / (2 * L ^ 4)) * (GM + A * Real.cos θ) ^ 2
          - (1 / L ^ 2) * (GM + A * Real.cos θ)) * Real.cos θ)
      = Real.pi * ψ₀ ^ 2 * (GM / L ^ 2) ^ 2 - Real.pi * ψ₀ * (GM / L ^ 2) := by
  have hfun : (fun θ : ℝ => ((ψ₀ / (2 * L ^ 4)) * (GM + A * Real.cos θ) ^ 2
      - (1 / L ^ 2) * (GM + A * Real.cos θ)) * Real.cos θ)
      = fun θ : ℝ =>
        (ψ₀ * GM ^ 2 / (2 * L ^ 4) - GM / L ^ 2) * Real.cos θ
        + (ψ₀ * GM * A / L ^ 4 - A / L ^ 2) * Real.cos θ ^ 2
        + (ψ₀ * A ^ 2 / (2 * L ^ 4)) * Real.cos θ ^ 3 := by
    funext θ
    ring
  rw [hfun, cos_polynomial_integral]
  field_simp
  try ring

/-- **The Herglotz advance as a function of the inverse semi-latus** `u = 1/p`:
`Δφ_E(ψ₀, u) = π·ψ₀²u² − π·ψ₀u`. -/
noncomputable def herglotzAdvance (ψ₀ u : ℝ) : ℝ :=
  Real.pi * ψ₀ ^ 2 * u ^ 2 - Real.pi * ψ₀ * u

/-- **The extra advance vanishes only trivially or at one orbit**:
`Δφ_E = 0 ↔ ψ₀ = 0 ∨ ψ₀·u = 1` — the dissipative correction can hide at exactly one
orbit size (`p = ψ₀`), never at two. -/
theorem herglotzAdvance_eq_zero_iff (ψ₀ u : ℝ) (hu : u ≠ 0) :
    herglotzAdvance ψ₀ u = 0 ↔ ψ₀ = 0 ∨ ψ₀ * u = 1 := by
  unfold herglotzAdvance
  constructor
  · intro h
    have hfac : Real.pi * ((ψ₀ * u) * (ψ₀ * u - 1)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with hπ | hin
    · exact absurd hπ Real.pi_ne_zero
    · rcases mul_eq_zero.mp hin with h0 | h1
      · rcases mul_eq_zero.mp h0 with h' | h'
        · exact Or.inl h'
        · exact absurd h' hu
      · exact Or.inr (by linarith [h1])
  · rintro (h | h)
    · rw [h]
      ring
    · linear_combination Real.pi * ψ₀ * u * h

/-- **The two-orbit exclusion** — sharper than the paper's single-planet bound: if two
orbits of different sizes both show zero anomalous advance, the Herglotz field
vanishes exactly.  One planet can sit at the hiding orbit `p = ψ₀`; two different
planets cannot. -/
theorem herglotz_two_orbit_exclusion (ψ₀ u₁ u₂ : ℝ) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0)
    (hne : u₁ ≠ u₂)
    (h₁ : herglotzAdvance ψ₀ u₁ = 0) (h₂ : herglotzAdvance ψ₀ u₂ = 0) :
    ψ₀ = 0 := by
  rcases (herglotzAdvance_eq_zero_iff ψ₀ u₁ hu₁).mp h₁ with h | h
  · exact h
  · rcases (herglotzAdvance_eq_zero_iff ψ₀ u₂ hu₂).mp h₂ with h' | h'
    · exact h'
    · have hψ : ψ₀ ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h
        exact one_ne_zero h.symm
      exact absurd (mul_left_cancel₀ hψ (h.trans h'.symm)) hne

/-! ### §D — the deflection of light from the same integrals -/

/-- `∫_{−π/2}^{π/2} (α·cosθ + β·cos²θ + γ·cos³θ) dθ = 2α + βπ/2 + 4γ/3` — the
half-revolution values of the cosine powers, by the same antiderivative as the full
revolution. -/
theorem cos_polynomial_integral_half (α β γ : ℝ) :
    (∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        (α * Real.cos θ + β * Real.cos θ ^ 2 + γ * Real.cos θ ^ 3))
      = 2 * α + β * Real.pi / 2 + 4 * γ / 3 := by
  have hFTC : ∀ θ : ℝ, HasDerivAt
      (fun x => α * Real.sin x + β * (x / 2 + Real.sin (2 * x) / 4)
        + γ * (Real.sin x - Real.sin x ^ 3 / 3))
      (α * Real.cos θ + β * Real.cos θ ^ 2 + γ * Real.cos θ ^ 3) θ := by
    intro θ
    have hsin : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
    have hlin : HasDerivAt (fun x : ℝ => 2 * x) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul 2
    have h2x : HasDerivAt (fun x : ℝ => Real.sin (2 * x))
        (Real.cos (2 * θ) * 2) θ := (Real.hasDerivAt_sin (2 * θ)).comp θ hlin
    have hsin3 : HasDerivAt (fun x : ℝ => Real.sin x ^ 3)
        (3 * Real.sin θ ^ 2 * Real.cos θ) θ := by
      have h := (Real.hasDerivAt_sin θ).pow 3
      refine h.congr_deriv ?_
      push_cast
      ring
    have h := ((hsin.const_mul α).add
      ((((hasDerivAt_id θ).div_const 2).add (h2x.div_const 4)).const_mul β)).add
      ((hsin.sub (hsin3.div_const 3)).const_mul γ)
    refine h.congr_deriv ?_
    rw [Real.cos_two_mul, Real.sin_sq]
    ring
  have hcont : Continuous fun θ : ℝ =>
      α * Real.cos θ + β * Real.cos θ ^ 2 + γ * Real.cos θ ^ 3 := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hFTC θ) (hcont.intervalIntegrable _ _)]
  have hsπ : Real.sin (2 * (Real.pi / 2)) = 0 := by
    rw [show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
  have hsnπ : Real.sin (2 * -(Real.pi / 2)) = 0 := by
    rw [show 2 * -(Real.pi / 2) = -Real.pi from by ring, Real.sin_neg, Real.sin_pi]
    ring
  rw [Real.sin_pi_div_two, hsπ]
  rw [show Real.sin (-(Real.pi / 2)) = -1 from by
    rw [Real.sin_neg, Real.sin_pi_div_two]]
  rw [hsnπ]
  ring

/-- **Einstein's light deflection `4GM/b` from the cosine-cube integral**: the
Laplace–Runge–Lenz form of the null bending integrates the post-Newtonian term
`3GMA·cos³θ/L²` over the passage, and `∫cos³ = 4/3` yields exactly `4GMA/L² = 4GM/b`
with `b = L²/A` the impact parameter — Einstein's second classical test from the same
machinery as the perihelion advance. -/
theorem lightDeflection_GR (GM A L : ℝ) (hL : L ≠ 0) :
    (∫ θ in (-(Real.pi / 2))..(Real.pi / 2), (3 * GM * A / L ^ 2) * Real.cos θ ^ 3)
      = 4 * GM / (L ^ 2 / A) := by
  have hfun : (fun θ : ℝ => (3 * GM * A / L ^ 2) * Real.cos θ ^ 3)
      = fun θ : ℝ => (0 : ℝ) * Real.cos θ + (0 : ℝ) * Real.cos θ ^ 2
        + (3 * GM * A / L ^ 2) * Real.cos θ ^ 3 := by
    funext θ
    ring
  rw [hfun, cos_polynomial_integral_half]
  field_simp
  try ring

/-- **The Herglotz extra deflection, exactly** (arXiv:2511.16304, the light integral):

  `Δφ_E = 2GMψ₀²/(3Ab²) − πGMψ₀/(2Ab)`

— and since the photon's effective Laplace–Runge–Lenz magnitude scales as the squared
frequency, the ratio to `4GM/b` scales as the wavelength squared: the plasma-like
chromatic bending the paper matches against the Cassini constraint. -/
theorem herglotzLightDeflection_integral (GM A b ψ₀ : ℝ) (hA : A ≠ 0) (hb : b ≠ 0) :
    (b ^ 2 * GM * ψ₀ / A) * ∫ θ in (-(Real.pi / 2))..(Real.pi / 2),
        ((ψ₀ / (2 * b ^ 4)) * Real.cos θ ^ 3 - (1 / b ^ 3) * Real.cos θ ^ 2)
      = 2 * GM * ψ₀ ^ 2 / (3 * A * b ^ 2) - Real.pi * GM * ψ₀ / (2 * A * b) := by
  have hfun : (fun θ : ℝ => (ψ₀ / (2 * b ^ 4)) * Real.cos θ ^ 3
      - (1 / b ^ 3) * Real.cos θ ^ 2)
      = fun θ : ℝ => (0 : ℝ) * Real.cos θ + (-(1 / b ^ 3)) * Real.cos θ ^ 2
        + (ψ₀ / (2 * b ^ 4)) * Real.cos θ ^ 3 := by
    funext θ
    ring
  rw [hfun, cos_polynomial_integral_half]
  field_simp
  try ring

end OrbitTests

/- ZIL-BEGIN -/

zil attach Relativity.SemiClassical.HerglotzGravity.HerglotzFRTData.einstein_reduction where
  formalizes @ "claim:the-herglotz-f-r-t-field-equations-reduce-to-the-einstein-equation-at-vanishing-herglotz-field-and-f-equals-r-meeting-the-clausius-thermodynamic-route-at-the-same-equation",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:wazny-csillag-pinto-harko-2025-herglotz-type-f-r-t-gravity-arxiv-2511-16304",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius"

zil attach Relativity.SemiClassical.HerglotzGravity.HerglotzFRTData.trace_equation where
  derives @ "claim:contracting-the-herglotz-f-r-t-field-equation-with-the-inverse-metric-under-the-natural-trace-data-gives-the-papers-trace-equation-exactly",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:wazny-csillag-pinto-harko-2025-herglotz-type-f-r-t-gravity-arxiv-2511-16304"

zil attach Relativity.SemiClassical.HerglotzGravity.HerglotzFRTData.traceless_form where
  derives @ "claim:the-traceless-form-of-the-herglotz-f-r-t-field-equation-follows-from-the-equation-and-its-trace-by-an-exact-pointwise-linear-combination-the-form-whose-time-time-component-drives-the-newtonian-limit",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Relativity.SemiClassical.HerglotzGravity.herglotzAdvance_integral",
  supported_by @ "lean:Cosmology.FLRW.Dynamics.herglotz_vacuum_equationOfState_iff",
  caveat @ "claim:derivative-built-tensors-enter-as-data-the-full-field-theoretic-weighted-variation-and-non-constant-couplings-in-the-balance-remain-open-with-hasvargradient-as-the-natural-carrier"

zil attach Relativity.SemiClassical.HerglotzGravity.balance_current where
  derives @ "claim:the-balance-current-of-herglotz-f-r-t-gravity-at-constant-couplings-the-energy-momentum-divergence-equals-the-herglotz-drain-minus-half-the-matter-trace-gradient-plus-the-coupling-remainder",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:wazny-csillag-pinto-harko-2025-herglotz-type-f-r-t-gravity-arxiv-2511-16304",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius_with_local_cosmological_constancy"

zil attach Relativity.SemiClassical.HerglotzGravity.conservation_iff_herglotz_divergence_free where
  derives @ "claim:the-energy-momentum-tensor-is-conserved-exactly-when-the-herglotz-tensor-is-divergence-free-at-vanishing-matter-trace-coupling-the-papers-conservation-constraint",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Relativity.SemiClassical.HerglotzGravity.balance_current"

zil attach Relativity.SemiClassical.HerglotzGravity.lightDeflection_GR where
  derives @ "claim:einsteins-light-deflection-four-g-m-over-b-follows-from-the-cosine-cube-half-revolution-integral-the-second-classical-test-from-the-same-machinery-as-the-perihelion",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Relativity.SemiClassical.HerglotzGravity.cos_polynomial_integral_half"

zil attach Relativity.SemiClassical.HerglotzGravity.herglotzLightDeflection_integral where
  derives @ "claim:the-herglotz-extra-deflection-evaluates-exactly-and-its-ratio-to-the-einstein-bending-scales-as-the-wavelength-squared-the-chromatic-plasma-like-signature",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:wazny-csillag-pinto-harko-2025-herglotz-type-f-r-t-gravity-arxiv-2511-16304"

zil attach Relativity.SemiClassical.HerglotzGravity.herglotzAdvance_integral where
  formalizes @ "claim:the-herglotz-dissipative-correction-to-the-perihelion-advance-evaluates-exactly-to-pi-times-the-squared-ratio-minus-the-ratio-of-the-herglotz-length-to-the-semi-latus-rectum",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:wazny-csillag-pinto-harko-2025-herglotz-type-f-r-t-gravity-arxiv-2511-16304",
  supported_by @ "lean:ClassicalMechanics.dampedOscillatorContactSlice",
  supported_by @ "lean:ClassicalMechanics.HerglotzContactSlice.effectiveLagrangian",
  caveat @ "claim:the-covariant-herglotz-f-r-t-field-equations-with-general-f-are-not-formalized-the-newtonian-advance-the-light-deflection-and-the-nonconservative-friedmann-pair-are-the-formalized-faces-and-the-flrw-sector-lives-in-cosmology-flrw"

zil attach Relativity.SemiClassical.HerglotzGravity.herglotz_two_orbit_exclusion where
  derives @ "claim:two-orbits-of-different-size-with-no-anomalous-advance-force-the-herglotz-field-to-vanish-exactly-one-planet-can-sit-at-the-hiding-orbit-two-cannot",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Relativity.SemiClassical.HerglotzGravity.herglotzAdvance_eq_zero_iff"

zil attach Relativity.SemiClassical.HerglotzGravity.apsidalAdvance_hasDerivAt_zero where
  derives @ "claim:einsteins-perihelion-coefficient-is-the-derivative-at-zero-of-the-exact-apsidal-advance-so-the-1915-computation-is-the-linearization-of-a-closed-form-carried-to-all-orders-of-the-oscillation-step",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Relativity.SemiClassical.HerglotzGravity.orbitOscillator_solution"

zil attach Relativity.SemiClassical.HerglotzGravity.einsteinParameter_planck_compton where
  derives @ "claim:the-mercury-precession-parameter-is-six-planck-areas-per-compton-wavelength-of-the-source-times-semi-latus-rectum-a-quantum-informational-reading-of-a-classical-orbit-number",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComptonClock.ZeroPointLength.compton_grav_product_eq_planckSq",
  caveat @ "claim:the-relativistic-binet-equation-supplying-the-parameter-from-schwarzschild-geodesics-is-not-formalized-the-holographic-route-reaches-the-einstein-equation-through-the-clausius-derivation-but-not-yet-the-geodesics"

zil attach Relativity.SemiClassical.HerglotzGravity.einsteinParameter_bitCount where
  derives @ "claim:the-precession-parameter-is-a-ratio-of-two-counts-the-orbit-size-in-source-compton-units-over-the-planck-bit-count-of-the-orbit-screen",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.TransverseMomentumEffectiveMass.inverseSquare_R_only_through_bits",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.einstein_from_clausius"

/- ZIL-END -/

end Relativity.SemiClassical.HerglotzGravity

end

end
