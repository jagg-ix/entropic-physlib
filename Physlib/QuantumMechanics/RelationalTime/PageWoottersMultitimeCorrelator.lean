/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.PageWootters
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.RelationalTime.PageWoottersMultitimeCorrelator -/

/-!
# Page–Wootters two-time correlations

The relational-time carrier was formalized only at the level of *one-time*
conditional states `ρ_S(τ)`.  Moreva et al.'s quantum-time experiment probes the
next level — **two-time correlations** `C(τ₁,τ₂) = ⟨Q(τ₁)Q(τ₂)⟩` — testing that
the relational clock reproduces not just state trajectories but multitime
observables.

In the eigenvalue Page–Wootters model the conditional system evolves by a pure
Schrödinger phase `e^{iφ_S(t)}` with `φ_S(t) = −E_sys·t/ℏ` (the carrier field
`PageWoottersBipartite.phaseS`).  Writing `q = ⟨ψ_S|Q|ψ_S⟩` for the one-time
expectation of any system observable `Q`, the two-time correlator is

`C(τ₁,τ₂) = ⟨ψ_S(τ₁)|Q|ψ_S(τ₂)⟩ = e^{iE_sys(τ₁−τ₂)/ℏ}·q`.

This module builds that correlator (`twoTimeCorrelator`) on the Page–Wootters
carrier and proves it exhibits the signatures of emergent Heisenberg-picture
dynamics:

* it depends only on the clock-time **difference** (`twoTimeCorrelator_eq_phase_diff`,
  `twoTimeCorrelator_depends_on_difference`);
* it is **time-translation invariant** (`twoTimeCorrelator_time_translation_invariant`);
* its magnitude is **stationary**, equal to the one-time expectation magnitude
  (`twoTimeCorrelator_norm`); and
* it **reduces to the one-time expectation at coincidence** τ₁ = τ₂
  (`twoTimeCorrelator_coincidence`),

with the evolution phase tied back to the carrier's Schrödinger phase field
(`evolvedPhase_at_carrier_time`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics.Landauer

namespace PageWoottersBipartite

variable {d_sys d_clock : Type}
  [Fintype d_sys] [DecidableEq d_sys]
  [Fintype d_clock] [DecidableEq d_clock]
variable (M : PageWoottersBipartite d_sys d_clock)

/-- **The conditional evolution phase** at clock reading `t`:
`e^{iφ_S(t)} = e^{−iE_sys t/ℏ}`, the phase acquired by the system's energy
eigenstate. -/
def evolvedPhase (t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (↑(M.E_sys * t / M.ℏ) : ℂ))

/-- The evolution phase at the carrier's own clock reading equals the exponential
of the Page–Wootters Schrödinger phase field, `e^{iφ_S}`. -/
@[zil_level bridge_theorem]
theorem evolvedPhase_at_carrier_time :
    M.evolvedPhase M.t = Complex.exp (Complex.I * (↑M.phaseS : ℂ)) := by
  rw [evolvedPhase, M.phaseS_eq]
  congr 1
  push_cast; ring

/-- **The Page–Wootters two-time correlator** for a system observable with
one-time expectation `q = ⟨ψ_S|Q|ψ_S⟩`:
`C(τ₁,τ₂) = ⟨ψ_S(τ₁)|Q|ψ_S(τ₂)⟩ = conj(e^{iφ_S(τ₁)})·e^{iφ_S(τ₂)}·q`. -/
def twoTimeCorrelator (q : ℂ) (t₁ t₂ : ℝ) : ℂ :=
  (starRingEnd ℂ) (M.evolvedPhase t₁) * M.evolvedPhase t₂ * q

/-- **The two-time correlator depends only on the clock-time difference**:
`C(τ₁,τ₂) = e^{iE_sys(τ₁−τ₂)/ℏ}·q`. -/
@[zil_level bridge_theorem]
theorem twoTimeCorrelator_eq_phase_diff (q : ℂ) (t₁ t₂ : ℝ) :
    M.twoTimeCorrelator q t₁ t₂
      = Complex.exp (Complex.I * (↑(M.E_sys * (t₁ - t₂) / M.ℏ) : ℂ)) * q := by
  unfold twoTimeCorrelator evolvedPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have h : (starRingEnd ℂ) (-Complex.I * (↑(M.E_sys * t₁ / M.ℏ) : ℂ))
        + -Complex.I * (↑(M.E_sys * t₂ / M.ℏ) : ℂ)
      = Complex.I * (↑(M.E_sys * (t₁ - t₂) / M.ℏ) : ℂ) := by
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  rw [h]

/-- **Coincidence limit** — at equal clock times the two-time correlator reduces
to the one-time expectation `q`. -/
@[zil_level physical_theorem]
theorem twoTimeCorrelator_coincidence (q : ℂ) (t : ℝ) :
    M.twoTimeCorrelator q t t = q := by
  rw [twoTimeCorrelator_eq_phase_diff]; simp

/-- **Stationarity** — the two-time correlator's magnitude is time-independent,
equal to the one-time expectation magnitude `‖q‖`. -/
@[zil_level physical_theorem]
theorem twoTimeCorrelator_norm (q : ℂ) (t₁ t₂ : ℝ) :
    ‖M.twoTimeCorrelator q t₁ t₂‖ = ‖q‖ := by
  rw [twoTimeCorrelator_eq_phase_diff, norm_mul, Complex.norm_exp]
  simp [Complex.mul_re]

/-- **Time-translation invariance** — shifting both clock readings by `s` leaves
the two-time correlator unchanged, the hallmark of an emergent time-translation
symmetry. -/
@[zil_level bridge_theorem]
theorem twoTimeCorrelator_time_translation_invariant (q : ℂ) (t₁ t₂ s : ℝ) :
    M.twoTimeCorrelator q (t₁ + s) (t₂ + s) = M.twoTimeCorrelator q t₁ t₂ := by
  have h : M.E_sys * ((t₁ + s) - (t₂ + s)) / M.ℏ = M.E_sys * (t₁ - t₂) / M.ℏ := by
    ring
  rw [twoTimeCorrelator_eq_phase_diff, twoTimeCorrelator_eq_phase_diff, h]

/-- **Difference form** — the two-time correlator is a function of the single
clock-time difference `τ₁ − τ₂`. -/
@[zil_level physical_theorem]
theorem twoTimeCorrelator_depends_on_difference (q : ℂ) (t₁ t₂ : ℝ) :
    M.twoTimeCorrelator q t₁ t₂ = M.twoTimeCorrelator q (t₁ - t₂) 0 := by
  have h : M.E_sys * (t₁ - t₂) / M.ℏ = M.E_sys * ((t₁ - t₂) - 0) / M.ℏ := by ring
  rw [twoTimeCorrelator_eq_phase_diff, twoTimeCorrelator_eq_phase_diff, h]

end PageWoottersBipartite

end Physlib.Thermodynamics.Landauer

/- ZIL-BEGIN -/

open Zil
open Physlib.Thermodynamics.Landauer.PageWoottersBipartite

zil attach twoTimeCorrelator_eq_phase_diff where
  formalizes @ "claim:the-page-wootters-two-time-correlator-equals-e-to-the-i-e-sys-tau-one-minus-tau-two-over-hbar-times-the-one-time-expectation-depending-only-on-the-clock-time-difference",
  supported_by @ "lean:Physlib.Thermodynamics.Landauer.PageWoottersBipartite.evolvedPhase"

zil attach twoTimeCorrelator_time_translation_invariant where
  supported_by @ "lean:twoTimeCorrelator_eq_phase_diff",
  formalizes @ "claim:the-page-wootters-two-time-correlator-is-time-translation-invariant-shifting-both-clock-readings-leaves-it-unchanged",
  caveat @ "claim:this-is-the-eigenvalue-page-wootters-model-where-conditional-evolution-is-a-pure-schrodinger-phase-not-a-general-multilevel-heisenberg-operator-correlator"

zil attach twoTimeCorrelator_coincidence where
  supported_by @ "lean:twoTimeCorrelator_eq_phase_diff",
  formalizes @ "claim:at-equal-clock-times-the-two-time-correlator-reduces-to-the-one-time-expectation"

zil attach evolvedPhase_at_carrier_time where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:the-conditional-evolution-phase-at-the-carrier-clock-reading-equals-the-exponential-of-the-page-wootters-schrodinger-phase-field"

zil_file_contract physlib.pageWoottersMultitimeCorrelator where
  promises "The Page-Wootters relational carrier is extended from one-time conditional states to two-time correlations. For a system observable with one-time expectation q, the two-time correlator C(tau1,tau2) equals e to the i E_sys (tau1 minus tau2) over hbar times q, depending only on the clock-time difference. It is time-translation invariant, its magnitude is stationary and equal to the one-time expectation magnitude, and it reduces to the one-time expectation at coincidence - the signatures of emergent Heisenberg-picture time evolution. The evolution phase is tied back to the carrier's Schrodinger phase field."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Thermodynamics.Landauer.PageWoottersBipartite.evolvedPhase",
    "lean:Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator"
  ]
  forbids_substitutes [
    "reading the pure-phase eigenvalue correlator as a general multilevel Heisenberg operator two-time correlator",
    "claiming the correlator depends on the two clock readings separately rather than only their difference"
  ]
  witnessed_by [
    evolvedPhase_at_carrier_time,
    twoTimeCorrelator_eq_phase_diff,
    twoTimeCorrelator_coincidence,
    twoTimeCorrelator_norm,
    twoTimeCorrelator_time_translation_invariant,
    twoTimeCorrelator_depends_on_difference
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.pageWoottersMultitimeCorrelator

/- Consolidated from Physlib.QuantumMechanics.RelationalTime.PageWoottersLeggettGarg -/

/-!
# Leggett–Garg violation from the Page–Wootters two-time correlator

Moreva et al.'s multitime programme asks whether the relational carrier reproduces the
*temporal* Bell analogue — a Leggett–Garg inequality violation.  Building on the
Page–Wootters two-time correlator (`PageWoottersMultitimeCorrelator.twoTimeCorrelator`),
whose value is `C(τ₁,τ₂) = e^{iE_sys(τ₁−τ₂)/ℏ}·q`, the real two-time correlation of a
system observable with one-time expectation `q` is

`C(τ₁,τ₂) = q·cos(E_sys(τ₁−τ₂)/ℏ)`  (`lgCorrelator_eq_re`).

The three-time Leggett–Garg quantity `K₃ = C(τ₁,τ₂) + C(τ₂,τ₃) − C(τ₁,τ₃)` at equal
spacing `τ` is `K₃ = q(2cos θ − cos 2θ)` with `θ = E_sys τ/ℏ` (`lgK3_equalSpacing`).  At
`θ = π/3` and unit correlation this reaches `K₃ = 3/2` (`lgK3_violation`), which exceeds
the macrorealist Leggett–Garg bound `K₃ ≤ 1` (`lgK3_exceeds_classical_bound`) — the
temporal analogue of the Bell/CHSH violation, on the relational clock.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Thermodynamics.Landauer

namespace PageWoottersBipartite

variable {d_sys d_clock : Type}
  [Fintype d_sys] [DecidableEq d_sys]
  [Fintype d_clock] [DecidableEq d_clock]
variable (M : PageWoottersBipartite d_sys d_clock)

/-- **The real two-time correlation** of an observable with real one-time expectation `q`:
`C(τ₁,τ₂) = q·cos(E_sys(τ₁−τ₂)/ℏ)`. -/
def lgCorrelator (q t₁ t₂ : ℝ) : ℝ := q * Real.cos (M.E_sys * (t₁ - t₂) / M.ℏ)

/-- The Leggett–Garg correlator is the real part of the Page–Wootters two-time
correlator at a real observable expectation. -/
@[zil_level bridge_theorem]
theorem lgCorrelator_eq_re (q t₁ t₂ : ℝ) :
    (M.twoTimeCorrelator (q : ℂ) t₁ t₂).re = M.lgCorrelator q t₁ t₂ := by
  rw [twoTimeCorrelator_eq_phase_diff, lgCorrelator, mul_comm Complex.I, Complex.mul_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- **The three-time Leggett–Garg quantity** `K₃ = C(τ₁,τ₂) + C(τ₂,τ₃) − C(τ₁,τ₃)`. -/
def lgK3 (q t₁ t₂ t₃ : ℝ) : ℝ :=
  M.lgCorrelator q t₁ t₂ + M.lgCorrelator q t₂ t₃ - M.lgCorrelator q t₁ t₃

/-- **Equal-spacing form** — for three equally spaced clock readings `t, t+τ, t+2τ`,
`K₃ = q(2cos θ − cos 2θ)` with `θ = E_sys τ/ℏ`. -/
@[zil_level physical_theorem]
theorem lgK3_equalSpacing (q t τ : ℝ) :
    M.lgK3 q t (t + τ) (t + 2 * τ)
      = q * (2 * Real.cos (M.E_sys * τ / M.ℏ) - Real.cos (2 * (M.E_sys * τ / M.ℏ))) := by
  unfold lgK3 lgCorrelator
  have h1 : M.E_sys * (t - (t + τ)) / M.ℏ = -(M.E_sys * τ / M.ℏ) := by ring
  have h2 : M.E_sys * ((t + τ) - (t + 2 * τ)) / M.ℏ = -(M.E_sys * τ / M.ℏ) := by ring
  have h3 : M.E_sys * (t - (t + 2 * τ)) / M.ℏ = -(2 * (M.E_sys * τ / M.ℏ)) := by ring
  rw [h1, h2, h3, Real.cos_neg, Real.cos_neg]
  ring

/-- **The trigonometric Leggett–Garg envelope** `2cos θ − cos 2θ ≤ 3/2`, from
`2cos θ − cos 2θ = −2(cos θ − ½)² + 3/2`.  Equality holds at `cos θ = ½` (`θ = π/3`). -/
theorem two_cos_sub_cos_two_le (θ : ℝ) :
    2 * Real.cos θ - Real.cos (2 * θ) ≤ 3 / 2 := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (Real.cos θ - 1 / 2)]

/-- **The tight quantum (Lüders) Leggett–Garg bound** — for a normalized correlation
`0 ≤ q ≤ 1`, the three-time quantity is bounded by `K₃ ≤ 3/2`.  So the `3/2` reached by
`lgK3_violation` is the *maximal* quantum value: the relational carrier saturates the Lüders
bound, well above the macrorealist bound `1`. -/
@[zil_level bridge_theorem]
theorem lgK3_le_luders (q t τ : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    M.lgK3 q t (t + τ) (t + 2 * τ) ≤ 3 / 2 := by
  rw [lgK3_equalSpacing]
  have htrig := two_cos_sub_cos_two_le (M.E_sys * τ / M.ℏ)
  nlinarith [mul_le_mul_of_nonneg_left htrig hq0, hq1]

/-- **Leggett–Garg violation** — at `θ = E_sys τ/ℏ = π/3` and unit correlation `q = 1`,
the three-time quantity reaches `K₃ = 3/2`. -/
@[zil_level bridge_theorem]
theorem lgK3_violation (t τ : ℝ) (hθ : M.E_sys * τ / M.ℏ = Real.pi / 3) :
    M.lgK3 1 t (t + τ) (t + 2 * τ) = 3 / 2 := by
  rw [lgK3_equalSpacing, hθ, Real.cos_pi_div_three, Real.cos_two_mul, Real.cos_pi_div_three]
  norm_num

/-- **The Leggett–Garg violation exceeds the macrorealist bound.**  The relational
carrier's `K₃ = 3/2` violates the Leggett–Garg inequality `K₃ ≤ 1` — the temporal
analogue of the CHSH/Bell violation. -/
@[zil_level bridge_theorem]
theorem lgK3_exceeds_classical_bound (t τ : ℝ) (hθ : M.E_sys * τ / M.ℏ = Real.pi / 3) :
    (1 : ℝ) < M.lgK3 1 t (t + τ) (t + 2 * τ) := by
  rw [lgK3_violation M t τ hθ]; norm_num

end PageWoottersBipartite

end Physlib.Thermodynamics.Landauer

/- ZIL-BEGIN -/

open Zil
open Physlib.Thermodynamics.Landauer.PageWoottersBipartite

zil attach lgCorrelator_eq_re where
  formalizes @ "claim:the-leggett-garg-real-two-time-correlation-is-the-real-part-of-the-page-wootters-two-time-correlator-equal-to-q-cosine-of-the-energy-time-phase",
  supported_by @ "lean:Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator"

zil attach lgK3_violation where
  formalizes @ "claim:the-page-wootters-three-time-leggett-garg-quantity-reaches-three-halves-at-phase-pi-over-three-and-unit-correlation",
  supported_by @ "lean:Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgCorrelator"

zil attach lgK3_exceeds_classical_bound where
  supported_by @ "lean:lgK3_violation",
  formalizes @ "claim:the-relational-carrier-leggett-garg-quantity-three-halves-violates-the-macrorealist-bound-of-one-the-temporal-analogue-of-the-chsh-bell-violation",
  caveat @ "claim:this-is-the-eigenvalue-page-wootters-scalar-phase-model-and-the-macrorealist-bound-of-one-is-taken-as-the-standard-leggett-garg-inequality-not-re-derived-here"

zil_file_contract physlib.pageWoottersLeggettGarg where
  promises "The Page-Wootters relational carrier reproduces the temporal Bell analogue, a Leggett-Garg violation. The real two-time correlation of a system observable with one-time expectation q is q times the cosine of the energy-time phase, the real part of the two-time correlator. The three-time Leggett-Garg quantity K3 at equal clock spacing tau is q times two cosine theta minus cosine two theta with theta the energy-time phase, and at theta equal pi over three with unit correlation it reaches three halves, exceeding the macrorealist Leggett-Garg bound of one - the temporal analogue of the CHSH Bell violation on the relational clock."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Thermodynamics.Landauer.PageWoottersBipartite.twoTimeCorrelator",
    "lean:Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgCorrelator",
    "lean:Physlib.Thermodynamics.Landauer.PageWoottersBipartite.lgK3"
  ]
  forbids_substitutes [
    "reading the eigenvalue scalar-phase correlator as a general multilevel Heisenberg two-time correlator",
    "claiming the macrorealist bound of one is re-derived here rather than the standard Leggett-Garg inequality"
  ]
  witnessed_by [
    lgCorrelator_eq_re,
    lgK3_equalSpacing,
    lgK3_violation,
    lgK3_exceeds_classical_bound
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.pageWoottersLeggettGarg

