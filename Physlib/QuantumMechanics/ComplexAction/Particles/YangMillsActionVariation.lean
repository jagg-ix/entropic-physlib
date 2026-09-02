/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.ProjectionGradientDecomposition

meta import Zil

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionVariation -/

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionVariation -/

/-!
# The variational core of the Yang–Mills equation `δ∫tr(F²) → D_μ F^{μν} = J`

Varying the Yang–Mills action `S = −¼∫tr(F_{μν}F^{μν})` with respect to the gauge potential `A` yields the
field equation `D_μ F^{μν} = J^ν`.  The algebraic core of that derivation is formalized here:

* the gauge-covariant variation of the field strength `δF_{μν} = D_μ(δA)_ν − D_ν(δA)_μ`;
* the **ad-invariance of the trace** `tr([A,F]G) + tr(F[A,G]) = 0` — the reason the connection terms drop,
  so the trace pairing is gauge-invariant;
* the **covariant integration-by-parts identity** `tr((D_μ F)G) + tr(F(D_μ G)) = ∂_μ tr(FG)` — the covariant
  derivative acts on `tr(FG)` as the *ordinary* derivative.  This is the step that, after integrating the
  total-derivative `∂_μ tr(FG)` to a vanishing boundary term, turns `δS = ∫tr(F·δF) = ∫tr(F·Dδa)` into
  `−∫tr((D_μ F)·δA)`, whose stationarity for arbitrary `δA` is `D_μ F^{μν} = 0`.

* `fieldStrength_variation` — `δF = D(δA) − D(δA)`.
* `trace_ad_invariant` — `tr([A,F]G) + tr(F[A,G]) = 0`.
* `covariant_leibniz_trace` — `tr((D_μ F)G) + tr(F(D_μ G)) = ∂_μ tr(FG)`.

Honest scope: the pointwise algebraic identities reducing the action variation to the field equation; the
spacetime integral and the vanishing of the total-derivative boundary term (giving `D_μ F^{μν} = J`) are
not carried here (the repository's divergence is an abstract linear map).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionVariation

open Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The gauge-covariant variation of the gauge potential** `D_μ(δA)_ν = ∂_μ δA_ν + [A_μ, δA_ν]`
(`dδA μ ν = ∂_μ δA_ν`). -/
def covVariationA (A : ι → Matrix ι ι ℝ) (δA : ι → Matrix ι ι ℝ) (dδA : ι → ι → Matrix ι ι ℝ)
    (μ ν : ι) : Matrix ι ι ℝ :=
  dδA μ ν + A μ * δA ν - δA ν * A μ

/-- **The variation of the field strength** `δF_{μν} = ∂_μ δA_ν − ∂_ν δA_μ + [δA_μ, A_ν] + [A_μ, δA_ν]`. -/
def fieldStrengthVariation (A : ι → Matrix ι ι ℝ) (δA : ι → Matrix ι ι ℝ) (dδA : ι → ι → Matrix ι ι ℝ)
    (μ ν : ι) : Matrix ι ι ℝ :=
  dδA μ ν - dδA ν μ + (δA μ * A ν - A ν * δA μ) + (A μ * δA ν - δA ν * A μ)

/-- **The field-strength variation is gauge-covariant** `δF_{μν} = D_μ(δA)_ν − D_ν(δA)_μ`. -/
@[zil_level physical_theorem]
theorem fieldStrength_variation (A : ι → Matrix ι ι ℝ) (δA : ι → Matrix ι ι ℝ)
    (dδA : ι → ι → Matrix ι ι ℝ) (μ ν : ι) :
    fieldStrengthVariation A δA dδA μ ν = covVariationA A δA dδA μ ν - covVariationA A δA dδA ν μ := by
  unfold fieldStrengthVariation covVariationA; abel

/-- **The trace is ad-invariant** `tr([A,F]G) + tr(F[A,G]) = 0` — the connection commutator terms cancel
under the trace (cyclicity).  This is why the covariant derivative acts on `tr(FG)` as the ordinary one. -/
@[zil_level physical_theorem]
theorem trace_ad_invariant (A F G : Matrix ι ι ℝ) :
    ((A * F - F * A) * G).trace + (F * (A * G - G * A)).trace = 0 := by
  simp only [sub_mul, mul_sub, Matrix.trace_sub, mul_assoc]
  have h : (A * (F * G)).trace = (F * (G * A)).trace := by
    rw [Matrix.trace_mul_comm, mul_assoc]
  rw [h]; abel

/-- **The covariant integration-by-parts identity** `tr((D_μ F)G) + tr(F(D_μ G)) = ∂_μ tr(FG)` — the
gauge-covariant derivative acts on the trace pairing as the ordinary partial derivative (`∂_μ tr(FG) =
tr((∂_μ F)G) + tr(F(∂_μ G))`), because the connection terms cancel by ad-invariance.  The step that
delivers the Yang–Mills field equation from the action variation. -/
@[zil_level physical_theorem]
theorem covariant_leibniz_trace (A dF dG : ι → Matrix ι ι ℝ) (F G : Matrix ι ι ℝ) (μ : ι) :
    (covariantDerivEndo A dF F μ * G).trace + (F * covariantDerivEndo A dG G μ).trace
      = (dF μ * G + F * dG μ).trace := by
  unfold covariantDerivEndo
  have key := trace_ad_invariant (A μ) F G
  simp only [add_mul, sub_mul, mul_add, mul_sub, mul_assoc, Matrix.trace_add, Matrix.trace_sub] at key ⊢
  linarith [key]

end Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionVariation

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionVariation

zil attach fieldStrength_variation where
  formalizes @ "claim:the-variation-of-the-yang-mills-field-strength-under-a-variation-of-the-gauge-potential-equals-the-antisymmetrized-gauge-covariant-derivative-of-the-potential-variation-delta-f-equals-d-delta-a-minus-d-delta-a"

zil attach trace_ad_invariant where
  supported_by @ "lean:HermitianMat.trace_sub",
  formalizes @ "claim:the-matrix-trace-is-ad-invariant-the-trace-of-the-connection-commutator-with-f-times-g-plus-f-times-the-connection-commutator-with-g-vanishes-so-the-connection-terms-drop-under-the-trace"

zil attach covariant_leibniz_trace where
  supported_by @ "lean:trace_ad_invariant",
  formalizes @ "claim:the-covariant-integration-by-parts-identity-the-trace-of-the-covariant-derivative-of-f-times-g-plus-f-times-the-covariant-derivative-of-g-equals-the-ordinary-partial-derivative-of-the-trace-of-f-g-the-step-delivering-the-yang-mills-field-equation-from-the-action-variation"

zil_file_contract physlib.yangMillsActionVariation where
  promises "The variational core of the Yang-Mills field equation, the derivation of the divergence-equals-current field equation from the F-squared action. The variation of the field strength under a variation of the gauge potential equals the antisymmetrized gauge-covariant derivative of the potential variation. The matrix trace is ad-invariant: the trace of the connection commutator with F times G plus F times the connection commutator with G vanishes, so the connection terms drop under the trace and the trace pairing is gauge-invariant. The covariant integration-by-parts identity states that the trace of the covariant derivative of F times G plus F times the covariant derivative of G equals the ordinary partial derivative of the trace of F G, because the connection terms cancel by ad-invariance; this is the step that, after integrating the total derivative to a vanishing boundary term, turns the action variation into the field equation whose stationarity for arbitrary potential variation is the vanishing covariant divergence of the field strength. Honest scope: the pointwise algebraic identities reducing the action variation to the field equation; the spacetime integral and the vanishing boundary term are not carried here."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.CovariantDerivativeEndomorphism.covariantDerivEndo"
  ]
  forbids_substitutes [
    "reading the pointwise algebraic variation identities as the full variational derivation including the spacetime integral and the vanishing of the boundary term"
  ]
  witnessed_by [
    fieldStrength_variation,
    trace_ad_invariant,
    covariant_leibniz_trace
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.yangMillsActionVariation

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsFieldEquation -/

/-!
# The Yang–Mills field equation from stationarity

Completing the variational derivation `δ∫tr(F²) → D_μ F^{μν} = J^ν`.  `YangMillsActionVariation` reduced the
action variation, via the covariant integration-by-parts identity, to

`δS = −∑_ν ∫ tr(E^ν · δA_ν)`,   `E^ν := D_μ F^{μν} − J^ν`   (the Euler–Lagrange density).

The remaining step is the **fundamental lemma of the calculus of variations**: since the trace pairing
`⟨X, Y⟩ = tr(XY)` is non-degenerate (`tr(X Xᵀ) = ∑_{ij} X_{ij}² = 0 ⇒ X = 0`), stationarity `δS = 0` for an
arbitrary variation `δA` forces `E^ν = 0` at every point — i.e. the **Yang–Mills field equation**
`D_μ F^{μν} = J^ν`.

* `trace_pairing_nondegenerate` — `(∀ Y, tr(X Y) = 0) → X = 0`.
* `yangMills_field_equation` — stationarity for arbitrary `δA` gives `E^ν = 0` (`D_μ F^{μν} = J^ν`).

Honest scope: the algebraic fundamental lemma and the extraction of the field equation from pointwise
stationarity; the spacetime integral itself (reducing the functional variation to this pointwise form) is
modelled by the arbitrary-variation hypothesis, matching the repository's abstract-divergence treatment.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsFieldEquation

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The trace pairing is non-degenerate** `(∀ Y, tr(X Y) = 0) → X = 0` — the fundamental lemma of the
calculus of variations for the trace form (test `Y = Xᵀ`: `tr(X Xᵀ) = ∑_{ij} X_{ij}²`). -/
@[zil_level physical_theorem]
theorem trace_pairing_nondegenerate (X : Matrix ι ι ℝ) (hX : ∀ Y, (X * Y).trace = 0) : X = 0 := by
  have h := hX Xᵀ
  have hsq : (X * Xᵀ).trace = ∑ i, ∑ j, (X i j) ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (sq (X i j)).symm
  rw [hsq] at h
  ext i j
  have hi : ∑ j, (X i j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _).mp h i
      (Finset.mem_univ i)
  have hij : (X i j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (X i j)).mp hi j (Finset.mem_univ j)
  simpa using pow_eq_zero_iff (by norm_num) |>.mp hij

/-- **The Yang–Mills field equation from stationarity** — if the action variation
`∑_ν tr(E^ν · δA_ν)` vanishes for every variation `δA`, then the Euler–Lagrange density `E^ν = 0` at every
`ν`.  With `E^ν = D_μ F^{μν} − J^ν` this is the Yang–Mills field equation `D_μ F^{μν} = J^ν`. -/
@[zil_level bridge_theorem]
theorem yangMills_field_equation (E : ι → Matrix ι ι ℝ)
    (hstat : ∀ (δA : ι → Matrix ι ι ℝ), (∑ ν, (E ν * δA ν).trace) = 0) :
    ∀ ν, E ν = 0 := by
  intro ν₀
  apply trace_pairing_nondegenerate
  intro Y
  have h := hstat (fun ν => if ν = ν₀ then Y else 0)
  rw [Finset.sum_eq_single_of_mem ν₀ (Finset.mem_univ ν₀)
    (fun ν _ hν => by simp [hν])] at h
  simpa using h

end Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsFieldEquation

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsFieldEquation

zil attach trace_pairing_nondegenerate where
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  formalizes @ "claim:the-matrix-trace-pairing-is-non-degenerate-if-the-trace-of-x-times-y-vanishes-for-every-y-then-x-is-zero-the-fundamental-lemma-of-the-calculus-of-variations-for-the-trace-form"

zil attach yangMills_field_equation where
  formalizes @ "claim:the-yang-mills-field-equation-from-stationarity-if-the-action-variation-the-sum-over-nu-of-the-trace-of-the-euler-lagrange-density-times-the-potential-variation-vanishes-for-every-variation-then-the-euler-lagrange-density-vanishes-the-covariant-divergence-of-the-field-strength-equals-the-current",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionVariation.covariant_leibniz_trace"

zil_file_contract physlib.yangMillsFieldEquation where
  promises "The Yang-Mills field equation from stationarity, completing the variational derivation of the divergence-equals-current equation from the F-squared action. The covariant integration-by-parts identity reduced the action variation to minus the sum over nu of the integral of the trace of the Euler-Lagrange density times the potential variation, where the Euler-Lagrange density is the covariant divergence of the field strength minus the current. The trace pairing is non-degenerate, the fundamental lemma of the calculus of variations for the trace form: if the trace of X times Y vanishes for every Y then X is zero, proved by testing with the transpose so that the trace of X times its transpose is the sum of the squared entries. Hence stationarity of the action for an arbitrary potential variation forces the Euler-Lagrange density to vanish at every index, which is the Yang-Mills field equation, the covariant divergence of the field strength equals the current. Honest scope: the algebraic fundamental lemma and the extraction of the field equation from pointwise stationarity; the spacetime integral reducing the functional variation to the pointwise form is modelled by the arbitrary-variation hypothesis."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionVariation.covariant_leibniz_trace"
  ]
  forbids_substitutes [
    "reading the pointwise fundamental-lemma extraction as the full functional variation including the spacetime integral and the vanishing boundary term"
  ]
  witnessed_by [
    trace_pairing_nondegenerate,
    yangMills_field_equation
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.yangMillsFieldEquation

/- Consolidated from Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionSpacetimeIntegral -/

/-!
# The spacetime-integral step of the Yang–Mills variation

`YangMillsFieldEquation` extracted `D_μ F^{μν} = J^ν` from stationarity *for an arbitrary variation* — a
hypothesis that stood in for the spacetime integral.  This module makes that integral explicit and honest by
modelling it as an additive functional `I` (the linear part of `∫ … d⁴x`) on a module of densities, and
shows the two facts the integral actually contributes:

* **Covariant integration by parts.** The pointwise covariant Leibniz identity
  (`YangMillsActionVariation.covariant_leibniz_trace`), integrated, reads `I(dDFG) + I(dFDG) = I(dTot)` with
  `dTot` a total derivative; the boundary term `I(dTot) = 0` then gives `I(dFDG) = −I(dDFG)`.  This is the
  step turning `δS = ∫ tr(F · D_μδA)` into `−∫ tr((D_μF) · δA)`.
* **Field equation from a stationary integral.** Once integration by parts has reduced the variation to the
  Euler–Lagrange pairing `I(redVar δA) = ∑_ν tr(E^ν · δA_ν)`, stationarity of the *integral* for every
  variation yields `E^ν = 0` — feeding the fundamental lemma `yangMills_field_equation`.

So the earlier "arbitrary-variation hypothesis" is now the composite of (integral IbP) + (integral evaluates
the pairing) + (stationarity), rather than an opaque assumption.

Honest scope: `I` is modelled abstractly as an additive functional with a vanishing-boundary hypothesis and
a faithfulness hypothesis (`hreduce`, that integrating the reduced density returns the pointwise pairing);
the measure-theoretic construction of `∫ d⁴x` and the analytic vanishing of the boundary term are not built.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionSpacetimeIntegral

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Covariant integration by parts under the spacetime integral.**  Modelling `∫ … d⁴x` by an additive
functional `I`, the integrated covariant Leibniz identity `dDFG + dFDG = dTot` (with `dTot` a total
derivative) together with the vanishing boundary term `I(dTot) = 0` gives `I(dFDG) = −I(dDFG)` — the step
that moves the covariant derivative off `δA` and onto `F` under the integral. -/
@[zil_level physical_theorem]
theorem covariant_integration_by_parts {D : Type*} [AddCommGroup D] (I : D →+ ℝ)
    (dDFG dFDG dTot : D) (hLeibniz : dDFG + dFDG = dTot) (hbdy : I dTot = 0) :
    I dFDG = -I dDFG := by
  have h : I dDFG + I dFDG = 0 := by rw [← map_add, hLeibniz, hbdy]
  linarith

/-- **The Yang–Mills field equation from a stationary integral.**  After integration by parts the action
variation is the integrated Euler–Lagrange pairing `I(redVar δA) = ∑_ν tr(E^ν · δA_ν)` (`hreduce`);
stationarity of the integral for every variation `δA` (`hstat`) then forces `E^ν = 0`, i.e. `D_μ F^{μν} =
J^ν`.  This supplies the arbitrary-variation hypothesis of `yangMills_field_equation` from the integral. -/
@[zil_level bridge_theorem]
theorem stationary_action_implies_field_equation {D : Type*} [AddCommGroup D]
    (I : D →+ ℝ) (redVar : (ι → Matrix ι ι ℝ) → D) (E : ι → Matrix ι ι ℝ)
    (hreduce : ∀ δA, I (redVar δA) = ∑ ν, (E ν * δA ν).trace)
    (hstat : ∀ δA, I (redVar δA) = 0) :
    ∀ ν, E ν = 0 :=
  YangMillsFieldEquation.yangMills_field_equation E fun δA => (hreduce δA).symm.trans (hstat δA)

end Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionSpacetimeIntegral

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionSpacetimeIntegral

zil attach covariant_integration_by_parts where
  formalizes @ "claim:covariant-integration-by-parts-under-the-spacetime-integral-modelling-the-integral-by-an-additive-functional-the-integrated-covariant-leibniz-identity-with-a-total-derivative-and-a-vanishing-boundary-term-gives-that-integrating-f-times-the-covariant-derivative-of-delta-a-equals-minus-integrating-the-covariant-derivative-of-f-times-delta-a",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsActionVariation.covariant_leibniz_trace"

zil attach stationary_action_implies_field_equation where
  formalizes @ "claim:the-yang-mills-field-equation-from-a-stationary-integral-after-integration-by-parts-the-integrated-euler-lagrange-pairing-being-stationary-for-every-variation-forces-the-euler-lagrange-density-to-vanish-the-covariant-divergence-of-the-field-strength-equals-the-current",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsFieldEquation.yangMills_field_equation"

zil_file_contract physlib.yangMillsActionSpacetimeIntegral where
  promises "The spacetime-integral step of the Yang-Mills variation. The field-equation module extracted the divergence-equals-current equation from stationarity for an arbitrary variation, a hypothesis standing in for the spacetime integral. This module makes that integral explicit by modelling it as an additive functional, the linear part of the four-dimensional integral, on a module of densities, and proves the two facts the integral contributes. Covariant integration by parts: the integrated covariant Leibniz identity, with a total derivative and a vanishing boundary term, gives that integrating F times the covariant derivative of the potential variation equals minus integrating the covariant derivative of F times the potential variation. Field equation from a stationary integral: once integration by parts has reduced the variation to the integrated Euler-Lagrange pairing, stationarity of the integral for every variation forces the Euler-Lagrange density to vanish, feeding the fundamental lemma. So the earlier arbitrary-variation hypothesis is now the composite of integral integration by parts, the integral evaluating the pairing, and stationarity. Honest scope: the integral is modelled abstractly as an additive functional with a vanishing-boundary hypothesis and a faithfulness hypothesis that integrating the reduced density returns the pointwise pairing; the measure-theoretic construction of the integral and the analytic vanishing of the boundary term are not built."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.YangMillsFieldEquation.yangMills_field_equation"
  ]
  forbids_substitutes [
    "reading the abstract additive-functional model of the integral as the measure-theoretic spacetime integral, or the vanishing-boundary and faithfulness hypotheses as proved analytic facts"
  ]
  witnessed_by [
    covariant_integration_by_parts,
    stationary_action_implies_field_equation
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.yangMillsActionSpacetimeIntegral

