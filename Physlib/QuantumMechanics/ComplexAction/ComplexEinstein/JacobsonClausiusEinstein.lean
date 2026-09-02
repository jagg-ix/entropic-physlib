/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy
public import Physlib.Thermodynamics.BekensteinJacobsonEntropicBits
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
meta import Zil

/-!
# Closing the Clausius chain: Einstein's equation from horizon thermodynamics

This completes Jacobson's *Thermodynamics of Spacetime* derivation begun in `EinsteinEquationOfState`
by supplying the two remaining links that turn horizon thermodynamics into the null-contracted
equation of state feeding that module's `einstein_equation_of_state`:

* **The geometric heart (Raychaudhuri area deficit ↔ Ricci).**  At a local equilibrium point of a
  future-regular null congruence (vanishing expansion `θ` and shear `σ²`), the horizon cross-section
  area obeys `A'' = −(R_{ab}kᵃkᵇ)·A` — the second-order area deficit is governed by the null Ricci
  contraction.  This is `area_secondDeriv_at_equilibrium`, built from the repository's
  `FutureRegularHorizonAreaEvolution` (`A' = θA`) and null Raychaudhuri
  (`θ' = −½θ² − σ² − R_{ab}kᵃkᵇ`).

* **The Clausius equation of state.**  The Clausius relation `δQ = T δS` with the Unruh temperature
  `T = κ/2π`, Bekenstein area–entropy `δS = δA/4G`, the Raychaudhuri area deficit (`δA ∝ −R_{ab}kᵃkᵇ`,
  above), and the boost-Killing heat flux (`δQ ∝ −κ T_{ab}kᵃkᵇ`) fixes the coupling: per null
  direction, `R_{ab}kᵃkᵇ = 8πG · T_{ab}kᵃkᵇ` (`clausius_equation_of_state`).  Demanding this for
  every null direction and feeding it to `einstein_equation_of_state` yields the Einstein field
  equation with cosmological term (`einstein_from_clausius`) — the coupling `κ = 8πG` is **derived**,
  not chosen.

Honest scope: `clausius_equation_of_state` takes the Clausius balance in its per-direction density
form, with the shared kinematic factor (the `∫ λ dλ dA` weighting common to `δQ` and `δS`) already
cancelled — that cancellation, and the boost-Killing flux and area-entropy identifications, are the
standard-GR inputs of Jacobson's argument, carried elsewhere in the repo (`unruhTemperature`,
`bekensteinEntropy`, `FutureRegularNullRaychaudhuri`) and not re-derived here.  The local constancy
link is now composed with `CosmologicalConstantConstancy`: under the explicit contracted-Bianchi,
stress-conservation, and metric-compatible Leibniz inputs, the cosmological scalar produced by the
equation of state has vanishing gradient.  Promotion from vanishing gradient to one global constant
still requires connected-spacetime differential geometry.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein

open Matrix minkowskiMatrix MeasureTheory Topology
open Physlib.Thermodynamics
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy

/-- **The geometric heart of the Clausius derivation.**  At a local equilibrium point `s₀` of a
future-regular null horizon congruence — vanishing expansion `θ(s₀)=0` and shear `σ²(s₀)=0` — the
horizon cross-section area's second derivative is the null Ricci contraction times the area:
`A''(s₀) = −(R_{ab}kᵃkᵇ)·A(s₀)`.  The area deficit is thus governed by the Ricci curvature, via the
null Raychaudhuri equation `θ' = −½θ² − σ² − R_{ab}kᵃkᵇ` and the transport law `A' = θA`. -/
@[zil_level physical_theorem]
theorem area_secondDeriv_at_equilibrium (H : FutureRegularHorizonAreaEvolution) (s₀ : ℝ)
    (hθ : H.expansion s₀ = 0) (hσ : H.shearSq s₀ = 0) :
    deriv (deriv H.area) s₀ = -H.ricciNull s₀ * H.area s₀ := by
  have hA' : deriv H.area = fun s => H.expansion s * H.area s :=
    funext fun s => (H.area_hasDerivAt s).deriv
  have hd2 : HasDerivAt (fun s => H.expansion s * H.area s)
      ((-(H.expansion s₀) ^ 2 / 2 - H.shearSq s₀ - H.ricciNull s₀) * H.area s₀
        + H.expansion s₀ * (H.expansion s₀ * H.area s₀)) s₀ :=
    (H.expansion_hasDerivAt s₀).mul (H.area_hasDerivAt s₀)
  rw [hA', hd2.deriv, hθ, hσ]
  ring

/-- **The Clausius equation of state.**  For a single null direction, the Clausius relation
`κ T_{ab}kᵃkᵇ = T_U · (R_{ab}kᵃkᵇ / 4G)` (heat flux = Unruh temperature × Bekenstein entropy
variation, the shared kinematic factor cancelled) with the Unruh temperature `T_U = κ/2π` forces the
gravitational coupling `R_{ab}kᵃkᵇ = 8πG · T_{ab}kᵃkᵇ`.  The `8πG` is the arithmetic product of the
`2π` of the Unruh temperature and the `4G` of the Bekenstein area–entropy law. -/
@[zil_level physical_theorem]
theorem clausius_equation_of_state (G κb Rkk Tkk T_U : ℝ) (hG : G ≠ 0) (hκb : κb ≠ 0)
    (hUnruh : T_U = κb / (2 * Real.pi))
    (hClausius : κb * Tkk = T_U * (Rkk / (4 * G))) :
    Rkk = 8 * Real.pi * G * Tkk := by
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  subst hUnruh
  field_simp at hClausius
  linear_combination -hClausius

/-- **Integral stripping (fundamental theorem of calculus).**  Two continuous functions whose
integrals over `[0,T]` agree for every upper limit `T` are equal.  This is the calculus fact that
lets one pass from Jacobson's *integrated* Clausius relation (equal heat and entropy integrals over
every horizon patch) to the *pointwise* equation of state. -/
@[zil_level structural]
theorem eq_of_integral_eq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ T : ℝ, ∫ x in (0 : ℝ)..T, f x = ∫ x in (0 : ℝ)..T, g x) : f = g := by
  funext b
  have hF : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, f x) (f b) b :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 b)
      (hf.stronglyMeasurableAtFilter volume (nhds b)) hf.continuousAt
  have hG : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, g x) (g b) b :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 b)
      (hg.stronglyMeasurableAtFilter volume (nhds b)) hg.continuousAt
  rw [funext h] at hF
  exact hF.unique hG

/-- **The density-form Clausius relation is derived from the integrated Clausius relation.**  If the
heat-flux density `q(λ)` and the entropy-variation density `s(λ)` along a horizon generator satisfy
the Clausius balance `∫₀ᵀ q = ∫₀ᵀ T_U·s` for **every** patch size `T` (the same `∫₀ᵀ` on both
sides), then the pointwise Clausius relation `q(λ) = T_U·s(λ)` holds at every `λ` — in particular at
the base point, supplying the density-form hypothesis of `clausius_equation_of_state`.  This closes
the integral-stripping step of Jacobson's argument. -/
@[zil_level bridge_theorem]
theorem clausius_density_from_integrated (T_U : ℝ) (q s : ℝ → ℝ)
    (hq : Continuous q) (hs : Continuous s)
    (hInt : ∀ T : ℝ, ∫ t in (0 : ℝ)..T, q t = ∫ t in (0 : ℝ)..T, T_U * s t) :
    ∀ lam : ℝ, q lam = T_U * s lam :=
  fun lam => congrFun (eq_of_integral_eq hq (continuous_const.mul hs) hInt) lam

/-- **The Einstein field equation from the Clausius relation.**  If the per-direction Clausius
equation of state holds for **every** local null direction `k`, then the Einstein field equation with
cosmological term holds with the derived coupling `κ = 8πG`:
`G_{ab} + Λ g_{ab} = 8πG · T_{ab}` for some `Λ`.  This chains `clausius_equation_of_state` (for each
null `k`) into `einstein_equation_of_state`, so horizon thermodynamics **outputs** Einstein's
equation with Newton's constant fixed by the Unruh–Bekenstein arithmetic. -/
@[zil_level bridge_theorem]
theorem einstein_from_clausius {d : ℕ}
    (Ric T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (G κb T_U : ℝ)
    (hRic : Ric.IsSymm) (hT : T.IsSymm) (hG : G ≠ 0) (hκb : κb ≠ 0)
    (hUnruh : T_U = κb / (2 * Real.pi))
    (hClausius : ∀ k : (Fin 1 ⊕ Fin d) → ℝ, k ⬝ᵥ (η *ᵥ k) = 0 →
      κb * (k ⬝ᵥ (T *ᵥ k)) = T_U * ((k ⬝ᵥ (Ric *ᵥ k)) / (4 * G))) :
    ∃ Λ : ℝ, einsteinFieldEquationCosmological Ric (Matrix.trace (η * Ric)) η T Λ
      (8 * Real.pi * G) := by
  refine ⟨_, einstein_equation_of_state Ric T (8 * Real.pi * G) hRic hT (fun k hk => ?_)⟩
  exact clausius_equation_of_state G κb (k ⬝ᵥ (Ric *ᵥ k)) (k ⬝ᵥ (T *ᵥ k)) T_U hG hκb hUnruh
    (hClausius k hk)

/-- **Jacobson's equation of state with the local-constancy link closed.**
Besides the all-null-direction Clausius balance, assume the standard differential
inputs used by the repository's contracted-Bianchi argument: divergence-free
Einstein tensor, conserved matter stress, and the metric-compatible Leibniz rule
`Div (Lambda g) = grad Lambda`.  Then the cosmological scalar produced by
`einstein_from_clausius` has vanishing gradient. -/
@[zil_level bridge_theorem]
theorem einstein_from_clausius_with_local_cosmological_constancy {d : ℕ}
    (Ric T : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (G κb T_U : ℝ)
    (Div : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ →ₗ[ℝ]
      ((Fin 1 ⊕ Fin d) → ℝ))
    (gradCosmological : ℝ → (Fin 1 ⊕ Fin d) → ℝ)
    (hRic : Ric.IsSymm) (hT : T.IsSymm) (hG : G ≠ 0) (hκb : κb ≠ 0)
    (hUnruh : T_U = κb / (2 * Real.pi))
    (hClausius : ∀ k : (Fin 1 ⊕ Fin d) → ℝ, k ⬝ᵥ (η *ᵥ k) = 0 →
      κb * (k ⬝ᵥ (T *ᵥ k)) = T_U * ((k ⬝ᵥ (Ric *ᵥ k)) / (4 * G)))
    (hBianchi : Div (einsteinTensor Ric (Matrix.trace (η * Ric)) η) = 0)
    (hConservation : Div T = 0)
    (hMetricLeibniz : ∀ cosmologicalConstant : ℝ,
      Div (cosmologicalConstant • η) = gradCosmological cosmologicalConstant) :
    ∃ cosmologicalConstant : ℝ,
      einsteinFieldEquationCosmological Ric (Matrix.trace (η * Ric)) η T
        cosmologicalConstant (8 * Real.pi * G) ∧
      gradCosmological cosmologicalConstant = 0 := by
  obtain ⟨cosmologicalConstant, hEinstein⟩ :=
    einstein_from_clausius Ric T G κb T_U hRic hT hG hκb hUnruh hClausius
  refine ⟨cosmologicalConstant, hEinstein, ?_⟩
  exact cosmologicalConstant_gradient_zero_matrix Div Ric η T
    (cosmologicalConstant • η) (Matrix.trace (η * Ric)) cosmologicalConstant
    (8 * Real.pi * G) (gradCosmological cosmologicalConstant) hEinstein hBianchi
    hConservation (hMetricLeibniz cosmologicalConstant)

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein

zil attach area_secondDeriv_at_equilibrium where
  formalizes @ "claim:at-a-local-equilibrium-point-of-a-future-regular-null-horizon-congruence-with-vanishing-expansion-and-shear-the-horizon-area-second-derivative-equals-minus-the-null-ricci-contraction-times-the-area-the-area-deficit-is-governed-by-ricci-curvature",
  supported_by @ "lean:Physlib.Thermodynamics.FutureRegularNullRaychaudhuri.expansion_deriv_nonpos"

zil attach clausius_equation_of_state where
  formalizes @ "claim:the-clausius-relation-heat-flux-equals-unruh-temperature-times-bekenstein-entropy-variation-forces-the-gravitational-coupling-null-ricci-contraction-equals-eight-pi-g-times-null-stress-contraction-per-null-direction"

zil attach eq_of_integral_eq where
  supported_by @ "lean:clausius_equation_of_state",
  formalizes @ "claim:two-continuous-functions-whose-integrals-over-zero-to-t-agree-for-every-upper-limit-t-are-equal-the-fundamental-theorem-of-calculus-integral-stripping-lemma"

zil attach clausius_density_from_integrated where
  formalizes @ "claim:the-pointwise-density-form-clausius-relation-is-derived-from-the-integrated-clausius-relation-holding-over-every-horizon-patch-closing-the-integral-stripping-step-of-jacobsons-argument",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.JacobsonClausiusEinstein.eq_of_integral_eq"

zil attach einstein_from_clausius where
  formalizes @ "claim:if-the-per-direction-clausius-equation-of-state-holds-for-every-local-null-direction-then-the-einstein-field-equation-with-cosmological-term-holds-with-the-derived-coupling-eight-pi-g-horizon-thermodynamics-outputs-einsteins-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState.einstein_equation_of_state"

zil attach einstein_from_clausius_with_local_cosmological_constancy where
  formalizes @ "claim:the-cosmological-scalar-produced-by-the-all-null-direction-jacobson-clausius-equation-has-vanishing-gradient-under-contracted-bianchi-stress-conservation-and-metric-compatible-leibniz-inputs",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.CosmologicalConstantConstancy.cosmologicalConstant_gradient_zero_matrix",
  caveat @ "claim:vanishing-gradient-is-local-constancy-global-constancy-still-requires-connected-spacetime-differential-geometry"

zil_file_contract physlib.jacobsonClausiusEinstein where
  promises "Completing Jacobson's derivation of Einstein's equation from horizon thermodynamics. At a local equilibrium point of a future-regular null congruence with vanishing expansion and shear, the horizon cross-section area's second derivative equals minus the null Ricci contraction times the area, so the area deficit is governed by Ricci curvature via the null Raychaudhuri equation and the transport law A prime equals theta A. The Clausius relation, heat flux equals Unruh temperature times Bekenstein entropy variation with the shared kinematic factor cancelled, together with the Unruh temperature kappa over two pi, forces the gravitational coupling null Ricci contraction equals eight pi G times null stress contraction per null direction, the eight pi G being the product of the two pi of the Unruh temperature and the four G of the area-entropy law. Demanding this for every null direction and feeding it to the equation-of-state polarization yields the Einstein field equation with cosmological term and the derived coupling eight pi G. Under explicit contracted-Bianchi, stress-conservation, and metric-compatible Leibniz inputs, the cosmological scalar produced by that theorem has vanishing gradient and is therefore locally constant. Honest scope: the shared kinematic cancellation and boost-Killing flux and area-entropy identifications remain standard-GR inputs; promotion from vanishing gradient to one global constant requires connected-spacetime differential geometry."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.Thermodynamics.FutureRegularHorizonAreaEvolution",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinEquationOfState.einstein_equation_of_state",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean.einsteinFieldEquationCosmological"
  ]
  forbids_substitutes [
    "reading the per-direction Clausius density form as deriving the integral kinematic-factor cancellation, or reading vanishing cosmological gradient as global constancy without connected-spacetime differential geometry"
  ]
  witnessed_by [
    area_secondDeriv_at_equilibrium,
    clausius_equation_of_state,
    eq_of_integral_eq,
    clausius_density_from_integrated,
    einstein_from_clausius,
    einstein_from_clausius_with_local_cosmological_constancy
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.jacobsonClausiusEinstein
