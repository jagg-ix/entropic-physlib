/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.GreenFunction
public import Physlib.QuantumMechanics.NonHermitian.Propagator
public import Physlib.QFT.PathIntegral.Lorentzian
public import Physlib.QFT.PathIntegral.MeasureExpectation

/-!
# Causal Green functions and the Feynman propagator of the Sorkin–Johnston vacuum

The Sorkin–Johnston construction takes as input the **Pauli–Jordan** function `Δ`, which is itself
built from the causal (advanced/retarded) Green functions of the field: `Δ = G_ret − G_adv`. This
module supplies that construction — turning a causal ordering on the region into a Pauli–Jordan
kernel — and the associated **time-ordered (Feynman)** propagator, extending
`SorkinJohnstonRegionState`.

Given a symmetric Green kernel `G(x,y) = G(y,x)` and a causal order `later x y` ("`x` is to the future
of `y`"):

 `G_ret(x,y) = [later x y] G(x,y)` (future-supported), `G_adv(x,y) = [later y x] G(x,y)`
 (past-supported), `Δ = G_ret − G_adv`.

The difference `Δ` is **automatically antisymmetric** — a Pauli–Jordan function — for *any* causal
order, needing only `G` symmetric. Feeding it to `SorkinJohnstonRegionState` yields an SJ state.

* **§A — advanced/retarded Green functions.** `retardedGreen`, `advancedGreen`, and their difference
 `causalPauliJordan`.
* **§B — the Pauli–Jordan function from causality.** `causalPauliJordan_isPauliJordan`: `G_ret − G_adv`
 is antisymmetric for any causal order (given `G` symmetric) — the `Δ`-from-Green-functions step.
* **§C — the Feynman (time-ordered) propagator.** `feynmanTwoPoint` (`T`-ordered two-point);
 `feynman_symm` (the `T`-product is symmetric under a strict causal order) and
 `feynman_wightman_pauliJordan` (`G_F − W = −iΔ` off the future cone, the `iε` structure).
* **§D — the SJ state from causal data.** `causalGreen_sjState`: the causal Green functions determine a
 Sorkin–Johnston state (reusing `wightman_isSJState`).
* **§E — complex-action bridge.** The same causal/Feynman two-point kernel is connected to the
 existing complex Schrödinger propagator, the scalar complex Green kernel `greenKernel`, the
 Lorentzian path-integral kernel, and the source-coupled path-integral two-point functional.

Proven: the antisymmetry of `G_ret − G_adv`, the symmetry of the time-ordered
propagator, the Feynman−Wightman relation, and the end-to-end SJ state from causal data. Interpretive:
`later` is the abstract causal order of the region (the datum standing for `x ∈ J⁺(y)`); `G` is the
symmetric Green kernel; the integrals are represented by their kernels.

## References

* R. D. Sorkin, "Scalar field theory on a causal set in histories form", J. Phys. Conf. Ser. 306,
 012017 (2011); S. Johnston, "Feynman propagator for a free scalar field on a causal set", PRL 103,
 180401 (2009). Reuses `SorkinJohnstonRegionState` (`IsPauliJordan`, `IsSymmetricKernel`,
 `wightmanTwoPoint`, `wightman_commutator`, `IsSJState`, `wightman_isSJState`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen

open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.NonHermitian.Propagator
open Physlib.QFT.PathIntegral

variable {α : Type*}

/-! ## §A — advanced/retarded Green functions -/

/-- **The retarded Green two-point** `G_ret(x,y) = [x later than y] G(x,y)`: supported when `x` is to the
future of `y`. -/
def retardedGreen (G : α → α → ℝ) (later : α → α → Prop) [DecidableRel later] (x y : α) : ℝ :=
  if later x y then G x y else 0

/-- **The advanced Green two-point** `G_adv(x,y) = [y later than x] G(x,y)`: supported when `x` is to the
past of `y`. -/
def advancedGreen (G : α → α → ℝ) (later : α → α → Prop) [DecidableRel later] (x y : α) : ℝ :=
  if later y x then G x y else 0

/-- **The causal Pauli–Jordan kernel** `Δ = G_ret − G_adv`. -/
def causalPauliJordan (G : α → α → ℝ) (later : α → α → Prop) [DecidableRel later] (x y : α) : ℝ :=
  retardedGreen G later x y - advancedGreen G later x y

/-! ## §B — the Pauli–Jordan function from causality -/

/-- **`G_ret − G_adv` is a Pauli–Jordan function** (antisymmetric): for *any* causal order `later`, the
difference of the retarded and advanced Green functions of a symmetric kernel `G` is antisymmetric
`Δ(x,y) = −Δ(y,x)`. This is the causal construction of the Pauli–Jordan input to the SJ vacuum. -/
theorem causalPauliJordan_isPauliJordan (G : α → α → ℝ) (later : α → α → Prop) [DecidableRel later]
    (hG : IsSymmetricKernel G) :
    IsPauliJordan (causalPauliJordan G later) := by
  intro x y
  unfold causalPauliJordan retardedGreen advancedGreen
  rw [hG y x]
  split_ifs <;> ring

/-! ## §C — the Feynman (time-ordered) propagator -/

/-- **The Feynman (time-ordered) two-point** `G_F(x,y) = ⟨T φ(x)φ(y)⟩`: the two-point function with the
later argument's operator to the left. -/
noncomputable def feynmanTwoPoint (W : α → α → ℂ) (later : α → α → Prop) [DecidableRel later]
    (x y : α) : ℂ :=
  if later x y then W x y else W y x

/-- **The time-ordered propagator is symmetric** `G_F(x,y) = G_F(y,x)`: the `T`-product is symmetric, as
long as the causal order is strict (asymmetric) and total on the pair. -/
theorem feynman_symm (W : α → α → ℂ) (later : α → α → Prop) [DecidableRel later] (x y : α)
    (hasym : ∀ a b, later a b → ¬ later b a) (htot : later x y ∨ later y x) :
    feynmanTwoPoint W later x y = feynmanTwoPoint W later y x := by
  unfold feynmanTwoPoint
  rcases htot with h | h
  · rw [if_pos h, if_neg (hasym _ _ h)]
  · rw [if_neg (hasym _ _ h), if_pos h]

/-- **The Feynman−Wightman relation** `G_F(x,y) − W(x,y) = −iΔ(x,y)` off the future cone (`¬ later x y`),
and `0` on it: the time-ordered propagator differs from the Wightman function by the Pauli–Jordan
commutator in the past direction — the `iε`/contour structure of the Feynman propagator. -/
theorem feynman_wightman_pauliJordan (A Δ : α → α → ℝ) (later : α → α → Prop) [DecidableRel later]
    (hA : IsSymmetricKernel A) (hΔ : IsPauliJordan Δ) (x y : α) :
    feynmanTwoPoint (wightmanTwoPoint A Δ) later x y - wightmanTwoPoint A Δ x y
      = if later x y then 0 else - (Complex.I * ((Δ x y : ℝ) : ℂ)) := by
  unfold feynmanTwoPoint
  split_ifs with h
  · ring
  · have hc := wightman_commutator A Δ hA hΔ x y
    linear_combination -hc

/-! ## §D — the SJ state from causal data -/

/-- **The causal Green functions determine a Sorkin–Johnston state**: from a symmetric Green kernel `G`,
a causal order, and a positive Hadamard part `A`, the Wightman function over the causal Pauli–Jordan
kernel `G_ret − G_adv` is an SJ state — the region vacuum built end-to-end from causal data. -/
theorem causalGreen_sjState (G A : α → α → ℝ) (later : α → α → Prop) [DecidableRel later]
    (hG : IsSymmetricKernel G) (hA : IsSymmetricKernel A) (hApos : ∀ x, 0 ≤ A x x) :
    IsSJState (wightmanTwoPoint A (causalPauliJordan G later)) (causalPauliJordan G later) :=
  wightman_isSJState A (causalPauliJordan G later) hA
    (causalPauliJordan_isPauliJordan G later hG) hApos

/-! ## §E — Link to complex Schrödinger and complex Green functionals -/

/-- **Scalar bridge.** The complex spectral Green kernel `greenKernel` for the eigenvalue
`λ = H_R - i H_I` is exactly the Lorentzian scalar propagator of the complex Hamiltonian
`H_C = H_R - i H_I`. This identifies the causal/Feynman two-point kernel's scalar
building block with the repo's complex-action path-integral propagator. -/
theorem greenKernel_eq_lorentzianPropagator (H_R H_I ℏ t : ℝ) (hI : 0 ≤ H_I) :
    greenKernel (((H_R : ℂ) - Complex.I * (H_I : ℂ))) ℏ t =
      lorentzianPropagator
        ({ H_R := H_R, H_I := H_I, H_I_nonneg := hI } : ComplexHamiltonian) t ℏ := by
  unfold greenKernel lorentzianPropagator lorentzianKernel
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The modulus of the complex spectral Green kernel is the modulus of the Lorentzian
complex-action propagator with the same `(H_R,H_I)`. -/
theorem norm_greenKernel_eq_lorentzianPropagator (H_R H_I ℏ t : ℝ) (hI : 0 ≤ H_I) :
    ‖greenKernel (((H_R : ℂ) - Complex.I * (H_I : ℂ))) ℏ t‖ =
      ‖lorentzianPropagator
        ({ H_R := H_R, H_I := H_I, H_I_nonneg := hI } : ComplexHamiltonian) t ℏ‖ := by
  rw [greenKernel_eq_lorentzianPropagator H_R H_I ℏ t hI]

/-- Operator bridge: the non-Hermitian Green operator `U(t) = exp(tG)` is the operator
propagator that solves the complex Schrödinger equation `iℏ ∂_t U = H_C U`. -/
theorem complexSchrodinger_greenOperator_equation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (H_C : H →L[ℂ] H) (hbar : ℝ) (hbar0 : hbar ≠ 0) (t : ℝ) :
    (Complex.I * (hbar : ℂ)) •
        (schrodingerGenerator H_C hbar * propagator H_C hbar t)
      = H_C * propagator H_C hbar t :=
  nonHermitian_schrodinger_operator H_C hbar hbar0 t

/-- A complex spectral two-point kernel built from the existing scalar Green kernel. -/
noncomputable def complexSpectralTwoPoint (lam : α → α → ℂ) (time : α → α → ℝ)
    (ℏ : ℝ) : α → α → ℂ :=
  fun x y => greenKernel (lam x y) ℏ (time x y)

/-- Time-ordering the complex spectral two-point kernel gives the Sorkin-Johnston/Feynman
two-point form with the complex Green kernel as its underlying Wightman block. -/
theorem feynmanTwoPoint_complexSpectralTwoPoint (lam : α → α → ℂ) (time : α → α → ℝ)
    (ℏ : ℝ) (later : α → α → Prop) [DecidableRel later] (x y : α) :
    feynmanTwoPoint (complexSpectralTwoPoint lam time ℏ) later x y =
      if later x y then greenKernel (lam x y) ℏ (time x y)
      else greenKernel (lam y x) ℏ (time y x) := by
  unfold feynmanTwoPoint complexSpectralTwoPoint
  split_ifs <;> rfl

/-- Path-integral two-point kernel: evaluate the existing complex path-integral model's
two-point correlation on two field insertions. -/
noncomputable def pathIntegralTwoPointKernel {Ω X : Type*} [MeasurableSpace Ω]
    (m : MeasurePathIntegralModel Ω) (field : X → Ω → ℂ) : X → X → ℂ :=
  fun x y => m.twoPointCorrelation (field x) (field y)

/-- The causal/Feynman kernel obtained from a complex path-integral two-point functional is
just the existing Sorkin-Johnston time-ordering applied to that two-point kernel. -/
noncomputable def pathIntegralFeynmanKernel {Ω X : Type*} [MeasurableSpace Ω]
    (m : MeasurePathIntegralModel Ω) (field : X → Ω → ℂ)
    (later : X → X → Prop) [DecidableRel later] : X → X → ℂ :=
  feynmanTwoPoint (pathIntegralTwoPointKernel m field) later

/-- Expands the previous definition: the Feynman kernel is the later insertion's
path-integral two-point correlation, otherwise the reversed correlation. -/
theorem pathIntegralFeynmanKernel_apply {Ω X : Type*} [MeasurableSpace Ω]
    (m : MeasurePathIntegralModel Ω) (field : X → Ω → ℂ)
    (later : X → X → Prop) [DecidableRel later] (x y : X) :
    pathIntegralFeynmanKernel m field later x y =
      if later x y then m.twoPointCorrelation (field x) (field y)
      else m.twoPointCorrelation (field y) (field x) := by
  unfold pathIntegralFeynmanKernel pathIntegralTwoPointKernel feynmanTwoPoint
  split_ifs <;> rfl

/-- The connected Green functional at zero source is the logarithm of the existing complex
path-integral partition functional. -/
theorem connectedGreenFunctional_zero {Ω : Type*} [MeasurableSpace Ω]
    (m : MeasurePathIntegralModel Ω) :
    m.connectedGeneratingFunctional (fun _ => (0 : ℂ)) = Complex.log m.partition :=
  m.connectedGeneratingFunctional_zero

/-- Repository-facing package: causal Green functions, Feynman time-ordering, complex
Schrödinger evolution, scalar complex Green kernels, and the path-integral two-point
functional are mutually linked by the existing APIs. -/
def HasCausalGreenComplexSchrodingerFunctionalBridge : Prop :=
  (∀ (H_R H_I ℏ t : ℝ) (hI : 0 ≤ H_I),
      greenKernel (((H_R : ℂ) - Complex.I * (H_I : ℂ))) ℏ t =
        lorentzianPropagator
          ({ H_R := H_R, H_I := H_I, H_I_nonneg := hI } : ComplexHamiltonian) t ℏ)
    ∧ (∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [FiniteDimensional ℂ H]
        (H_C : H →L[ℂ] H) (hbar : ℝ), hbar ≠ 0 → ∀ t : ℝ,
        (Complex.I * (hbar : ℂ)) •
            (schrodingerGenerator H_C hbar * propagator H_C hbar t)
          = H_C * propagator H_C hbar t)
    ∧ (∀ {Ω X : Type*} [MeasurableSpace Ω]
        (m : MeasurePathIntegralModel Ω) (field : X → Ω → ℂ)
        (later : X → X → Prop) [DecidableRel later] (x y : X),
        pathIntegralFeynmanKernel m field later x y =
          if later x y then m.twoPointCorrelation (field x) (field y)
          else m.twoPointCorrelation (field y) (field x))
    ∧ (∀ {Ω : Type*} [MeasurableSpace Ω] (m : MeasurePathIntegralModel Ω),
        m.connectedGeneratingFunctional (fun _ => (0 : ℂ)) = Complex.log m.partition)

/-- The causal Green/Feynman layer is linked to the complex Schrödinger and complex
Green-functional layers. -/
theorem causalGreen_complexSchrodinger_functional_bridge_checked :
    HasCausalGreenComplexSchrodingerFunctionalBridge := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H_R H_I ℏ t hI
    exact greenKernel_eq_lorentzianPropagator H_R H_I ℏ t hI
  · intro H _ _ _ _ H_C hbar hbar0 t
    exact complexSchrodinger_greenOperator_equation H_C hbar hbar0 t
  · intro Ω X _ m field later _ x y
    exact pathIntegralFeynmanKernel_apply m field later x y
  · intro Ω _ m
    exact connectedGreenFunctional_zero m

end Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonCausalGreen
