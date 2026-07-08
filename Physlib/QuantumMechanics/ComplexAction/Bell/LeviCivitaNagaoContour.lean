/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaTensor
public import Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
public import Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian

/-!
# Bell no-signaling, Levi-Civita gravity, and the Nagao-Nielsen contour

This file links the Bell/CHSH no-signaling plus Levi-Civita tensor bridge to the
Nagao-Nielsen oscillator and contour infrastructure.

The common invariant is the Lorentzian convergence form

`lorentzianForm q = (Re q)^2 - (Im q)^2 = Re(q^2)`.

At unit mass, this is exactly the Nagao-Nielsen oscillator discriminant
`Re(1 * q^2)`.  Therefore a Bell spacelike point is not just outside the
45-degree cone: it is the inverted-harmonic-oscillator regime of
`ComplexOscillator.CausalRegimes`.  The permitted contour ray
`exp(i theta)` with `cos(2 theta) > 0` is the complementary harmonic-oscillator
regime.

The main theorem packages the resulting compatibility contract:

* the complex Einstein real sector gives the Levi-Civita d'Alembert balance;
* the imaginary sector gives `Lambda = kappa • S`;
* the Bell spacelike face is no-signaling and an inverted oscillator;
* the Nagao-Nielsen real contour is reversible/Kozak-even/zero entropic time;
* a permitted contour ray is the harmonic-oscillator side of the same phase diagram.
* the permitted ray also includes the actual Nagao-Nielsen contour integral
  normalization and Gaussian contour-independence lemmas.

No new axioms or new physics primitives are introduced.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaNagaoContour

open Physlib.QuantumMechanics.Entanglement
open Physlib.QuantumMechanics.ComplexAction.Bell.DeterministicBounds
open Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaTensor
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourGaussian
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.ContourShift
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FieldEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.PhaseDiagram
open Physlib.QuantumMechanics.ComplexAction.ComplexOscillator.CausalRegimes
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.KramersKronig.Parity
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.GravitationalTensor
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.NagaoKozakContourEntropicTime
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.EntropicTime
open MeasureTheory

variable {ι : Type*}

/-! ## §1 — Predicate and discriminator identifications -/

/-- The Bell/CHSH spacelike face and the future-included spacelike cone are the same
Lorentzian condition `lorentzianForm q < 0`, only exposed from two namespaces. -/
theorem bellSpacelike_iff_futureIncludedSpacelike (q : ℂ) :
    Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces.spacelike q
      ↔ Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian.spacelike q := by
  rfl

/-- At unit mass, the Nagao-Nielsen oscillator discriminant is the Lorentzian
convergence form. -/
theorem unitMassOscillatorDiscriminant_eq_lorentzian (ω : ℂ) :
    ((1 : ℂ) * ω ^ 2).re = lorentzianForm ω := by
  rw [one_mul, lorentzianForm_eq_re_sq]

/-- A Bell spacelike point is an inverted harmonic oscillator in the Nagao-Nielsen
complex-oscillator phase diagram. -/
theorem bellSpacelike_isInvertedOscillator
    (q : ℂ)
    (hq : Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces.spacelike q) :
    IsInvertedHarmonicOscillator 1 q := by
  have hsp : Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian.spacelike q :=
    (bellSpacelike_iff_futureIncludedSpacelike q).mp hq
  exact (spacelike_iff_isInvertedHarmonicOscillator q).mp hsp

/-- A permitted Nagao-Nielsen contour ray is on the harmonic-oscillator side of the
same causal phase diagram. -/
theorem permittedContourRay_isHarmonicOscillator (θ : ℝ)
    (hθ : 0 < Real.cos (2 * θ)) :
    IsHarmonicOscillator 1 (Complex.exp (θ * Complex.I)) := by
  have ht : Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian.timelike
      (Complex.exp (θ * Complex.I)) := by
    unfold Physlib.QuantumMechanics.ComplexAction.Rapidity.FutureIncludedLorentzian.timelike
    rw [Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Contour.lorentzianForm_rayDir]
    exact hθ
  exact (timelike_iff_isHarmonicOscillator _).mp ht

/-! ## §2 — Bell/Levi-Civita facts with oscillator meaning -/

/-- The complex Einstein real sector, Bell no-signaling, and the Nagao-Nielsen
inverted-oscillator regime are one compatible contract on a spacelike Bell face. -/
theorem complexEinstein_bellSpacelike_isInvertedOscillator
    (q : ℂ)
    (hq : Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces.spacelike q)
    (x : CHSHAssignment)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (κ : ℝ) (hκ : κ ≠ 0)
    (hComplex : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    T + gravitationalTensor Ric scalarR g κ = 0
      ∧ Λ = κ • S
      ∧ IsInvertedHarmonicOscillator 1 q
      ∧ |classicalCHSHValue x| ≤ 2
      ∧ chshExpression quantumCorrelation 0 (Real.pi / 2)
        (Real.pi / 4) (3 * Real.pi / 4) = tsirelsonWitness
      ∧ (2 : ℝ) < tsirelsonWitness
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂) := by
  have hLCBell :=
    complexEinstein_realSector_bell_no_signaling q hq x Ric scalarR g Λ T S κ hκ hComplex
  exact
    ⟨hLCBell.1,
      hLCBell.2.1,
      bellSpacelike_isInvertedOscillator q hq,
      hLCBell.2.2.2.1,
      hLCBell.2.2.2.2.1,
      hLCBell.2.2.2.2.2.1,
      hLCBell.2.2.2.2.2.2⟩

/-! ## §3 — Bell/Levi-Civita facts with the reversible Nagao-Nielsen contour -/

/-- Bell no-signaling and the Levi-Civita d'Alembert balance are compatible with the
Nagao-Nielsen/Kozak reversible real contour. -/
theorem leviCivita_bellNoSignaling_realContour_reversible
    (q : ℂ)
    (hq : Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces.spacelike q)
    (x : CHSHAssignment)
    (ξ : ℝ) (hξ : 0 < ξ) (ω : ℝ)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g T : Matrix ι ι ℝ)
    (κ : ℝ) (hκ : κ ≠ 0)
    (hEinstein : einsteinFieldEquation Ric scalarR g T κ) :
    T + gravitationalTensor Ric scalarR g κ = 0
      ∧ 0 ≤ lorentzianDispersion 0 ω
      ∧ FnEven (lorentzianDispersion 0)
      ∧ bogoliubovEntropicTime ξ 0 = 0
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂) := by
  have hLCBell :=
    leviCivita_dAlembert_bell_no_signaling q hq x Ric scalarR g T κ hκ hEinstein
  have hContour := real_contour_reversible ξ hξ ω
  exact
    ⟨hLCBell.1,
      hContour.1,
      hContour.2.1,
      hContour.2.2,
      hLCBell.2.2.2.2.2⟩

/-- Synthesis: the last Bell/Levi-Civita formalization now talks directly to
the Nagao-Nielsen contour and oscillator phase diagram. -/
theorem bellLeviCivita_nagaoContour_oscillator_synthesis
    (q : ℂ)
    (hq : Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces.spacelike q)
    (x : CHSHAssignment)
    (θ ξ ω : ℝ) (hθ : 0 < Real.cos (2 * θ)) (hξ : 0 < ξ)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (κ : ℝ) (hκ : κ ≠ 0)
    (hComplex : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    T + gravitationalTensor Ric scalarR g κ = 0
      ∧ Λ = κ • S
      ∧ IsInvertedHarmonicOscillator 1 q
      ∧ IsHarmonicOscillator 1 (Complex.exp (θ * Complex.I))
      ∧ FnEven (lorentzianDispersion 0)
      ∧ bogoliubovEntropicTime ξ 0 = 0
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂) := by
  have hEin :=
    complexEinstein_bellSpacelike_isInvertedOscillator q hq x Ric scalarR g Λ T S κ hκ hComplex
  have hContour := real_contour_reversible ξ hξ ω
  exact
    ⟨hEin.1,
      hEin.2.1,
      hEin.2.2.1,
      permittedContourRay_isHarmonicOscillator θ hθ,
      hContour.2.1,
      hContour.2.2,
      hEin.2.2.2.2.2.2⟩

/-! ## §4 — Bell/Levi-Civita facts with actual contour integrals -/

/--
Synthesis with the actual Nagao-Nielsen contour integral lemmas.

Compared with `bellLeviCivita_nagaoContour_oscillator_synthesis`, this theorem
adds the analytic content from the contour files:

* `contour_normalization`: the regularized complex delta normalizes to `1`
  along the permitted ray;
* `gaussianContourIntegral_indep`: the Gaussian contour integral is independent
  of the chosen permitted ray.
-/
theorem bellLeviCivita_nagaoContour_integral_synthesis
    (q : ℂ)
    (hq : Physlib.QuantumMechanics.ComplexAction.Bell.ThreeFaces.spacelike q)
    (x : CHSHAssignment)
    (θ θ' ξ ω ε c : ℝ) (hθ : |θ| < Real.pi / 4) (hθ' : |θ'| < Real.pi / 4)
    (hξ : 0 < ξ) (hε : 0 < ε) (hc : 0 < c)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (g Λ T S : Matrix ι ι ℝ)
    (κ : ℝ) (hκ : κ ≠ 0)
    (hComplex : complexEinsteinFieldEquation (einsteinTensor Ric scalarR g) Λ T S κ) :
    T + gravitationalTensor Ric scalarR g κ = 0
      ∧ Λ = κ • S
      ∧ IsInvertedHarmonicOscillator 1 q
      ∧ IsHarmonicOscillator 1 (Complex.exp (θ * Complex.I))
      ∧ FnEven (lorentzianDispersion 0)
      ∧ bogoliubovEntropicTime ξ 0 = 0
      ∧ (∀ δ₁ δ₂ : ℝ, bobMarginal δ₁ = bobMarginal δ₂)
      ∧ (∫ s : ℝ, deltaEpsC ε (Complex.exp (θ * Complex.I) * s) *
            Complex.exp (θ * Complex.I)) = 1
      ∧ (∫ s : ℝ, contourIntegrand (gaussH c) θ s)
          = (∫ s : ℝ, contourIntegrand (gaussH c) θ' s) := by
  have hθCone : 0 < Real.cos (2 * θ) := by
    rw [abs_lt] at hθ
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hEin :=
    complexEinstein_bellSpacelike_isInvertedOscillator q hq x Ric scalarR g Λ T S κ hκ hComplex
  have hContour := real_contour_reversible ξ hξ ω
  exact
    ⟨hEin.1,
      hEin.2.1,
      hEin.2.2.1,
      permittedContourRay_isHarmonicOscillator θ hθCone,
      hContour.2.1,
      hContour.2.2,
      hEin.2.2.2.2.2.2,
      contour_normalization hε hθ,
      gaussianContourIntegral_indep hc hθ hθ'⟩

end Physlib.QuantumMechanics.ComplexAction.Bell.LeviCivitaNagaoContour

end
