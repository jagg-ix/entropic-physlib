/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WittenJonesPolynomialChernSimons
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ThetaModular
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonOperators
public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
public import Physlib.QFT.PathIntegral.RigorousComplexFK
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas.ExactCoefficientForms

/-! # ABJMWilsonLoopsFermiGas — part `Recurrence`. Full paper docstring in the umbrella module `Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas`; namespace and
declaration names are unchanged across the parts (the umbrella re-exports them). -/

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
@[expose] public section
namespace Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas


/-- Right-hand side of the `U_n` recurrence in equation (5.14), with `dV` standing for `∂z V`. -/
noncomputable def abjmURecurrenceRHS
    (k : ℝ) (dV : ℕ → ℂ → ℂ) (V U : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  dV (n - 1) z
    - (1 / (4 * (Real.pi : ℂ) * (k : ℂ)))
      * (∑ m ∈ Finset.Icc 1 (n - 1),
          V (n - m - 1) (((-1 : ℂ) ^ m) * z) * U m z
        )

/-- For `n = 1`, the recurrence sum is empty and `U₁ = ∂z V₀`, as in equation (5.13). -/
lemma abjmURecurrenceRHS_one
    (k : ℝ) (dV : ℕ → ℂ → ℂ) (V U : ℕ → ℂ → ℂ) (z : ℂ) :
    abjmURecurrenceRHS k dV V U 1 z = dV 0 z := by
  simp [abjmURecurrenceRHS]

/-- For `n = 2`, equation (5.14) specializes to one convolution term. -/
lemma abjmURecurrenceRHS_two
    (k : ℝ) (dV : ℕ → ℂ → ℂ) (V U : ℕ → ℂ → ℂ) (z : ℂ) :
    abjmURecurrenceRHS k dV V U 2 z =
      dV 1 z
        - (1 / (4 * (Real.pi : ℂ) * (k : ℂ))) * (V 0 ((-1 : ℂ) * z) * U 1 z) := by
  simp [abjmURecurrenceRHS]

/-- Right-hand side of the `I_n` recurrence in equation (5.14). -/
noncomputable def abjmIRecurrenceRHS
    (k : ℝ) (psi : ℂ → ℂ → ℂ) (I : ℕ → ℂ → ℂ → ℂ) (U : ℕ → ℂ → ℂ)
    (n : ℕ) (y z : ℂ) : ℂ :=
  Complex.exp (y / (k : ℂ)) * I (n - 1) y z
    + (-1 : ℂ) ^ (n - 1) * z * psi y (((-1 : ℂ) ^ n) * z) * U (n - 1) z

/-- For `n = 1`, the recurrence has the printed `I₀/U₀` specialization. -/
lemma abjmIRecurrenceRHS_one
    (k : ℝ) (psi : ℂ → ℂ → ℂ) (I : ℕ → ℂ → ℂ → ℂ) (U : ℕ → ℂ → ℂ) (y z : ℂ) :
    abjmIRecurrenceRHS k psi I U 1 y z =
      Complex.exp (y / (k : ℂ)) * I 0 y z + z * psi y ((-1 : ℂ) * z) * U 0 z := by
  simp [abjmIRecurrenceRHS]

/-- Closed iterated form (5.15), with `I₁` and the `U_m` recurrence values supplied. -/
noncomputable def abjmIClosedFromI1AndU
    (k : ℝ) (psi : ℂ → ℂ → ℂ) (I1 : ℂ → ℂ → ℂ) (U : ℕ → ℂ → ℂ)
    (n : ℕ) (y z : ℂ) : ℂ :=
  Complex.exp (y * ((n : ℂ) - 1) / (k : ℂ)) * I1 y z
    + z * ∑ m ∈ Finset.Icc 1 (n - 1),
        (-1 : ℂ) ^ m * Complex.exp (y * ((n : ℂ) - 1 - (m : ℂ)) / (k : ℂ))
          * psi y (((-1 : ℂ) ^ (m + 1)) * z) * U m z

/-- Appendix C potential identities and Appendix D recurrences, packaged as explicit obligations. -/
structure ABJMPotentialRecurrenceCarrier where
  level : ℝ
  V : ℕ → ℕ → ℂ → ℂ
  V0 : ℕ → ℂ → ℂ
  dV0 : ℕ → ℂ → ℂ
  U : ℕ → ℂ → ℂ
  I : ℕ → ℂ → ℂ → ℂ
  I1 : ℂ → ℂ → ℂ
  psi : ℂ → ℂ → ℂ
  V_symm : ∀ n m z, V n m z = V m n z
  V0_eq : ∀ n z, V0 n z = V n 0 z
  V_relation :
    ∀ n m z,
      V n (m + 1) (-z) + V (n + 1) m z =
        V n 0 (-z) * V 0 m z / (4 * (Real.pi : ℂ) * (level : ℂ))
  U_zero : ∀ z, U 0 z = 4 * (Real.pi : ℂ) * (level : ℂ) * dV0 0 z
  U_recurrence : ∀ n z, U n z = abjmURecurrenceRHS level dV0 V0 U n z
  I_one : ∀ y z, I 1 y z = I1 y z
  I_recurrence : ∀ n y z, I n y z = abjmIRecurrenceRHS level psi I U n y z
  I_closed : ∀ n y z, I n y z = abjmIClosedFromI1AndU level psi I1 U n y z

/-- **[Appendix C, equation (C.2)]** Potential matrix elements reduce by the quadratic relation. -/
lemma ABJMPotentialRecurrenceCarrier.potential_relation_eq
    (P : ABJMPotentialRecurrenceCarrier) (n m : ℕ) (z : ℂ) :
    P.V n (m + 1) (-z) + P.V (n + 1) m z =
      P.V n 0 (-z) * P.V 0 m z / (4 * (Real.pi : ℂ) * (P.level : ℂ)) :=
  P.V_relation n m z

/-- **[Equation (5.15)]** The iterated `I_n` solution is obtained from `I₁` and the `U_m`. -/
lemma ABJMPotentialRecurrenceCarrier.I_eq_closed
    (P : ABJMPotentialRecurrenceCarrier) (n : ℕ) (y z : ℂ) :
    P.I n y z = abjmIClosedFromI1AndU P.level P.psi P.I1 P.U n y z :=
  P.I_closed n y z


/-- **ABJM Wilson observables use the existing rigorous complex FK lane.**  Once an ABJM Wilson observable
is supplied as a `WittenAnalyticPathIntegral` observable, Lean checks the same Bochner integrability and
norm bound as for the Witten/Jones construction. -/
lemma abjm_wilsonLoop_rigorousFK_bridge
    {Path Loop : Type*} [MeasurableSpace Path]
    (W : WittenAnalyticPathIntegral Path Loop) (L : Loop) :
    Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction :=
  W.rigorousComplexFK L

/-- **ABJM Wilson loops link to CSW level quantization and theta periodicity.**  This packages the
Wilson-loop FK obligation with the existing integer-level theta modularity used by the CSW torus sector. -/
lemma abjm_wilsonLoop_csw_theta_bridge
    {Path Loop : Type*} [MeasurableSpace Path]
    (W : WittenAnalyticPathIntegral Path Loop) (L : Loop)
    (c : HayashiCouplings) (τ z : ℂ) :
    (Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction)
      ∧ (holomorphicCoupling c + antiholomorphicCoupling c) / 2 = (c.level : ℂ)
      ∧ cswTheta (c.level : ℂ) (τ + 2) z = cswTheta (c.level : ℂ) τ z
      ∧ cswTheta (c.level : ℂ) τ (z + 1) = cswTheta (c.level : ℂ) τ z :=
  ⟨W.rigorousComplexFK L, witten_jones_integer_level_theta_periodicities c τ z⟩

/-- **ABJM Wilson/Fermi-gas layer linked to the repo's Bose-bilinear fermion-field bridge.**  The paper's
Fermi-gas and superconnection language can be carried alongside the existing Kálnay statement that the
fermion-field generators are represented by Bose-bilinear words satisfying the CAR. -/
lemma abjm_wilsonLoop_kalnay_fermion_bridge
    {Path Loop : Type*} [MeasurableSpace Path] {n k : ℕ}
    (W : WittenAnalyticPathIntegral Path Loop) (L : Loop)
    (c : HayashiCouplings) (lam ω e : ℂ) (Λ : ℝ) (hΛ : Λ < 0)
    (HR HI : ℝ) (χ : Fin k → ℂ)
    (P : LocalCSConnection n × LocalCSConnection n) (ψ : ℂ)
    (Ψ φ : Fin k × Fin k) (O : Fin k) (p : Momentum 3) (hcharge : Ψ ≠ φ) :
    (Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction)
      ∧ KalnayBoseFermiFieldStatement p :=
  witten_analytic_concreteCSW_kalnay_field_bridge
    W L c lam ω e Λ hΛ HR HI χ P ψ Ψ φ O p hcharge

/-- **ABJM Wilson/Fermi-gas layer linked to the full item-9 CSW package and Kálnay.**  This is the
consumer theorem for the ABJM file: once an ABJM Wilson observable is supplied in the Witten analytic
path-integral lane, the existing repo theorem gives FK control, Poisson/theta resummation, Verlinde fusion,
Wilson/Verlinde diagonalization, torus geometric quantization, and Bose-bilinear fermion fields together. -/
lemma abjm_wilsonLoop_item9_kalnay_fermion_bridge
    {Path Loop : Type*} [MeasurableSpace Path] {n k : ℕ} (hk : 0 < k)
    (W : WittenAnalyticPathIntegral Path Loop) (L : Loop)
    (c : HayashiCouplings) (lam ω e : ℂ) (Λ : ℝ) (hΛ : Λ < 0)
    (HR HI : ℝ) (χ : Fin k → ℂ)
    (P : LocalCSConnection n × LocalCSConnection n) (ψ : ℂ)
    (Ψ φ : Fin k × Fin k) (O : Fin k) (p : Momentum 3) (hcharge : Ψ ≠ φ)
    (G : CSWGeometricQuantizationPackage k hk) :
    (Integrable (fun A => W.wilsonObservable L A * W.model.weight A) W.model.μ ∧
      ‖W.wilsonIntegral L‖ ≤ W.wilsonBound L * W.partitionFunction)
      ∧ (∀ τ z a,
        cswThetaBasis k a (-1 / τ) z =
          ∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z)
      ∧ (∀ a b c,
        cswFusionCoeff k a b c = cswVerlindeCoefficientByS k hk a b c)
      ∧ (∀ a q,
        cswWilsonVerlindeOperator k a (fun b => cswSMatrix k b q) =
          fun c => cswVerlindeEigenvalue k hk a q * cswSMatrix k c q)
      ∧ Module.finrank ℂ (TorusHilbert k) = k
      ∧ KalnayBoseFermiFieldStatement p :=
  witten_analytic_concreteCSW_item9_kalnay_field_bridge
    hk W L c lam ω e Λ hΛ HR HI χ P ψ Ψ φ O p hcharge G


end Physlib.QuantumMechanics.ComplexAction.ABJMWilsonLoopsFermiGas

end
