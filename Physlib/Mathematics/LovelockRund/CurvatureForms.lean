/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.LovelockRund.DifferentialForms
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiFromConnection

/-!
# Curvature forms and Bianchi identities

This module formalizes the differential-form curvature layer of
Lovelock--Rund Sections 5.6 and 7.3. The connection and curvature forms are
built on Mathlib's existing exterior derivative. The abelian or linearized
Cartan curvature is `Ω = dω`, so its Bianchi identity is exactly `d²ω = 0`.

The model space is arbitrary and may be infinite dimensional. The connection
index type is also arbitrary; no `Fintype` assumption is needed for the
componentwise curvature family.

For the nonabelian component identity and its contracted conservation
consequence, the module reuses Physlib's existing
`SecondBianchiCyclicFamily` API instead of introducing a parallel curvature
calculus.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.Mathematics.LovelockRund

open Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.BianchiValidation

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {r : WithTop ℕ∞}

/-- A connection 1-form on an arbitrary normed model space. -/
abbrev ConnectionOneForm := DifferentialForm 𝕜 E F 1

/-- A curvature 2-form on an arbitrary normed model space. -/
abbrev CurvatureTwoForm := DifferentialForm 𝕜 E F 2

/-- Abelian or linearized Cartan curvature `Ω = dω`. -/
def abelianCurvature (ω : ConnectionOneForm (𝕜 := 𝕜) (E := E) (F := F)) :
    CurvatureTwoForm (𝕜 := 𝕜) (E := E) (F := F) :=
  extDeriv ω

/-- Differential Bianchi identity for abelian or linearized curvature. -/
theorem abelianCurvature_bianchi
    {ω : ConnectionOneForm (𝕜 := 𝕜) (E := E) (F := F)}
    (hω : ContDiff 𝕜 r ω) (hr : minSmoothness 𝕜 2 ≤ r) :
    extDeriv (abelianCurvature ω) = 0 := by
  exact extDeriv_extDeriv hω hr

/-- Curvature commutes pointwise with pullback. -/
theorem abelianCurvature_pullback
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {ω : ConnectionOneForm (𝕜 := 𝕜) (E := E) (F := F)}
    {f : G → E} {x : G}
    (hω : DifferentiableAt 𝕜 ω (f x))
    (hf : ContDiffAt 𝕜 r f x)
    (hr : minSmoothness 𝕜 2 ≤ r) :
    abelianCurvature (pullbackForm ω f) x =
      (abelianCurvature ω (f x)).compContinuousLinearMap
        (fderiv 𝕜 f x) := by
  exact extDeriv_pullbackForm hω hf hr

/-- A connection one-form carrying two arbitrary bundle indices. The index
type may be infinite. -/
abbrev IndexedConnectionOneForm (ι : Type*) :=
  ι → ι → ConnectionOneForm (𝕜 := 𝕜) (E := E) (F := F)

/-- Componentwise abelian curvature of an indexed connection family. -/
def indexedCurvature {ι : Type*}
    (ω : IndexedConnectionOneForm (𝕜 := 𝕜) (E := E) (F := F) ι) :
    ι → ι → CurvatureTwoForm (𝕜 := 𝕜) (E := E) (F := F) :=
  fun a b => extDeriv (ω a b)

/-- Componentwise Bianchi identity for an arbitrary, possibly infinite,
connection-index family. -/
theorem indexedCurvature_bianchi
    {ι : Type*}
    {ω : IndexedConnectionOneForm (𝕜 := 𝕜) (E := E) (F := F) ι}
    (hω : ∀ a b, ContDiff 𝕜 r (ω a b))
    (hr : minSmoothness 𝕜 2 ≤ r) :
    ∀ a b, extDeriv (indexedCurvature ω a b) = 0 := by
  intro a b
  exact extDeriv_extDeriv (hω a b) hr

/-- Explicit component form of the second Bianchi cyclic identity, reusing the
existing Physlib curvature API. -/
theorem secondBianchi_explicit
    {κ : Type*} (D : κ → κ → κ → κ → κ → ℝ)
    (hD : SecondBianchi D) :
    ∀ a b c d e,
      D a b c d e + D a b d e c + D a b e c d = 0 :=
  hD

/-- The component second Bianchi identity together with its contracted form
forces source conservation through the Einstein field equation. -/
theorem secondBianchi_implies_conservation
    {κ : Type*}
    (D : κ → κ → κ → κ → κ → ℝ)
    (hD : SecondBianchi D)
    {ι : Type*} [Fintype ι]
    (divRicci gradScalar divT : ι → ℝ)
    (kappa : ℝ) (hkappa : kappa ≠ 0)
    (hField :
      einsteinDivergence divRicci gradScalar = (-kappa) • divT)
    (hContracted : contractedSecondBianchi divRicci gradScalar) :
    (∀ a b c d e,
      D a b c d e + D a b d e c + D a b e c d = 0) ∧
      divT = 0 :=
  second_bianchi_cyclic_and_conservation
    D hD divRicci gradScalar divT kappa hkappa hField hContracted

end Physlib.Mathematics.LovelockRund

end
