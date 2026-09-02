/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Mathematics.HarmonicAnalysis.SobolevHeatSemigroupDuhamel
meta import Zil

/-!
# Finite spectral heat flow

OpenWave's thermal criterion evolves finitely many periodic Fourier modes by the
exact multiplier `exp (-κ λᵢ t)`. This file formalizes that finite spectral
semigroup, its identity and composition laws, preservation of the zero mode,
and the zero-diffusivity limit.

The file does not claim a microscopic derivation of thermodynamics or the full
measure-theoretic heat kernel on an arbitrary continuum carrier.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow

/-- Exact heat evolution of a finite or arbitrary family of spectral
coefficients with nonnegative Laplacian eigenvalues supplied separately. -/
noncomputable def flow {ι : Type*}
    (κ : ℝ) (lam : ι → ℝ) (t : ℝ) (u : ι → ℝ) : ι → ℝ :=
  fun i => Real.exp (-κ * lam i * t) * u i

@[simp] theorem flow_apply {ι : Type*}
    (κ : ℝ) (lam : ι → ℝ) (t : ℝ) (u : ι → ℝ) (i : ι) :
    flow κ lam t u i = Real.exp (-κ * lam i * t) * u i := rfl

/-- Time zero is the identity. -/
@[simp] theorem flow_zero {ι : Type*}
    (κ : ℝ) (lam : ι → ℝ) (u : ι → ℝ) :
    flow κ lam 0 u = u := by
  funext i
  simp [flow]

/-- Exact semigroup composition. -/
theorem flow_add {ι : Type*}
    (κ : ℝ) (lam : ι → ℝ) (s t : ℝ) (u : ι → ℝ) :
    flow κ lam (s + t) u = flow κ lam s (flow κ lam t u) := by
  funext i
  rw [flow_apply, flow_apply, flow_apply]
  rw [show -κ * lam i * (s + t) =
      (-κ * lam i * s) + (-κ * lam i * t) by ring,
    Real.exp_add]
  ring

/-- Zero diffusivity freezes every mode. -/
@[simp] theorem flow_zero_diffusivity {ι : Type*}
    (lam : ι → ℝ) (t : ℝ) (u : ι → ℝ) :
    flow 0 lam t u = u := by
  funext i
  simp [flow]

/-- Every zero-eigenvalue mode is exactly conserved. This is the spectral
statement behind conservation of total heat on a periodic grid. -/
theorem flow_preserves_zero_mode {ι : Type*}
    (κ : ℝ) (lam : ι → ℝ) (t : ℝ) (u : ι → ℝ) (i : ι)
    (hi : lam i = 0) :
    flow κ lam t u i = u i := by
  simp [flow, hi]

end Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow

/- ZIL-BEGIN -/

zil attach Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow.flow_add where
  supported_by @ "lean:Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow.flow_apply",
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:the-finite-spectral-heat-evolution-is-an-exact-semigroup"

zil attach Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow.flow_preserves_zero_mode where
  formalizes @ "claim:the-zero-laplacian-mode-is-conserved-by-the-finite-spectral-heat-flow",
  caveat @ "claim:this-is-the-spectral-total-heat-conservation-identity-not-a-microscopic-thermodynamic-derivation"

zil attach Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow.flow_zero_diffusivity where
  supported_by @ "lean:CPTPMap.funext",
  formalizes @ "claim:zero-diffusivity-freezes-every-spectral-mode"

zil_file_contract physlib.m9.finiteSpectralHeatFlow where
  promises "The exact finite spectral heat multiplier, identity and semigroup laws, zero-mode conservation, and zero-diffusivity limit used by the OpenWave periodic thermal solver."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects []
  forbids_substitutes ["a microscopic thermodynamic derivation of heat conduction, these are the exact spectral-multiplier identities",
    "continuum heat-equation well-posedness, only the finite spectral multiplier with its semigroup and conservation laws is proven"]
  witnessed_by [
    Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow.flow_zero,
    Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow.flow_add,
    Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow.flow_zero_diffusivity,
    Physlib.Mathematics.HarmonicAnalysis.FiniteSpectralHeatFlow.flow_preserves_zero_mode ]

/- ZIL-END -/
