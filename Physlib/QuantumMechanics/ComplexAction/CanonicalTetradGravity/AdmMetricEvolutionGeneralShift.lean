/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse
public import Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# The ADM spatial-metric evolution with a general shift

`ExtrinsicCurvatureTracelessTransverse` supplied the general extrinsic curvature and the
transverse-traceless mode. The third piece the inspection named — **general shift dynamics** — is the
shift's contribution to the ADM evolution equation. The shift `N^i` enters the spatial-metric
evolution through the **Lie derivative** of `γ` along `N`,

  `∂_t γ_ij = −2 N K_ij + (L_N γ)_ij`,   `(L_N γ)_ij = D_i N_j + D_j N_i`,

and that Lie derivative is already `Curvature.DiffeomorphismMetricVariation.metricLieDerivative` (Loinger
Eq. 7): `(L_ε γ)_{mn} = ε^s ∂_s γ_{mn} + γ_{ms} ∂_n ε^s + γ_{ns} ∂_m ε^s`. So the general-shift evolution
is not out of scope — it is that Lie derivative with `ε = N`.

* `admMetricEvolution` — `∂_t γ = −2N K + L_N γ`, the ADM spatial-metric rate with a **general** shift.
* `admMetricEvolution_symm` — the rate is symmetric (symmetric `K`, symmetric `γ`).
* `admMetricEvolution_zero_shift` — at `N^i = 0` (geodesic slicing) it reduces to `−2N K`: the shift-free
  evolution the trace-only model implicitly assumed is the vanishing-shift special case.
* `extrinsicCurvature_of_evolution` — inverting it, `K = −(1/2N)(∂_t γ − L_N γ)`: the extrinsic
  curvature is the metric velocity with the shift's Lie-drag removed (`N ≠ 0`).

The shift is the Lagrange multiplier conjugate to the **momentum constraint** `D_j(K^ij − γ^ij K) = κ j^i`.
Its flux tensor is also a function of the full (traceless) `K`:

* `momentumFluxTensor` — `π^ij = K^ij − γ^ij K` (orthonormal frame).
* `momentumFluxTensor_eq_traceless` — `π = A − ⅔(tr K)·1`: the momentum flux carries the trace-free
  extrinsic curvature `A_ij` of `ExtrinsicCurvatureTracelessTransverse`, not just the trace.
* `momentumFluxTensor_trace` — `tr π = −2 tr K` (in `d = 3`).

Out of scope (the analytic layer): the covariant derivative `D_i` as an operator on a curved `γ` (here
the Lie derivative carries the shift term in a coordinate frame), and the time integration of the flow.
-/

set_option autoImplicit false

open Matrix
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse
open Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.AdmMetricEvolutionGeneralShift

/-! ## The ADM spatial-metric evolution with a general shift -/

/-- **[The Lie derivative along the zero shift vanishes]** `L_0 γ = 0` — a vanishing shift drags the
metric nowhere. -/
theorem metricLieDerivative_zero_shift (γ : Matrix (Fin 3) (Fin 3) ℝ)
    (dγ : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) :
    metricLieDerivative γ dγ 0 0 = 0 := by
  ext m n
  simp [metricLieDerivative]

/-- **The ADM spatial-metric evolution rate** `∂_t γ_ij = −2N K_ij + (L_N γ)_ij` — with lapse `N`,
extrinsic curvature `K`, and a **general** shift `N^i` entering through the Lie derivative
`(L_N γ)_ij = D_i N_j + D_j N_i` (`metricLieDerivative γ dγ shift dShift`). -/
def admMetricEvolution (N : ℝ) (K γ : Matrix (Fin 3) (Fin 3) ℝ)
    (dγ : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) (shift : Fin 3 → ℝ)
    (dShift : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (-(2 * N)) • K + metricLieDerivative γ dγ shift dShift

/-- **[The metric evolution rate is symmetric]** `(∂_t γ)ᵀ = ∂_t γ` — for symmetric extrinsic curvature
and symmetric metric derivatives. -/
theorem admMetricEvolution_symm (N : ℝ) (K γ : Matrix (Fin 3) (Fin 3) ℝ)
    (dγ : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) (shift : Fin 3 → ℝ)
    (dShift : Matrix (Fin 3) (Fin 3) ℝ) (hK : Kᵀ = K) (hdγ : ∀ s, (dγ s)ᵀ = dγ s) :
    (admMetricEvolution N K γ dγ shift dShift)ᵀ = admMetricEvolution N K γ dγ shift dShift := by
  unfold admMetricEvolution
  rw [Matrix.transpose_add, Matrix.transpose_smul, hK,
    metricLieDerivative_symm γ dγ shift dShift hdγ]

/-- **[Zero shift is the geodesic-slicing limit]** `∂_t γ = −2N K` at `N^i = 0`: the shift-free evolution
the conformally-flat, trace-only model implicitly used is the vanishing-shift special case of the general
one. -/
theorem admMetricEvolution_zero_shift (N : ℝ) (K γ : Matrix (Fin 3) (Fin 3) ℝ)
    (dγ : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) :
    admMetricEvolution N K γ dγ 0 0 = (-(2 * N)) • K := by
  unfold admMetricEvolution
  rw [metricLieDerivative_zero_shift, add_zero]

/-- **[The extrinsic curvature is the shift-corrected metric velocity]** given the evolution equation
`v = ∂_t γ`, `K = −(1/2N)(v − L_N γ)` (`N ≠ 0`): `K` is the metric velocity with the shift's Lie-drag
`L_N γ` subtracted off — the standard ADM definition of the extrinsic curvature for a general shift. -/
theorem extrinsicCurvature_of_evolution (N : ℝ) (K γ : Matrix (Fin 3) (Fin 3) ℝ)
    (dγ : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) (shift : Fin 3 → ℝ)
    (dShift v : Matrix (Fin 3) (Fin 3) ℝ) (hN : N ≠ 0)
    (hv : v = admMetricEvolution N K γ dγ shift dShift) :
    K = (-(2 * N))⁻¹ • (v - metricLieDerivative γ dγ shift dShift) := by
  have h2N : -(2 * N) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero two_ne_zero hN)
  rw [hv]
  unfold admMetricEvolution
  rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ h2N, one_smul]

/-! ## The momentum constraint the shift is conjugate to -/

/-- **The momentum-constraint flux** `π^{ij} = K^{ij} − γ^{ij} K` (orthonormal frame): the tensor whose
divergence `D_j π^{ij} = κ j^i` is the momentum (super-momentum) constraint — the constraint the shift
`N^i` is the Lagrange multiplier for. -/
def momentumFluxTensor (K : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  K - (Matrix.trace K) • 1

/-- **[The momentum flux carries the trace-free extrinsic curvature]** `π = A − ⅔(tr K)·1`: the momentum
constraint the shift enforces is a function of the full `K_ij` through its trace-free part
`A_ij = extrinsicTraceless K`, not only the trace. -/
theorem momentumFluxTensor_eq_traceless (K : Matrix (Fin 3) (Fin 3) ℝ) :
    momentumFluxTensor K = extrinsicTraceless K - (2 / 3 * Matrix.trace K) • 1 := by
  unfold momentumFluxTensor extrinsicTraceless
  module

/-- **[The momentum-flux trace is `−2 tr K`]** (in `d = 3`). -/
theorem momentumFluxTensor_trace (K : Matrix (Fin 3) (Fin 3) ℝ) :
    (momentumFluxTensor K).trace = -2 * Matrix.trace K := by
  unfold momentumFluxTensor
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  ring

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.AdmMetricEvolutionGeneralShift

end

end

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.AdmMetricEvolutionGeneralShift in
#physlib_axiom_clean_all [
  metricLieDerivative_zero_shift,
  admMetricEvolution_symm,
  admMetricEvolution_zero_shift,
  extrinsicCurvature_of_evolution,
  momentumFluxTensor_eq_traceless,
  momentumFluxTensor_trace ]

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.AdmMetricEvolutionGeneralShift in
#physlib_non_vacuous_all [
  metricLieDerivative_zero_shift,
  admMetricEvolution_symm,
  admMetricEvolution_zero_shift,
  extrinsicCurvature_of_evolution,
  momentumFluxTensor_eq_traceless,
  momentumFluxTensor_trace ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.AdmMetricEvolutionGeneralShift.admMetricEvolution_zero_shift where
  formalizes @ "claim:the-general-shift-adm-metric-evolution-reduces-to-the-shift-free-rate-at-vanishing-shift",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Curvature.DiffeomorphismMetricVariation.metricLieDerivative"

zil attach Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.AdmMetricEvolutionGeneralShift.extrinsicCurvature_of_evolution where
  formalizes @ "claim:the-extrinsic-curvature-is-the-adm-metric-velocity-with-the-general-shift-lie-drag-removed",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.AdmMetricEvolutionGeneralShift.admMetricEvolution"

zil attach Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.AdmMetricEvolutionGeneralShift.momentumFluxTensor_eq_traceless where
  formalizes @ "claim:the-momentum-constraint-flux-the-shift-enforces-carries-the-trace-free-extrinsic-curvature",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse.extrinsicTraceless"

/- ZIL-END -/
