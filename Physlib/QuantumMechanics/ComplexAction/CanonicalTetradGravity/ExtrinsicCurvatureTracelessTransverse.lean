/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
public import Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# Beyond the trace: the traceless extrinsic curvature and the transverse-traceless graviton

`TetradADMGravity.hamiltonianConstraint` writes the time–time Einstein equation `ℋ = ³R + (tr K)² − K_ij K^ij`
with the extrinsic-curvature norm `K_ij K^ij` as an **opaque scalar** `KdotK`, so the full symmetric `K_ij`
enters the dynamics only through its trace `tr K` (`yorkTime`). This file supplies the two pieces of the
3+1 formalism that go beyond the trace — the general (traceless) extrinsic curvature and the
transverse-traceless (radiative) metric mode — as self-contained matrix algebra over the spatial frame,
in an orthonormal spatial gauge `γ_ij = δ_ij` (so `K^ij = K_ij` and `K_ij K^ij = Tr(K²)`).

## The general extrinsic curvature (its traceless part)

`extrinsicTraceless K = K − (⅓ tr K)·1` is the trace-free part `A_ij = K_ij − ⅓γ_ij K` — the shear/tidal
degrees of freedom the trace `tr K` discards.

* `extrinsicTraceless_trace_zero` — `tr A = 0`.
* `extrinsicNormSq_decomp` — `K_ij K^ij = A_ij A^ij + ⅓(tr K)²`: the York conformal/trace-free split of the
  extrinsic-curvature norm — the full `K_ij` enters through `Tr(A²)` (the graviton part) plus `⅓(tr K)²`
  (the conformal part). This is the content the opaque `KdotK` was hiding.
* `hamiltonianConstraint_traceless_split` — feeding the genuine `K_ij K^ij` into the scalar constraint,
  `ℋ = ³R + ⅔(tr K)² − A_ij A^ij`: the Hamiltonian constraint as an explicit function of the full `K_ij`,
  with the trace-free (graviton) term separated from the conformal (trace) term.

## The transverse-traceless graviton mode

The spatial metric perturbation `h_ij` has, of its six components, exactly two physical (radiative)
polarizations: the transverse-traceless part. `ttProject k h = t·h·t − ½ Tr(t·h)·t`, with `t = δ − k⊗k/k²`
the spin-1 transverse projector (`YangMillsCoulombGaugeVacuum.transverseProjector`), is the spin-2
transverse-traceless projector `Λ_{ij,kl} = t_{ik}t_{jl} − ½ t_{ij}t_{kl}`.

* `ttProject_isSymm` — the projection of a symmetric tensor is symmetric.
* `ttProject_transverse` — `(Λh)·k = 0`: the projected mode is divergence-free (transverse).
* `ttProject_traceless` — `Tr(Λh) = 0`, **exactly in `d = 3`**, where `tr t = 2` supplies the two physical
  polarizations (the `½` counterterm cancels the trace only at `tr t = 2`).
* `ttProject_transverseTraceless` — both together: `Λh` is genuinely transverse-traceless, the radiative
  gravitational degree of freedom absent from the conformally-flat, trace-only model.

Out of scope (the dynamical layer): the propagation `□h^{TT}_{ij} = −16πG T_{ij}` and the general shift
evolution — this file supplies the kinematic decomposition the wave equation would act on.
-/

set_option autoImplicit false

open Matrix
open scoped Matrix
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse

/-! ## The traceless extrinsic curvature (general `K_ij`, not just its trace) -/

/-- **The traceless (trace-free) extrinsic curvature** `A_ij = K_ij − ⅓ γ_ij K` in an orthonormal spatial
frame (`γ_ij = δ_ij`): the shear/tidal part of `K` that the York time `tr K` discards. -/
def extrinsicTraceless (K : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  K - (Matrix.trace K / 3) • 1

/-- **[The trace-free extrinsic curvature is trace-free]** `tr A = 0`. -/
theorem extrinsicTraceless_trace_zero (K : Matrix (Fin 3) (Fin 3) ℝ) :
    (extrinsicTraceless K).trace = 0 := by
  unfold extrinsicTraceless
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  ring

/-- **The extrinsic-curvature norm** `K_ij K^ij = Tr(K²)` (orthonormal spatial frame). -/
def extrinsicNormSq (K : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := (K * K).trace

/-- **[The York conformal / trace-free split of `K_ij K^ij`]** `K_ij K^ij = A_ij A^ij + ⅓(tr K)²`: the
extrinsic-curvature norm separates into the trace-free (graviton) part `Tr(A²)` and the conformal (trace)
part `⅓(tr K)²`. The full symmetric `K_ij` enters through `Tr(A²)`, which the trace `tr K` alone omits. -/
theorem extrinsicNormSq_decomp (K : Matrix (Fin 3) (Fin 3) ℝ) :
    extrinsicNormSq K
      = (extrinsicTraceless K * extrinsicTraceless K).trace + (Matrix.trace K) ^ 2 / 3 := by
  simp only [extrinsicNormSq, extrinsicTraceless, Matrix.sub_mul, Matrix.mul_sub, smul_mul_assoc,
    mul_smul_comm, Matrix.mul_one, Matrix.one_mul, smul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
  ring

/-- **[The Hamiltonian constraint as a function of the full `K_ij`]** `ℋ = ³R + ⅔(tr K)² − A_ij A^ij`:
substituting the genuine `K_ij K^ij` (not an opaque scalar) into `TetradADMGravity.hamiltonianConstraint`
splits the time–time Einstein constraint into the conformal term `⅔(tr K)²` and the trace-free graviton
term `A_ij A^ij` — the extrinsic curvature now enters through its full tensor, not only its trace. -/
theorem hamiltonianConstraint_traceless_split (R3 : ℝ) (K : Matrix (Fin 3) (Fin 3) ℝ) :
    hamiltonianConstraint R3 (extrinsicNormSq K) K
      = R3 + 2 / 3 * (Matrix.trace K) ^ 2 - (extrinsicTraceless K * extrinsicTraceless K).trace := by
  unfold hamiltonianConstraint yorkTime
  rw [extrinsicNormSq_decomp]
  ring

/-! ## The transverse-traceless graviton mode -/

/-- **The spin-2 transverse-traceless projector** `Λ_{ij,kl} = t_{ik}t_{jl} − ½ t_{ij}t_{kl}` applied to a
symmetric tensor `h`: `ttProject k h = t·h·t − ½ Tr(t·h)·t`, with `t = δ − k⊗k/k²` the transverse (spin-1)
projector. Extracts the physical (radiative) gravitational polarizations from a metric perturbation. -/
def ttProject (k : Fin 3 → ℝ) (h : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  transverseProjector k * h * transverseProjector k
    - (1 / 2 * (transverseProjector k * h).trace) • transverseProjector k

/-- **[The transverse-traceless projection of a symmetric tensor is symmetric]** `(Λh)ᵀ = Λh`. -/
theorem ttProject_isSymm (k : Fin 3 → ℝ) {h : Matrix (Fin 3) (Fin 3) ℝ} (hh : hᵀ = h) :
    (ttProject k h)ᵀ = ttProject k h := by
  unfold ttProject
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul,
    transverseProjector_isSymm, hh, Matrix.mul_assoc]

/-- **[The transverse-traceless mode is transverse]** `(Λh)·k = 0`: the projected metric perturbation is
divergence-free along the propagation direction `k` — the physical gravitational wave has no longitudinal
part. -/
theorem ttProject_transverse (k : Fin 3 → ℝ) (h : Matrix (Fin 3) (Fin 3) ℝ) (hk : k ⬝ᵥ k ≠ 0) :
    ttProject k h *ᵥ k = 0 := by
  unfold ttProject
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    transverseProjector_mulVec_self k hk, Matrix.mulVec_zero, smul_zero, sub_zero]

/-- **[The transverse-traceless mode is traceless, in `d = 3`]** `Tr(Λh) = 0`. The `½` counterterm cancels
the trace precisely because `tr t = d − 1 = 2` in three spatial dimensions — the count of the two physical
graviton polarizations. -/
theorem ttProject_traceless (k : Fin 3 → ℝ) (h : Matrix (Fin 3) (Fin 3) ℝ) (hk : k ⬝ᵥ k ≠ 0) :
    (ttProject k h).trace = 0 := by
  have hPhP : (transverseProjector k * h * transverseProjector k).trace
      = (transverseProjector k * h).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, transverseProjector_mul_self k hk]
  unfold ttProject
  rw [Matrix.trace_sub, Matrix.trace_smul, hPhP, transverseProjector_trace k hk, smul_eq_mul]
  push_cast
  ring

/-- **[The projected mode is transverse-traceless]** `(Λh)·k = 0 ∧ Tr(Λh) = 0`: `ttProject k h` is a genuine
transverse-traceless tensor — the two-polarization radiative gravitational degree of freedom absent from a
conformally-flat, trace-only extrinsic-curvature model. -/
theorem ttProject_transverseTraceless (k : Fin 3 → ℝ) (h : Matrix (Fin 3) (Fin 3) ℝ)
    (hk : k ⬝ᵥ k ≠ 0) :
    ttProject k h *ᵥ k = 0 ∧ (ttProject k h).trace = 0 :=
  ⟨ttProject_transverse k h hk, ttProject_traceless k h hk⟩

end Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse

end

end

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse in
#physlib_axiom_clean_all [
  extrinsicTraceless_trace_zero,
  extrinsicNormSq_decomp,
  hamiltonianConstraint_traceless_split,
  ttProject_isSymm,
  ttProject_transverse,
  ttProject_traceless,
  ttProject_transverseTraceless ]

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse in
#physlib_non_vacuous_all [
  extrinsicTraceless_trace_zero,
  extrinsicNormSq_decomp,
  hamiltonianConstraint_traceless_split,
  ttProject_isSymm,
  ttProject_transverse,
  ttProject_traceless,
  ttProject_transverseTraceless ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse.extrinsicNormSq_decomp where
  supported_by @ "lean:HermitianMat.trace_one",
  supported_by @ "lean:HermitianMat.trace_smul",
  formalizes @ "claim:the-extrinsic-curvature-norm-splits-into-the-trace-free-graviton-part-and-the-conformal-trace-part"

zil attach Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse.hamiltonianConstraint_traceless_split where
  formalizes @ "claim:the-hamiltonian-constraint-is-a-function-of-the-full-extrinsic-curvature-not-only-its-trace",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse.extrinsicNormSq_decomp",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity.hamiltonianConstraint"

zil attach Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ExtrinsicCurvatureTracelessTransverse.ttProject_transverseTraceless where
  formalizes @ "claim:the-spin-two-projection-of-a-metric-perturbation-is-transverse-traceless-the-radiative-graviton-mode",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector",
  caveat @ "claim:the-transverse-traceless-wave-propagation-and-general-shift-evolution-remain-out-of-scope"

/- ZIL-END -/
