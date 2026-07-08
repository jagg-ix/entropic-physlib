/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM

/-!
# The metric evolution of entropic geometrodynamics: extrinsic curvature is the metric velocity (Ipek–Caticha)

Formalizes the geometrodynamic **evolution of the spatial metric** in Ipek–Caticha (arXiv:2006.05036, Eqs. 61,
84b): under a normal deformation the metric changes by (minus twice) the extrinsic curvature,

`∂_⊥ g_{ij} = −2 K_{ij}` (Eq. 61), `£_m g_{ij} = (2κ/√g)(2π_{ij} − π g_{ij}) N` (Eq. 84b),

so the metric's normal velocity is proportional to `2π_{ij} − π g_{ij}`, which is exactly minus the extrinsic
curvature `K` of `IpekCatichaDeWittSupermetricADM`. In the mixed-momentum representation `M = π^i_j` the metric
velocity is `V(M) = 2M − (Tr M)·1`, and the geometrodynamic content is:

* the **metric velocity is minus the extrinsic curvature** `V(M) = −K` (`metricVelocity_eq_neg_extrinsic`) — the
 extrinsic curvature *is* the "velocity" of the spatial metric under a normal deformation (`∂_⊥ g = −2K`,
 the geometry evolving along the foliation);
* the **volume expansion is minus the York time** `Tr V(M) = −Tr M` (`metricVelocity_trace`) — the trace of the
 metric velocity is minus the trace of the momentum (the York time `tr K`), the expansion scalar of the
 hypersurface;
* the **momentum is recovered from the metric velocity** `M = ½(V(M) − (Tr V(M))·1)` (`admMomentum_from_metricVelocity`)
 — the canonical momentum is reconstructed from the metric's rate of change, closing the geometrodynamic loop with
 the `K ↔ π` inversion.

So entropic geometrodynamics evolves the spatial metric along the foliation with velocity the (negative) extrinsic
curvature, whose trace is the York-time expansion, and the canonical momentum is read back from that velocity — the
`(g_{ij}, π^{ij})` phase-space dynamics of the Ipek–Caticha model.

* **§A — the metric velocity is minus the extrinsic curvature** (`metricVelocityMixed`,
 `metricVelocity_eq_neg_extrinsic`).
* **§B — the expansion and the momentum recovery** (`metricVelocity_trace`,
 `admMomentum_from_metricVelocity`).

The metric-velocity/extrinsic-curvature identity, the expansion trace, and the momentum
recovery are exact `3×3` matrix algebra in the mixed-momentum representation, reusing `admExtrinsicMixed`. The full
tensor Lie-derivative evolution (with lapse and shift) is the referenced content. No new axioms.

## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 61, 84b, 85); ADM geometrodynamics. Repo structure:
 `EntropicTime.IpekCatichaDeWittSupermetricADM` (`admExtrinsicMixed`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMetricEvolution

/-! ## §A — the metric velocity is minus the extrinsic curvature -/

/-- **The mixed metric velocity** `V(M) = 2M − (Tr M)·1` — the normal velocity of the spatial metric (Ipek–Caticha
Eq. 84b, proportional to `2π_{ij} − π g_{ij}`), the rate of change of the geometry along the foliation. -/
noncomputable def metricVelocityMixed (M : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (2 : ℝ) • M - M.trace • (1 : Matrix (Fin 3) (Fin 3) ℝ)

/-- **[The metric velocity is minus the extrinsic curvature] `V(M) = −K`.** The normal velocity of the spatial
metric is minus the extrinsic curvature `K = (Tr M)·1 − 2M` — the geometrodynamic relation `∂_⊥ g_{ij} = −2 K_{ij}`
(Eq. 61): the extrinsic curvature *is* the velocity of the metric. -/
theorem metricVelocity_eq_neg_extrinsic (M : Matrix (Fin 3) (Fin 3) ℝ) :
    metricVelocityMixed M = -admExtrinsicMixed M := by
  unfold metricVelocityMixed admExtrinsicMixed
  module

/-! ## §B — the expansion and the momentum recovery -/

/-- **[The volume expansion is minus the York time] `Tr V(M) = −Tr M`.** The trace of the metric velocity — the
expansion scalar of the hypersurface — is minus the trace of the gravitational momentum (the York time `tr K`). -/
theorem metricVelocity_trace (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (metricVelocityMixed M).trace = -M.trace := by
  unfold metricVelocityMixed
  simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
    Nat.cast_ofNat]
  ring

/-- **[The momentum is recovered from the metric velocity] `M = ½(V(M) − (Tr V(M))·1)`.** The canonical
gravitational momentum is reconstructed from the metric's velocity, closing the geometrodynamic loop: the metric
evolves with velocity `−K`, and the momentum is read back from that velocity. -/
theorem admMomentum_from_metricVelocity (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (1 / 2 : ℝ) • (metricVelocityMixed M - (metricVelocityMixed M).trace • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      = M := by
  rw [metricVelocity_trace]
  unfold metricVelocityMixed
  module

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMetricEvolution

end
