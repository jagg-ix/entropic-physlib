/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

/-!
# Linking the Ipek–Caticha ADM sector to the repository's canonical gravity (York time, Gauss–Codazzi, Wheeler–DeWitt)

Connects the Ipek–Caticha gravitational sector (`IpekCatichaDeWittSupermetricADM`,
`IpekCatichaMatterGravityConstraint`) to the repository's canonical-gravity infrastructure
(`CanonicalTetradGravity.TetradADMGravity`, the Lusanna/York-time ADM Hamiltonian constraint feeding the
Wheeler–DeWitt equation). The Ipek–Caticha mixed extrinsic curvature `K = (Tr M)·1 − 2M` (Eq. 85) is exactly the
`K` of the repository's `yorkTime`/`hamiltonianConstraint`, so the two developments describe one canonical gravity:

* the **Ipek–Caticha York time is the momentum trace** `yorkTime(K) = Tr M` (`admExtrinsicMixed_yorkTime`) —
 Lusanna's York-time gauge variable `tr K` of the Ipek–Caticha extrinsic curvature is the trace of the
 gravitational momentum, reusing `admExtrinsicMixed_trace` and the repository `yorkTime = Matrix.trace`;
* the **Ipek–Caticha vacuum super-Hamiltonian is the Gauss–Codazzi constraint** `R + (Tr M)² = KdotK`
 (`ipekCaticha_admConstraint_vacuum`) — the ADM Hamiltonian constraint `hamiltonianConstraint = 0` for the
 Ipek–Caticha extrinsic curvature is the `G_{nn} = 0` relation between the `3`-curvature and the extrinsic
 curvature;
* the **Klein–Gordon matter sources the ADM constraint** `R + (Tr M)² = KdotK + κ ℋ`
 (`ipekCaticha_kgMatter_sources_admConstraint`) — the Ipek–Caticha Klein–Gordon energy density `ℋ`
 (`kgMatterDensity`) is the source `κρ` of the repository's `sourcedHamiltonianConstraint`, the quantum matter
 curving the geometry: the `G_{nn} = κ T_{nn}` Einstein constraint.

So the Ipek–Caticha coupled gravity is the repository's canonical ADM gravity: its extrinsic curvature feeds the
York-time / Gauss–Codazzi `hamiltonianConstraint` that (quantized) is the Wheeler–DeWitt equation
(`WheelerDeWittComplexEinstein`), and its Klein–Gordon matter is the constraint's source. The transition weight
itself already sits on the entropic `kuikenWeight` hub (`EntropicDynamicsTransitionProbability.edTransitionWeight_is_kuiken`,
alongside the Hawking, Matsubara, Sorkin and confinement weights).

* **§A — the York time link** (`admExtrinsicMixed_yorkTime`).
* **§B — the Gauss–Codazzi vacuum constraint** (`ipekCaticha_admConstraint_vacuum`).
* **§C — matter-sourced ADM constraint** (`ipekCaticha_kgMatter_sources_admConstraint`).

The York-time identity, the vacuum Gauss–Codazzi constraint, and the matter-sourced constraint
are exact algebra, reusing `admExtrinsicMixed`/`admExtrinsicMixed_trace`, `kgMatterDensity`, and the repository
`yorkTime`/`hamiltonianConstraint`/`sourcedHamiltonianConstraint`. The full tetrad ADM canonical structure and the
Wheeler–DeWitt quantization live in the referenced modules. No new axioms.

## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 85, 100a); Gauss–Codazzi; B.S. DeWitt. Repo dependencies:
 `CanonicalTetradGravity.TetradADMGravity` (`yorkTime`, `hamiltonianConstraint`, `sourcedHamiltonianConstraint`),
 `EntropicTime.IpekCatichaDeWittSupermetricADM`, `EntropicTime.IpekCatichaMatterGravityConstraint`.

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint

/-! ## §A — the York time link -/

/-- **[The Ipek–Caticha York time is the momentum trace] `yorkTime(K) = Tr M`.** Lusanna's York-time gauge
variable `tr K` (the trace of the extrinsic curvature) of the Ipek–Caticha mixed extrinsic curvature
`K = (Tr M)·1 − 2M` is the trace of the gravitational momentum `M` — the repository `yorkTime` of the arc's
`admExtrinsicMixed`, via `admExtrinsicMixed_trace`. -/
theorem admExtrinsicMixed_yorkTime (M : Matrix (Fin 3) (Fin 3) ℝ) :
    yorkTime (admExtrinsicMixed M) = M.trace := by
  unfold yorkTime
  exact admExtrinsicMixed_trace M

/-! ## §B — the Gauss–Codazzi vacuum constraint -/

/-- **[The Ipek–Caticha vacuum super-Hamiltonian is the Gauss–Codazzi constraint] `R + (Tr M)² = KdotK`.** The
repository ADM Hamiltonian constraint `hamiltonianConstraint = 0` for the Ipek–Caticha extrinsic curvature is the
`G_{nn} = 0` relation `R₃ + (Tr M)² = KdotK` between the spatial curvature and the extrinsic curvature — the
vacuum super-Hamiltonian constraint (Eqs. 66, 68). -/
theorem ipekCaticha_admConstraint_vacuum (R3 KdotK : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    hamiltonianConstraint R3 KdotK (admExtrinsicMixed M) = 0 ↔ R3 + M.trace ^ 2 = KdotK := by
  rw [hamiltonianConstraint_vacuum_iff, admExtrinsicMixed_yorkTime]

/-! ## §C — matter-sourced ADM constraint -/

/-- **[The Klein–Gordon matter sources the ADM constraint] `R + (Tr M)² = KdotK + κ ℋ`.** The Ipek–Caticha
Klein–Gordon energy density `ℋ = kgMatterDensity` (Eq. 100a) is the source `κρ` of the repository's
`sourcedHamiltonianConstraint`: the quantum matter curves the geometry, the `G_{nn} = κ T_{nn}` Einstein constraint
in canonical form. -/
theorem ipekCaticha_kgMatter_sources_admConstraint (R3 KdotK κ sqrtg ginv π gradchi V : ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    sourcedHamiltonianConstraint R3 KdotK (kgMatterDensity sqrtg ginv π gradchi V) κ
        (admExtrinsicMixed M)
      ↔ R3 + M.trace ^ 2 = KdotK + κ * kgMatterDensity sqrtg ginv π gradchi V := by
  unfold sourcedHamiltonianConstraint hamiltonianConstraint
  rw [admExtrinsicMixed_yorkTime]
  constructor <;> intro h <;> linarith

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint

end
