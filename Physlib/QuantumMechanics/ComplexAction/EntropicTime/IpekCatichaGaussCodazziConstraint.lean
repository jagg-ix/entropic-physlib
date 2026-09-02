/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

meta import Zil

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

**Honest layering.** The York-time identity, the vacuum Gauss–Codazzi constraint, and the matter-sourced constraint
are exact algebra, reusing `admExtrinsicMixed`/`admExtrinsicMixed_trace`, `kgMatterDensity`, and the repository
`yorkTime`/`hamiltonianConstraint`/`sourcedHamiltonianConstraint`. The full tetrad ADM canonical structure and the
Wheeler–DeWitt quantization live in the referenced modules. ## References

* S. Ipek, A. Caticha, arXiv:2006.05036 (Eqs. 85, 100a); Gauss–Codazzi; B.S. DeWitt. Repo carriers:
  `CanonicalTetradGravity.TetradADMGravity` (`yorkTime`, `hamiltonianConstraint`, `sourcedHamiltonianConstraint`),
  `EntropicTime.IpekCatichaDeWittSupermetricADM`, `EntropicTime.IpekCatichaMatterGravityConstraint`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint


/-- **[The Ipek–Caticha York time is the momentum trace] `yorkTime(K) = Tr M`.** Lusanna's York-time gauge
variable `tr K` (the trace of the extrinsic curvature) of the Ipek–Caticha mixed extrinsic curvature
`K = (Tr M)·1 − 2M` is the trace of the gravitational momentum `M` — the repository `yorkTime` of the arc's
`admExtrinsicMixed`, via `admExtrinsicMixed_trace`. -/
lemma admExtrinsicMixed_yorkTime (M : Matrix (Fin 3) (Fin 3) ℝ) :
    yorkTime (admExtrinsicMixed M) = M.trace := by
  unfold yorkTime
  exact admExtrinsicMixed_trace M


/-- **[The Ipek–Caticha vacuum super-Hamiltonian is the Gauss–Codazzi constraint] `R + (Tr M)² = KdotK`.** The
repository ADM Hamiltonian constraint `hamiltonianConstraint = 0` for the Ipek–Caticha extrinsic curvature is the
`G_{nn} = 0` relation `R₃ + (Tr M)² = KdotK` between the spatial curvature and the extrinsic curvature — the
vacuum super-Hamiltonian constraint (Eqs. 66, 68). -/
lemma ipekCaticha_admConstraint_vacuum (R3 KdotK : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    hamiltonianConstraint R3 KdotK (admExtrinsicMixed M) = 0 ↔ R3 + M.trace ^ 2 = KdotK := by
  rw [hamiltonianConstraint_vacuum_iff, admExtrinsicMixed_yorkTime]


/-- **[The Klein–Gordon matter sources the ADM constraint] `R + (Tr M)² = KdotK + κ ℋ`.** The Ipek–Caticha
Klein–Gordon energy density `ℋ = kgMatterDensity` (Eq. 100a) is the source `κρ` of the repository's
`sourcedHamiltonianConstraint`: the quantum matter curves the geometry, the `G_{nn} = κ T_{nn}` Einstein constraint
in canonical form. -/
lemma ipekCaticha_kgMatter_sources_admConstraint (R3 KdotK κ sqrtg ginv π gradchi V : ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    sourcedHamiltonianConstraint R3 KdotK (kgMatterDensity sqrtg ginv π gradchi V) κ
        (admExtrinsicMixed M)
      ↔ R3 + M.trace ^ 2 = KdotK + κ * kgMatterDensity sqrtg ginv π gradchi V := by
  unfold sourcedHamiltonianConstraint hamiltonianConstraint
  rw [admExtrinsicMixed_yorkTime]
  constructor <;> intro h <;> linarith

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint.ipekCaticha_admConstraint_vacuum where
  formalizes @ "claim:in-vacuum-the-entropic-dynamics-adm-hamiltonian-constraint-vanishing-is-exactly-the-gauss-codazzi-relation-spatial-ricci-scalar-plus-trace-k-squared-equals-k-dot-k-tying-intrinsic-curvature-to-extrinsic-curvature",
  supported_by @ "paper:ipek-caticha-entropic-dynamics-quantum-gravity-functional-schrodinger-constraints"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint.ipekCaticha_kgMatter_sources_admConstraint where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint.admExtrinsicMixed_yorkTime",
  formalizes @ "claim:klein-gordon-quantum-matter-enters-the-adm-hamiltonian-constraint-as-the-source-kappa-times-the-matter-density-the-canonical-form-of-the-einstein-constraint-g-normal-normal-equals-kappa-t-normal-normal"

zil attach Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint.admExtrinsicMixed_yorkTime where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM.admExtrinsicMixed_trace",
  formalizes @ "claim:the-ipek-caticha-york-time-gauge-variable-trace-k-equals-the-trace-of-the-gravitational-momentum-m"

zil_file_contract physlib.ipekCatichaGaussCodazziConstraint where
  promises "Linking the Ipek-Caticha ADM sector to the repository's canonical gravity (York time, Gauss-Codazzi, Wheeler-DeWitt). In vacuum the ADM Hamiltonian constraint vanishing is exactly the Gauss-Codazzi relation R_3 + (Tr M)^2 = K.K (ipekCaticha_admConstraint_vacuum); Klein-Gordon quantum matter enters as the source kappa*H, the canonical Einstein constraint G_nn = kappa T_nn (ipekCaticha_kgMatter_sources_admConstraint); and the York-time gauge variable Tr K equals the trace of the gravitational momentum M (admExtrinsicMixed_yorkTime)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity.yorkTime",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaDeWittSupermetricADM.admExtrinsicMixed",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaMatterGravityConstraint.kgMatterDensity"]
  forbids_substitutes ["the full Gauss-Codazzi-Mainardi embedding equations with the covariant derivatives of the extrinsic curvature and the diffeomorphism (momentum) constraint, which are the cited canonical-gravity infrastructure",
    "any claim that the Einstein constraints are derived from the field equations; only the algebraic identification of the vanishing ADM constraint with the trace relation is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint.ipekCaticha_admConstraint_vacuum,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint.ipekCaticha_kgMatter_sources_admConstraint,
    Physlib.QuantumMechanics.ComplexAction.EntropicTime.IpekCatichaGaussCodazziConstraint.admExtrinsicMixed_yorkTime]

/- ZIL-END -/
