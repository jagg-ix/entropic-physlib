/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MatsubaraSorkinReggeEntropicWeight
public import Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance

/-!
# The Sorkin causal-set quantum-gravity path integral on the entropic-weight hub

This links the **Sorkin causal-set quantum-gravity path integral** — the sum over causal sets
`Z = ∑ exp[(i/ℏ) S_2D]` weighted by the discrete Einstein–Hilbert (Benincasa–Dowker) action
`S_2D = ℏ·(N − 2N₀ + 4N₁ − 2N₂)` (`CausalSetIntervalAbundance.bdgAction2D`) — to the same master complex-action
weight / entropic-damping hub (`kuikenWeight`) carrying the Matsubara, Sorkin-histories, Regge and Caldeira–Leggett
path integrals (`MatsubaraSorkinReggeEntropicWeight`).

The causal-set gravity supplies the **real (phase) action** `S_R = S_2D` of the master weight
`exp[(i/ℏ)S_R − (1/ℏ)S_I]` — the discrete geometry is a pure phase. When the causal set carries an entropic
(imaginary) action `S_I` — Wick rotation, a preferred-past growth dynamics, or the environment damping — the
weight's modulus is `kuikenWeight ℏ S_I = e^{−S_I/ℏ}`, joining the four entropic incarnations as the geometric
partner. The **real-action, `S_I = 0`** limit is a **unit-modulus (unitary) sum over causal sets** — the
reversible limit, matching the `N_c = 4` Regge, high-`T` Matsubara, no-environment Sorkin and diagonal
Caldeira–Leggett unitary cases.

The loop closes back on the Sorkin decoherence functional: the causal *order* itself supplies
(`CausalSetIntervalAbundance.causalSign_isPauliJordan`) the Pauli–Jordan kernel that fixes the Sorkin–Johnston
vacuum, which (`DecoherenceFunctionalSorkinJohnston`) *is* the decoherence functional — so the causal-set
quantum-gravity path integral and the Sorkin quantum measure are two ends of one construction.

* **§A — the causal-set QG weight is the entropic weight.** **`causalSet_bdg_modulus_is_kuiken`**
  (`‖exp[(i/ℏ)S_2D − S_I/ℏ]‖ = kuikenWeight ℏ S_I`).
* **§B — the reversible (unitary) limit.** **`causalSet_bdg_real_unitary`** (real BDG action ⇒ unit modulus).
* **§C — the fifth member of the unification.** **`causalSet_gravity_is_fifth`** (`= kuikenWeight 1 S_I`, matching
  Matsubara/Regge/Sorkin/Caldeira–Leggett), **`causalSet_gravity_eq_matsubara`** (equal at a common action).

**Honest layering.** Exact `Real.exp` identities placing `bdgAction2D` into the master weight and reading off the
modulus; the causal-set combinatorics (interval abundances, Poisson sprinkling) and the convergence of the
sum-over-causal-sets are `CausalSetIntervalAbundance`'s content, reused not re-derived.

## References

* Reuses `CausalSetIntervalAbundance` (Benincasa–Dowker action, Glaser–Surya) and
  `MatsubaraSorkinReggeEntropicWeight` on `PathIntegral.ComplexActionPathIntegralWeight`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionPathIntegralWeight
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.MatsubaraThermalOscillator
open Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance
open Physlib.QuantumMechanics.ComplexAction.MatsubaraSorkinReggeEntropicWeight

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral


/-- **The Sorkin causal-set QG weight is the master complex-action weight**, with the discrete Einstein–Hilbert
action `S_2D = ℏ·bdgAction2D` as the real phase and an entropic action `S_I`; its modulus is the entropic damping
`kuikenWeight ℏ S_I = e^{−S_I/ℏ}` (`master_modulus_is_kuiken`). The causal-set gravity path integral sits on the
same hub as Matsubara/Sorkin/Regge/Caldeira–Leggett. -/
lemma causalSet_bdg_modulus_is_kuiken (N N₀ N₁ N₂ S_I ℏ : ℝ) :
    ‖complexActionPathIntegralWeight (ℏ * bdgAction2D N N₀ N₁ N₂) S_I ℏ‖ = kuikenWeight ℏ S_I :=
  master_modulus_is_kuiken _ _ _


/-- **A real causal-set action gives a unitary sum over causal sets** — with no entropic action (`S_I = 0`) the
discrete Einstein–Hilbert weight `exp[(i/ℏ)S_2D]` has unit modulus: the reversible/unitary limit of the causal-set
quantum-gravity path integral (the `N_c = 4` Regge / high-`T` Matsubara / no-environment Sorkin analogue). -/
lemma causalSet_bdg_real_unitary (N N₀ N₁ N₂ ℏ : ℝ) :
    ‖complexActionPathIntegralWeight (ℏ * bdgAction2D N N₀ N₁ N₂) 0 ℏ‖ = 1 := by
  rw [causalSet_bdg_modulus_is_kuiken, kuikenWeight, zero_div, neg_zero, Real.exp_zero]


/-- **The causal-set QG path integral is the fifth incarnation of the entropic weight** — at `ℏ = 1` its modulus is
`kuikenWeight 1 S_I`, the same weight as the Matsubara thermal, Regge geometric, Sorkin entanglement and
Caldeira–Leggett decoherence path integrals (`four_actions_one_entropic_weight`). Geometry is the phase; the four
`S_I` are the damping. -/
lemma causalSet_gravity_is_fifth (N N₀ N₁ N₂ S_I : ℝ) :
    ‖complexActionPathIntegralWeight (1 * bdgAction2D N N₀ N₁ N₂) S_I 1‖ = kuikenWeight 1 S_I :=
  causalSet_bdg_modulus_is_kuiken N N₀ N₁ N₂ S_I 1

/-- **Causal-set gravity and the Matsubara thermal weight coincide** at a common entropic action `S_I = βE` — the
discrete-geometry path integral's damping is the same entropic weight as the imaginary-time thermal one. -/
lemma causalSet_gravity_eq_matsubara (N N₀ N₁ N₂ β E : ℝ) :
    ‖complexActionPathIntegralWeight (1 * bdgAction2D N N₀ N₁ N₂) (β * E) 1‖
      = matsubaraBoltzmannWeight β E := by
  rw [causalSet_gravity_is_fifth, matsubara_boltzmann_is_kuiken]

end Physlib.QuantumMechanics.ComplexAction.SorkinCausalSetGravityPathIntegral
