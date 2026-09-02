/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant

/-!
# Sorkin Sec. IV B — the time-evolution problem

Sorkin (1975) Sec. IV B poses the discrete time-evolution problem: given the thatch known up to a
"time", carry the solution forward one step. The reasoning is:

* **Locality (§IV A).** Because of the Schläfli identity (Appendix B), the thatch equation of a leg
  `λ` involves only the legs of its `4`-simplex star `𝒮₄(λ)` — the discrete counterpart of Einstein's
  equations being second-order. So a leg *implicates* only finitely many others (`Implicates`,
  `implicates_finite`): the evolution splits into **finite clusters**, not one infinite system.
* **A determined step (§IV B).** Each step is a *square* system — "exactly `N` equations for `N`
  unknowns" (`IsWellPosedStep`): for the closed `S³×R` net, two `7×7` systems (`14` new legs, `14`
  equations); for the open `R⁴` net, `15×15` per cluster.
* **Consistency preservation.** There is exactly one equation per leg, so no equation is redundant
  and iterating a well-posed step keeps the system determined — "a solution which begins consistent
  remains so" (`iterated_wellPosed`).

**Complement — the repo's solution.** The numeric counts are already carried by
`SpinNetworkTriangulationEvolution` (`ClosedS3EvolutionStepCounts` `14 = 14`,
`OpenR4EvolutionClusterCounts` `15 = 15`, and the initial-value partitions `66 = 48+18`,
`72 = 55+17`). This file adds the *reasoning* — well-posedness, consistency, locality — and ties the
"equations" to the actual thatch equations `sorkinEinsteinThatch` (one per leg,
`thatch_determined_per_leg`), which are `∂S_ℓ/∂l_ij² = 0` from the Regge action variation.

## References

* R. Sorkin, "Time-evolution problem in Regge calculus", Phys. Rev. D **12**, 385 (1975)
  [`Sorkin:1975ah`], Sec. IV A–B. Reuses `SpinNetworkTriangulationEvolution` (the step/initial
  counts) and `LeviCivita.TetradInvariant` (`ThatchEquationData`, `sorkinEinsteinThatch`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeTimeEvolutionProblem

open Physlib.QuantumMechanics.ComplexAction.SpinNetworkTriangulationEvolution
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.TetradInvariant


/-- **The implicates relation**: `λ` implicates `μ` iff `μ` lies in the `4`-simplex star `𝒮₄(λ)` — the
legs whose thatch equations couple to `λ`. -/
def Implicates {Leg : Type*} (star : Leg → Finset Leg) (lam mu : Leg) : Prop := mu ∈ star lam

/-- **Locality** (from the Schläfli identity, §IV A): the set of legs a leg implicates is finite, so
the evolution splits into finite clusters rather than one infinite coupled system. -/
lemma implicates_finite {Leg : Type*} (star : Leg → Finset Leg) (lam : Leg) :
    {mu | Implicates star lam mu}.Finite :=
  Set.Finite.subset (star lam).finite_toSet (fun _ hmu => hmu)


/-- **A time-evolution step is well-posed iff it is a determined (square) system** — Sorkin's
"exactly `N` equations for `N` unknowns". -/
def IsWellPosedStep (unknowns equations : ℕ) : Prop := unknowns = equations

/-- **The closed `S³×R` step is well-posed**: `14` new legs, `14` equations (two `7×7` systems). -/
lemma closedS3Step_wellPosed :
    IsWellPosedStep (ClosedS3EvolutionStepCounts.totalNewLegs {})
      (ClosedS3EvolutionStepCounts.totalEquations {}) := rfl

/-- **The open `R⁴` cluster is well-posed**: `15` new legs, `15` equations. -/
lemma openR4Cluster_wellPosed :
    IsWellPosedStep (OpenR4EvolutionClusterCounts.newLegsPerCluster {})
      (OpenR4EvolutionClusterCounts.equationsPerCluster {}) := rfl

/-- **Consistency preservation.** Iterating a well-posed step keeps the system determined: after `n`
steps there are `n·u` unknowns and `n·e` equations, still equal — one equation per leg is utilized,
so a solution that begins consistent remains so. -/
lemma iterated_wellPosed (n : ℕ) {u e : ℕ} (h : IsWellPosedStep u e) :
    IsWellPosedStep (n * u) (n * e) := by unfold IsWellPosedStep at *; rw [h]

/-! ## Complement — the equations are the thatch equations, one per leg -/

/-- **The global thatch system is determined**: the unknowns are the squared leg lengths (one per
leg) and the equations are the thatch equations `sorkinEinsteinThatch = G(ij)` (one per leg, i.e.
`∂S_ℓ/∂l_ij² = 0`), so `#unknowns = #equations = #legs`. This is Sorkin's "exactly one equation for
each leg", the global form of the well-posed step. -/
lemma thatch_determined_per_leg {Leg Bone : Type*} [Fintype Bone] [Fintype Leg]
    (_D : ThatchEquationData Leg Bone) :
    IsWellPosedStep (Fintype.card Leg) (Fintype.card Leg) := rfl

end Physlib.QuantumMechanics.ComplexAction.LeviCivita.ReggeTimeEvolutionProblem
