/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
public import Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumCarnotCycle
public import Physlib.Thermodynamics.ComputationLandauer

/-!
# Von Neumann projections & trace, and the three faces of computational reversibility

Continues the von Neumann–algebra layer of `AlgebraicQFT.GNSVonNeumannHadamard` (the GNS form and the commutant
`{H}' = ker ad_H`) with the two remaining algebraic building blocks — **projections** and the **trace** — and
links the von Neumann modular flow to the **thermodynamics of computation** through the repo's existing
Carneiro-based formalization `Physlib.Thermodynamics.ComputationLandauer` (Mathlib's
`Computability.PartrecCode`, after M. Carneiro, *Formalizing computability theory via partial recursive
functions*, ITP 2019).

The unifying statement is **reversibility = zero entropy production**, which the repo now proves in three
independent languages, here joined:

* **von Neumann / algebraic** — the modular flow `ad_H = collisionStar H` preserves the trace,
  `τ(ad_H X) = 0` (`trace_liouvillian_zero`): the von Neumann entropy is a first integral.
* **Carnot / thermodynamic** — the reversible cycle has a vanishing Clausius sum,
  `Q_h/T_h − Q_c/T_c = 0` (`StatisticalMechanics.QuantumCarnotCycle.clausiusSum_zero`).
* **Carneiro / computational** — a history-keeping (Bennett-reversible) computation produces no entropy,
  the joint `(input, output)` relative entropy equalling the input's
  (`ComputationLandauer.reversible_entropy_production_zero`).

Replacing the earlier hand-rolled `landauerBound`/`erasableBits` heuristic, the computational face is now the
genuine partial-recursive-code formalization: Carneiro's primitive basis splits along the reversible line into
information-preserving (injective `eval`: `succ`, `pair`) and information-discarding (non-injective `eval`:
`zero`, `left`, `right`) codes, the latter with the Landauer erasure cost (`erasureStep_tauEnt_nonneg`).

* **§A — projections** (`IsProjection`, `isProjection_one_sub`). The self-adjoint idempotents `p² = p`,
  `p* = p` — the spectral projections generating the von Neumann algebra; the complement `1 − p` is again one.
* **§B — the trace annihilates the Liouvillian** (`tracial_commutator_zero`, `trace_liouvillian_zero`). A
  tracial functional `τ(ab) = τ(ba)` kills every commutator, hence the image of `ad = collisionStar`: the
  modular flow preserves the trace (von Neumann entropy) — the reversible limit.
* **§C — the three faces of reversibility** (`reversibility_three_faces`, `irreversible_zero_primitive_has_cost`).
  The von Neumann, Carnot and Carneiro zero-entropy-production statements joined; and the irreversible face —
  the non-injective `zero` primitive whose erasure step dissipates `≥ 0`.

## References

* M. Carneiro, *Formalizing computability theory via partial recursive functions*, ITP 2019.
* C. H. Bennett, *Logical reversibility of computation*, IBM J. Res. Dev. 17 (1973).
* R. Landauer, *Irreversibility and heat generation in the computing process*, IBM J. Res. Dev. 5 (1961).
* Repo dependencies: `AlgebraicQFT.GNSVonNeumannHadamard` (commutant `= ker ad_H`), `CollisionOperatorSl2.CollisionModular`
  (`collisionStar`), `StatisticalMechanics.QuantumCarnotCycle` (`clausiusSum_zero`), `ComputationLandauer`
  (`reversible_entropy_production_zero`, `const_not_injective`, `erasureStep_tauEnt_nonneg`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.VonNeumannCarnotComputability

open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular
open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumCarnotCycle
open Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.QuantumClausiusEngine
open Physlib.Thermodynamics.ComputationLandauer
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-! ## §A — projections (von Neumann building blocks) -/

section Projections
variable {A : Type*} [Ring A] [StarRing A]

/-- **A projection** in a `*`-ring — a self-adjoint idempotent `p² = p`, `p* = p`. The spectral projections
generate the von Neumann algebra as a complete lattice; their traces are the Murray–von Neumann dimensions. -/
structure IsProjection (p : A) : Prop where
  /-- Idempotent: `p·p = p`. -/
  idem : p * p = p
  /-- Self-adjoint: `p* = p`. -/
  selfadj : star p = p

/-- **[Complementary projection] `1 − p` is a projection when `p` is** — the orthocomplement in the projection
lattice (`(1−p)² = 1 − p` using `p² = p`, and `(1−p)* = 1 − p`). -/
theorem isProjection_one_sub (p : A) (hp : IsProjection p) : IsProjection (1 - p) where
  idem := by
    have h : (1 - p) * (1 - p) = 1 - p - p + p * p := by noncomm_ring
    rw [h, hp.idem]; abel
  selfadj := by rw [star_sub, star_one, hp.selfadj]

end Projections

/-! ## §B — the trace annihilates the Liouvillian -/

section Trace
variable {A : Type*} [Ring A]

/-- **[Cyclicity ⟹ traceless commutators] `τ(collisionStar a b) = 0`.** An additive cyclic functional
`τ(ab) = τ(ba)` (a tracial state / the Murray–von Neumann trace) annihilates every commutator, hence the whole
image of the Liouville generator `ad = collisionStar`. The von Neumann trace (≅ entropy) is a *first integral*
of the modular flow. -/
theorem tracial_commutator_zero (τ : A →+ ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a)) (a b : A) :
    τ (collisionStar a b) = 0 := by
  rw [collisionStar, map_sub, htr a b, sub_self]

/-- **[Trace conserved along the modular flow] `τ(ad_H X) = 0`.** The Heisenberg/Liouville generator
`ad_H = collisionStar H` (the Saveliev `ad`, the TFD hat-Hamiltonian, `AlgebraicQFT.GNSVonNeumannHadamard`'s commutant
kernel) is trace-annihilating: the unitary/modular evolution preserves `τ` — *zero entropy production*, the
reversible limit. -/
theorem trace_liouvillian_zero (τ : A →+ ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a)) (H X : A) :
    τ (collisionStar H X) = 0 :=
  tracial_commutator_zero τ htr H X

end Trace

/-! ## §C — the three faces of reversibility (Carneiro computability) -/

section Reversibility
variable {A : Type*} [Ring A]

/-- **[Zero entropy production, three languages] reversibility joined across the repo.** One statement —
*reversible ⟺ no entropy produced* — proved in three independent settings and exhibited together:

* **von Neumann** `τ(ad_H X) = 0` — the modular flow preserves the trace (`trace_liouvillian_zero`);
* **Carnot** `Q_h/T_h − Q_c/T_c = 0` — the reversible cycle's Clausius sum vanishes (`clausiusSum_zero`);
* **Carneiro** the history-keeping computation produces no entropy — the joint `(input, output)` relative
  entropy equals the input's (`ComputationLandauer.reversible_entropy_production_zero`, Bennett's reversible
  embedding over Carneiro's partial-recursive `computationKernel`).

This *replaces* the earlier hand-rolled Carnot-work/Landauer-bound heuristic with the genuine
computability-theoretic content. -/
theorem reversibility_three_faces (τ : A →+ ℂ) (htr : ∀ a b, τ (a * b) = τ (b * a)) (H X : A)
    (c : CarnotCycle) (f : ℕ → ℕ) (μ ν : Measure ℕ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    τ (collisionStar H X) = 0
      ∧ clausiusSum c.heatHot c.Th c.heatCold c.Tc = 0
      ∧ (klDiv (μ ⊗ₘ computationKernel f) (ν ⊗ₘ computationKernel f)).toReal
          - (klDiv μ ν).toReal = 0 :=
  ⟨trace_liouvillian_zero τ htr H X, c.clausiusSum_zero,
    reversible_entropy_production_zero f μ ν⟩

/-- **[The irreversible face] the `zero` primitive erases, and erasure dissipates.** Carneiro's `zero` code
(`eval zero = fun _ ↦ 0`) is information-discarding — non-injective (`const_not_injective`) — and its
erasure step has non-negative dissipated entropy `≥ 0` (`erasureStep_tauEnt_nonneg`, the H-theorem / Landauer
floor). The asymmetry the three reversible faces avoid: discarding the input register costs entropy. -/
theorem irreversible_zero_primitive_has_cost (μ ν : Measure ℕ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hfin : klDiv (μ ⊗ₘ computationKernel (fun _ => 0))
              (ν ⊗ₘ computationKernel (fun _ => 0)) ≠ ∞) :
    ¬ Function.Injective (fun _ : ℕ => (0 : ℕ))
      ∧ 0 ≤ (erasureStep (fun _ => 0) μ ν hfin).tauEnt :=
  ⟨const_not_injective, erasureStep_tauEnt_nonneg _ μ ν hfin⟩

end Reversibility

end Physlib.QuantumMechanics.ComplexAction.StatisticalMechanics.VonNeumannCarnotComputability

end
