/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CausalOrthogonalityQuasiLocalNet

/-!
# Entanglement requires noncommutativity of both factors (Labuschagne–Majewski §3.2, Prop. 3.9)

Formalizes the algebraic core of the entanglement characterization of Labuschagne–Majewski (arXiv:2503.14107,
Prop. 3.9): for a composite system `𝓜 ⊗ 𝒩`, the natural positive cone `𝒫⁺` (the states) equals the convex hull
`𝒫₀⁺` of product states — i.e. **all states are separable** — *iff either factor is commutative*; if both factors
are noncommutative, entangled states exist (`𝒫⁺ ≠ 𝒫₀⁺`). Noncommutativity of *both* parties is the precondition
for quantum (non-classical) correlations.

The algebraic content — realized here through the repository's `commutant` — is that a **commutative (classical)
factor is central**, and therefore contributes only classical correlations:

* a factor is **classical** exactly when it is contained in its own commutant (`IsClassicalFactor`,
 `classicalFactor_comm`) — a commutative algebra of observables;
* a **classical factor causally independent from another is central**: it commutes with *everything* in the joint
 system (`classical_factor_central`), so no entanglement can be generated across it — the algebraic shadow of
 Prop. 3.9's "either factor commutative ⟹ 𝒫⁺ = 𝒫₀⁺";
* in a quasi-local net, a **classical local region is central** among the observables it is causally independent
 from (`quasiLocalNet_classical_region_central`), so its correlations are separable; entanglement of two regions
 requires *both* local algebras to be noncommutative.

So the presence of entanglement is an algebraic property: it needs quantum (noncommuting) observables on *both*
sides — a classical factor is central and yields only separable, classical correlations.

* **§A — a classical factor is its own subcommutant** (`IsClassicalFactor`, `classicalFactor_comm`).
* **§B — a classical factor is central** (`classical_factor_central`).
* **§C — a classical region of a quasi-local net is central** (`quasiLocalNet_classical_region_central`).

`IsClassicalFactor`, its commutativity, and the centrality facts are exact reuse of
`commutant` (`Set.centralizer`). This is the *algebraic* characterization (a commutative factor is central); the
full state-cone statement of Prop. 3.9 (`𝒫⁺ = 𝒫₀⁺` as sets of normal states) is not built — the positive cone,
separable-state convex hull, and Reeh–Schlieder vacuum entanglement are recorded, not formalized. No new axioms.

## References

* L.E. Labuschagne, W.A. Majewski, arXiv:2503.14107, §3.2, Prop. 3.9 (entanglement ⟺ both factors noncommutative).
 Repo dependencies: `AlgebraicQFT.GNSVonNeumannHadamard` (`commutant`),
 `AlgebraicQFTQuasifree.CausalOrthogonalityQuasiLocalNet` (`QuasiLocalNet`).

No new axioms.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.CausalOrthogonalityQuasiLocalNet

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.EntanglementNoncommutativeFactors

variable {A : Type*} [Monoid A]

/-! ## §A — a classical factor is its own subcommutant -/

/-- **A classical (commutative) factor** — a set of observables contained in its own commutant, `S ⊆ S'`. Its
elements pairwise commute: a *classical* algebra of observables with only classical correlations. -/
def IsClassicalFactor (S : Set A) : Prop := S ⊆ commutant S

/-- **[A classical factor's observables commute] `a, b ∈ S ⟹ a·b = b·a`.** A classical factor is a commutative
set of observables. -/
theorem classicalFactor_comm {S : Set A} (h : IsClassicalFactor S) {a b : A} (ha : a ∈ S)
    (hb : b ∈ S) : a * b = b * a :=
  ((h ha) b hb).symm

/-! ## §B — a classical factor is central -/

/-- **[A classical factor causally independent from another is central] `S ⊆ (S ∪ T)'`.** If `S` is classical
(`S ⊆ S'`) and commutes with `T` (`S ⊆ T'`, causal independence of the two factors), then `S` commutes with
*everything* in the joint system `S ∪ T`: it is central. A commutative factor generates no entanglement — the
algebraic content of Prop. 3.9's "either factor commutative ⟹ all states separable". -/
theorem classical_factor_central {S T : Set A} (hcl : IsClassicalFactor S) (hind : S ⊆ commutant T) :
    S ⊆ commutant (S ∪ T) := by
  unfold commutant IsClassicalFactor at *
  rw [Set.centralizer_union]
  exact Set.subset_inter hcl hind

/-! ## §C — a classical region of a quasi-local net is central -/

/-- **[A classical local region of a quasi-local net is central] `𝒜(α) ⊆ (𝒜(α) ∪ 𝒜(β))'`.** If the local
algebra of a region `α` is classical (commutative) and `α` is causally independent from `β`, then `𝒜(α)`
commutes with all observables of both regions — it is central and generates only classical (separable)
correlations. Entanglement of two regions of the net requires *both* local algebras to be noncommutative
(Prop. 3.9). -/
theorem quasiLocalNet_classical_region_central {ι : Type*} [Preorder ι] (Q : QuasiLocalNet A ι)
    {α β : ι} (hcl : IsClassicalFactor (Q.alg α)) (h : Q.causal.orth α β) :
    Q.alg α ⊆ commutant (Q.alg α ∪ Q.alg β) :=
  classical_factor_central hcl (Q.causalIndependence h)

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.EntanglementNoncommutativeFactors

end
