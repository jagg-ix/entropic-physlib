/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet

/-!
# Reeh–Schlieder: the cyclic–separating duality on the Verch local net

Constructs the **Reeh–Schlieder** property of a fermion region's local algebra on the repo's existing
**Verch local net** (`AlgebraicQFTQuasifree.HadamardLocalNet`, `LocalNet`, `HaagDuality`) and **von Neumann commutant**
(`AlgebraicQFT.GNSVonNeumannHadamard`, `commutant = Set.centralizer`). A reference vector `Ω` (the vacuum) is

* **cyclic** for an algebra `M` — its orbit `MΩ` is total: any bounded operator annihilating `MΩ` is zero
  (`IsCyclic`);
* **separating** for `M` — no nonzero element of `M` annihilates `Ω` (`IsSeparating`),

and the **Reeh–Schlieder duality** ties the two across the commutant: a vector cyclic for the commutant `M'`
is separating for `M` (`separating_of_cyclic_commutant`), and cyclic for `M` is separating for `M'`
(`separating_commutant_of_cyclic`) — because `a ∈ M`, `b' ∈ M'` commute, so `a(b'Ω) = b'(aΩ)`.

On the Verch local net with **Haag duality** `R(O^⊥)' = R(O)`, this gives the standard statement: a vector
cyclic for the causal-complement algebra `R(O^⊥)` is separating for the local algebra `R(O)`
(`reehSchlieder_net`). A vector both cyclic and separating (`ReehSchlieder`) is the precondition that
licenses Tomita–Takesaki — the modular operator `Δ_O` and the modular Hamiltonian `K_O = −log Δ_O`
(`ThermoFieldDynamics.KazamaTomitaTakesakiModular`, `modularGenerator`) — for the local algebra of the region.

So the Reeh–Schlieder cyclic-and-separating vector is the missing precondition of the repo's Tomita/modular
arc: it is what makes the local fermion algebra's modular flow exist, and Haag duality converts cyclicity on
the complement into separation on the region.

* **§A — cyclic and separating** (`IsSeparating`, `IsCyclic`, `ReehSchlieder`).
* **§B — the Reeh–Schlieder duality** (`separating_of_cyclic_commutant`, `separating_commutant_of_cyclic`).
* **§C — Reeh–Schlieder on the Verch local net** (`reehSchlieder_net`).

## References

* H. Reeh, S. Schlieder (1961); R. Verch (Schmidt–Verch, local net + Haag duality). structures:
  `AlgebraicQFTQuasifree.HadamardLocalNet` (`LocalNet`, `HaagDuality`), `AlgebraicQFT.GNSVonNeumannHadamard` (`commutant`),
  `ThermoFieldDynamics.KazamaTomitaTakesakiModular` (`modularGenerator`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.GNSVonNeumannHadamard
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## §A — cyclic and separating -/

/-- **[Separating] no nonzero element of `M` annihilates `Ω`.** `a ∈ M`, `aΩ = 0 ⟹ a = 0` — the vector `Ω`
distinguishes the elements of the algebra. -/
def IsSeparating (M : Set (H →L[ℂ] H)) (Ω : H) : Prop :=
  ∀ a ∈ M, a Ω = 0 → a = 0

/-- **[Cyclic] the orbit `MΩ` is total.** Any bounded operator annihilating every `bΩ` (`b ∈ M`) is zero —
the operator-theoretic statement that `MΩ` is dense. -/
def IsCyclic (M : Set (H →L[ℂ] H)) (Ω : H) : Prop :=
  ∀ a : H →L[ℂ] H, (∀ b ∈ M, a (b Ω) = 0) → a = 0

/-- **The Reeh–Schlieder property**: `Ω` is cyclic and separating for `M`. -/
def ReehSchlieder (M : Set (H →L[ℂ] H)) (Ω : H) : Prop :=
  IsCyclic M Ω ∧ IsSeparating M Ω

/-! ## §B — the Reeh–Schlieder duality -/

/-- **[Cyclic for the commutant ⟹ separating] `Ω` cyclic for `M'` ⟹ `Ω` separating for `M`.** If `a ∈ M`
kills `Ω` then it kills the total set `M'Ω` (as `a(b'Ω) = b'(aΩ) = 0` by commutation), hence `a = 0`. -/
theorem separating_of_cyclic_commutant (M : Set (H →L[ℂ] H)) (Ω : H)
    (hcyc : IsCyclic (commutant M) Ω) : IsSeparating M Ω := by
  intro a haM haΩ
  apply hcyc
  intro b' hb'
  have hcomm : a * b' = b' * a := Set.mem_centralizer_iff.mp hb' a haM
  rw [← ContinuousLinearMap.mul_apply, hcomm, ContinuousLinearMap.mul_apply, haΩ]
  exact map_zero b'

/-- **[Cyclic ⟹ separating for the commutant] `Ω` cyclic for `M` ⟹ `Ω` separating for `M'`.** If `a' ∈ M'`
kills `Ω` then it kills the total set `MΩ` (as `a'(bΩ) = b(a'Ω) = 0`), hence `a' = 0`. -/
theorem separating_commutant_of_cyclic (M : Set (H →L[ℂ] H)) (Ω : H)
    (hcyc : IsCyclic M Ω) : IsSeparating (commutant M) Ω := by
  intro a' ha' ha'Ω
  apply hcyc
  intro b hb
  have hcomm : a' * b = b * a' := (Set.mem_centralizer_iff.mp ha' b hb).symm
  rw [← ContinuousLinearMap.mul_apply, hcomm, ContinuousLinearMap.mul_apply, ha'Ω]
  exact map_zero b

/-! ## §C — Reeh–Schlieder on the Verch local net -/

/-- **[Reeh–Schlieder on the local net] cyclic for `R(O^⊥)` ⟹ separating for `R(O)`.** On the Verch local
net with Haag duality `R(O^⊥)' = R(O)`, a vector cyclic for the causal-complement algebra `R(O^⊥)` is
separating for the local algebra `R(O)` of the region — the Reeh–Schlieder property of the fermion region. -/
theorem reehSchlieder_net {ι : Type*} [Preorder ι] (N : LocalNet (H →L[ℂ] H) ι) (O : ι) (Ω : H)
    (hdual : HaagDuality N O) (hcyc : IsCyclic (N.alg (N.compl O)) Ω) :
    IsSeparating (N.alg O) Ω := by
  have h := separating_commutant_of_cyclic (N.alg (N.compl O)) Ω hcyc
  have hd : commutant (N.alg (N.compl O)) = N.alg O := hdual
  rwa [hd] at h

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating

end
