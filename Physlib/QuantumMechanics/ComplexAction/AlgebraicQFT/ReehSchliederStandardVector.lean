/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating

/-!
# The standard (cyclic-and-separating) vacuum vector — the Tomita precondition

Completes the Reeh–Schlieder construction (`AlgebraicQFT.ReehSchliederCyclicSeparating`) by producing the **standard
vector** of a local algebra: a vector that is **both cyclic and separating** for `R(O)`, which is exactly
the precondition of Tomita–Takesaki modular theory (the modular operator `Δ_O = S*S` and the modular
Hamiltonian `K_O = −log Δ_O` exist for a standard vector).

On the Verch local net with **Haag duality** `R(O^⊥)' = R(O)`, a vacuum vector `Ω` that is cyclic for *both*
the region algebra `R(O)` and its causal complement `R(O^⊥)` is **standard** for `R(O)`
(`reehSchlieder_standard`):

* cyclic for `R(O)` is given;
* separating for `R(O)` follows from cyclicity for `R(O^⊥)` via the Reeh–Schlieder duality and Haag duality
  (`reehSchlieder_net`).

So the Reeh–Schlieder vacuum — cyclic for every local algebra and its complement — is a standard vector for
each region, and therefore includes the region's modular flow. This is the missing precondition that
licenses the repo's Tomita/modular arc (`ThermoFieldDynamics.KazamaTomitaTakesakiModular`, `PTSymmetricQFT.ModularFlowBoundedOp`,
the Bisognano–Wichmann wedge `K` of `AlgebraicQFT.SummersVacuumModularLinks`) on the local fermion algebra.

* **§A — the standard vector** (`reehSchlieder_standard`).

## References

* H. Reeh, S. Schlieder; M. Tomita, M. Takesaki (modular theory of a standard vector). structures:
  `AlgebraicQFT.ReehSchliederCyclicSeparating` (`ReehSchlieder`, `IsCyclic`, `reehSchlieder_net`),
  `AlgebraicQFTQuasifree.HadamardLocalNet` (`HaagDuality`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederStandardVector

open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederCyclicSeparating

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## §A — the standard vector -/

/-- **[The Reeh–Schlieder vacuum is a standard vector] cyclic for `R(O)` and `R(O^⊥)` ⟹ cyclic and
separating for `R(O)`.** On the Verch local net with Haag duality `R(O^⊥)' = R(O)`, a vector cyclic for both
the region algebra and its causal complement is **standard** for `R(O)` — cyclic and separating — the
precondition of Tomita–Takesaki modular theory. Its modular operator `Δ_O` and modular Hamiltonian
`K_O = −log Δ_O` exist, so the region has a modular flow. -/
theorem reehSchlieder_standard {ι : Type*} [Preorder ι] (N : LocalNet (H →L[ℂ] H) ι) (O : ι) (Ω : H)
    (hdual : HaagDuality N O) (hcycO : IsCyclic (N.alg O) Ω)
    (hcycComp : IsCyclic (N.alg (N.compl O)) Ω) :
    ReehSchlieder (N.alg O) Ω :=
  ⟨hcycO, reehSchlieder_net N O Ω hdual hcycComp⟩

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ReehSchliederStandardVector

end
