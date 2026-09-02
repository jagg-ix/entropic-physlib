/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.LovelockDimensionalTermination
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.GKPWittenAdSCFTDictionary

/-!
# Holographic dimensional reduction of the Lovelock terms: which curvature order survives in `AdS_{d+1}`

The GKP–Witten dictionary (`AdSCFT.GKPWittenAdSCFTDictionary`) maps a bulk field in `AdS_{d+1}` to a
boundary operator of the `d`-dimensional CFT (of dimension `conformalDimension d μ`), and the
Ryu–Takayanagi area law (`AdSCFT.RyuTakayanagiFormulaAlgebra`) reduces the bulk geometry's
entanglement entropy to a boundary surface. Reading Lovelock's dimensional termination
(`Curvature.LovelockDimensionalTermination`) through this holographic reduction fixes **which curvature
order can be a dynamical bulk correction to a given boundary `CFT_d`**.

For the holographic bulk `AdS_{d+1}` (spacetime dimension `D = d + 1`), the order-`n` Lovelock tensor
term carries `2n + 1` indices, so it is a dynamical field iff `2n + 1 ≤ D = d + 1`, i.e. iff the boundary
CFT dimension satisfies `d ≥ 2n`:

* **§A — the threshold.** `lovelock_dynamical_iff_boundary_dim` (`d ≥ 2n`),
  `einstein_dynamical_iff_boundary_ge_two` (`n = 1`: `d ≥ 2`, the AdS₃/CFT₂ threshold at which the
  Ryu–Takayanagi geodesic first computes a boundary entropy), `gaussBonnet_dynamical_iff_boundary_ge_four`
  (`n = 2`: `d ≥ 4`, so the leading Lovelock correction enters the dictionary only at the AdS₅/CFT₄ level).
* **§B — the critical boundary.** `lovelock_topological_at_critical_boundary`: at `d = 2n − 1` (bulk
  `AdS_{2n}`, Dadhich's critical dimension) the order-`n` tensor term vanishes — the density is a total
  derivative reducing to a pure boundary term, carrying no dynamical bulk field to source a boundary
  operator.

This is the bulk-gravity input to the holographic reduction: the boundary dimension `d` that the GKP–Witten
`conformalDimension` and the Ryu–Takayanagi area law are written over is exactly the dimension counter that
Lovelock's generalized-Kronecker termination acts on.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AdSCFT.LovelockHolographicDimensionalReduction

open Physlib.QuantumMechanics.ComplexAction.Curvature


/-- **The holographic Lovelock survival threshold**: in the bulk `AdS_{d+1}` (spacetime dimension
`d + 1`) the order-`n` Lovelock tensor term is a dynamical field — `0 < genKroneckerTrace (d+1) (2n+1)` —
iff the boundary `CFT_d` dimension satisfies `d ≥ 2n`. The GKP–Witten boundary operator
`GKPWittenAdSCFTDictionary.conformalDimension d μ` lives at the same boundary dimension `d`. -/
lemma lovelock_dynamical_iff_boundary_dim (n d : ℕ) :
    0 < LovelockDimensionalTermination.genKroneckerTrace (d + 1) (2 * n + 1) ↔ 2 * n ≤ d := by
  rw [LovelockDimensionalTermination.lovelockTensorTerm_pos_iff]; omega

/-- **Einstein gravity in the holographic bulk**: the `n = 1` term is dynamical in `AdS_{d+1}` iff the
boundary CFT dimension is `d ≥ 2` — the AdS₃/CFT₂ threshold at which the Ryu–Takayanagi geodesic (RT §B)
first computes a boundary entropy. -/
lemma einstein_dynamical_iff_boundary_ge_two (d : ℕ) :
    0 < LovelockDimensionalTermination.genKroneckerTrace (d + 1) 3 ↔ 2 ≤ d := by
  have h := lovelock_dynamical_iff_boundary_dim 1 d
  simpa using h

/-- **Gauss–Bonnet in the holographic bulk**: the `n = 2` term is dynamical in `AdS_{d+1}` iff the
boundary CFT dimension is `d ≥ 4` — the leading Lovelock correction enters the AdS/CFT dictionary only at
the AdS₅/CFT₄ level. -/
lemma gaussBonnet_dynamical_iff_boundary_ge_four (d : ℕ) :
    0 < LovelockDimensionalTermination.genKroneckerTrace (d + 1) 5 ↔ 4 ≤ d := by
  have h := lovelock_dynamical_iff_boundary_dim 2 d
  simpa using h


/-- **The Dadhich critical dimension is the topological / pure-boundary regime**: at the boundary
dimension `d = 2n − 1` (bulk `AdS_{2n}`) the order-`n` Lovelock tensor term vanishes — the density is a
total derivative reducing to a boundary term, with no dynamical bulk field. One step up, at `d = 2n`
(bulk `AdS_{2n+1}`), `lovelock_dynamical_iff_boundary_dim` turns the term on. -/
lemma lovelock_topological_at_critical_boundary (n : ℕ) :
    LovelockDimensionalTermination.genKroneckerTrace (2 * n) (2 * n + 1) = 0 := by
  rw [LovelockDimensionalTermination.genKroneckerTrace_eq_zero_iff]; omega

end Physlib.QuantumMechanics.ComplexAction.AdSCFT.LovelockHolographicDimensionalReduction

end
