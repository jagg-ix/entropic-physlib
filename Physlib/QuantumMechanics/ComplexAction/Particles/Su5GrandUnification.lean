/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector

/-!
# A. `SU(5)` Grand Unification

The capstone of the gauge sector: the `SU(5)` grand-unified theory (Georgi–Glashow) unifies colour `SU(3)`,
weak `SU(2)`, and hypercharge `U(1)` into a single `SU(5)`, and one Standard-Model fermion generation into
`5̄ ⊕ 10`. This file records the branching arithmetic under `SU(5) → SU(3)_C × SU(2)_L × U(1)_Y`, built on the
`SU(N)` adjoint dimensions of `SuNGaugeSector` and completing the `Su5` charge/representation modules.

* **§A — the `24` gauge bosons.** **`su5_gauge_decomp`** (`24 = 8 + 3 + 1 + 12`): the `SU(5)` adjoint
  (`sunAdjointDim 5 = 24`) splits into the `8` gluons (`sunAdjointDim 3`), the `3` weak bosons
  (`sunAdjointDim 2`), the `1` hypercharge boson, and the `12` new `X/Y` leptoquark bosons (`(3,2) ⊕ (3̄,2)`)
  that mediate proton decay. `standardModel_gauge_bosons` (`8 + 3 + 1 = 12`, the SM gauge bosons) and
  `leptoquark_count` (`24 − 12 = 12`).
* **§B — the fermion generation `5̄ ⊕ 10`.** `su5_fund_decomp` (`5 = 3 + 2`, the `5` = colour-triplet
  down-quark `(3,1)` ⊕ lepton doublet `(1,2)`); `su5_ten_decomp` (`10 = 6 + 3 + 1`, the `10 = Λ²(5)` = quark
  doublet `(3,2)` ⊕ up-antiquark `(3̄,1)` ⊕ positron `(1,1)`); `su5_generation_dim` (`5 + 10 = 15` chiral
  fermions per generation, `10 = C(5,2)`).

## A.1. References

* H. Georgi, S. L. Glashow (1974), `SU(5)` unification; `24 = (8,1)⊕(1,3)⊕(1,1)⊕(3,2)⊕(3̄,2)`,
  `5̄ ⊕ 10` generation. Built on `Particles.SuNGaugeSector` (`sunAdjointDim`); completes
  `Particles.Su5ChargeQuantizationCartanTensor` / `Su5TenRepresentation` (the `5̄`/`10` charges).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.Su5GrandUnification

/-! ## A.2. The `24` Gauge Bosons -/

/-- **The `SU(5)` gauge bosons branch as `24 = 8 + 3 + 1 + 12`** under `SU(5) → SU(3)_C × SU(2)_L × U(1)_Y`:
the `8` gluons (`sunAdjointDim 3`), the `3` weak bosons (`sunAdjointDim 2`), the `1` hypercharge boson, and the
`12` new `X/Y` leptoquark bosons `(3,2) ⊕ (3̄,2)` (the proton-decay mediators). -/
lemma su5_gauge_decomp : sunAdjointDim 5 = sunAdjointDim 3 + sunAdjointDim 2 + 1 + 12 := by decide

/-- **The Standard-Model gauge bosons are `12`** `8 + 3 + 1` — gluons, `W`, and hypercharge `B`. -/
lemma standardModel_gauge_bosons : sunAdjointDim 3 + sunAdjointDim 2 + 1 = 12 := by decide

/-- **The `X/Y` leptoquark bosons are `12`** `24 − 12` — the new `SU(5)` gauge bosons beyond the Standard
Model, mediating proton decay. -/
lemma leptoquark_count : sunAdjointDim 5 - (sunAdjointDim 3 + sunAdjointDim 2 + 1) = 12 := by decide

/-! ## A.3. The Fermion Generation `5̄ ⊕ 10` -/

/-- **The fundamental `5` branches as `5 = 3 + 2`**: the colour-triplet down-quark `(3,1)` plus the lepton
doublet `(1,2)`. -/
lemma su5_fund_decomp : 5 = 3 + 2 := by decide

/-- **The `10 = Λ²(5)` branches as `10 = 6 + 3 + 1`**: the quark doublet `(3,2)` (`6`), the up-antiquark
`(3̄,1)` (`3`), and the positron `(1,1)` (`1`). -/
lemma su5_ten_decomp : Nat.choose 5 2 = 6 + 3 + 1 := by decide

/-- **A generation is `5̄ ⊕ 10 = 15` chiral fermions** `5 + C(5,2) = 5 + 10 = 15`: the anti-fundamental `5̄`
plus the antisymmetric `10 = Λ²(5)` complete one Standard-Model generation. -/
lemma su5_generation_dim : 5 + Nat.choose 5 2 = 15 := by decide

end Physlib.QuantumMechanics.ComplexAction.Particles.Su5GrandUnification
