/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# A concrete Bose-bilinear realization of the Kálnay composite fermion

`BoseFermiOperatorAlgebra.CompositeFermionCAR` proves that *any* element `f` of a `*`-ring satisfying the CAR
(`IsFermionMode`) includes the full Pauli/number algebra — but it never exhibits such an `f`, so the
construction is left abstract (and its theorems vacuously conditional). This file supplies the **concrete
witness**, realizing Kálnay's bilinear-in-Bose construction `f ∝ ∫ F(z,x,x′) b†(x) b(x′)` (Eq. 2.2.4;
field form Eq. 5.7) in
its exact, interpretation-free core.

**Exact statement.** A *finite* Bose bilinear `Σ Fᵢⱼ bᵢ† bⱼ` cannot satisfy `{f, f†} = 1` as an
operator on the full Fock space — number-conserving bilinears have a quartic `{f, f†}`, never a `c`-number;
the genuine fermion appears only on a *restricted sector*. Taking the simplest kernel binding two Bose modes
`a, b`, the bilinear `f = a† b` (Kálnay's number-conserving bilinear form), **represented on the
single-quantum two-mode sector**
`{|1,0⟩, |0,1⟩}`, *does* satisfy the canonical anticommutation relations exactly. On that 2-dimensional
sector `a† b` is the matrix

 `f = !![0, 1; 0, 0]` over `ℂ` (`boseBilinear`),

with conjugate `f† = a b† = !![0, 0; 1, 0]` (`star_boseBilinear`). It is a fermion mode
(`boseBilinear_isFermionMode`):

 `f² = 0` (Pauli: no double occupation of the single-quantum sector),
 `f f† + f† f = 𝟙` (`{f, f†} = 1`).

Its number operator `n = f† f = !![0, 0; 0, 1]` (`fermionNumber_boseBilinear`) is the projector onto the
occupied mode `|0,1⟩`. Instantiating the abstract algebra on this concrete `f`
(`kalnay_bose_bilinear_realization`) proves `IsFermionMode` as **realizable**, so the Kálnay CAR file is
non-vacuous: a genuine fermion built bilinearly from Bose operators.

The restriction to the single-quantum sector is the exact, finite-dimensional shadow of Kálnay's one-boson
subspace `𝔹₁`; here it is a clean operator identity, *not* the para-statistics / `𝔹₁→𝔹ₚ` "decay" reading
(that is interpretation, excluded).

* **§A — the Bose bilinear and its conjugate** (`boseBilinear`, `star_boseBilinear`).
* **§B — it is a fermion mode** (`boseBilinear_mul_self`, `boseBilinear_isFermionMode`,
 `fermionNumber_boseBilinear`).
* **§C — the realization** (`kalnay_bose_bilinear_realization`).

## References

* A. J. Kálnay, "On Fermi quantum fields constructed from Bose quantum fields" (Eq. 2.2.4 and Eq. 5.7, the
 bilinear kernel). structure: `BoseFermiOperatorAlgebra.CompositeFermionCAR` (`IsFermionMode`, `fermionNumber`,
 `kalnay_composite_fermion`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseBilinearRealization

open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.CompositeFermionCAR

/-! ## §A — the Bose bilinear and its conjugate -/

/-- **The Bose bilinear `f = a† b`** (Kálnay's Eq. 2.2.4/5.7 bilinear form, two modes bound by a `c`-number
kernel), represented on
the single-quantum two-mode sector `{|1,0⟩, |0,1⟩}` as a `2×2` complex matrix. It annihilates `|0,1⟩` into
`|1,0⟩` and kills `|1,0⟩`. -/
def boseBilinear : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- **[The conjugate bilinear] `f† = a b† = !![0,0;1,0]`.** The Hermitian adjoint (conjugate transpose) of the
Bose bilinear on the single-quantum sector. -/
theorem star_boseBilinear : star boseBilinear = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boseBilinear]

/-! ## §B — it is a fermion mode -/

/-- **[Pauli: `f² = 0`] the single-quantum sector forbids double occupation.** -/
theorem boseBilinear_mul_self : boseBilinear * boseBilinear = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boseBilinear, Matrix.mul_apply, Fin.sum_univ_two]

/-- **[The Bose bilinear is a fermion mode] `f² = 0` and `{f, f†} = f f† + f† f = 𝟙`.** The two-mode Bose
bilinear `a† b`, restricted to the single-quantum sector, satisfies the canonical anticommutation relations
exactly — a genuine fermion built from Bose operators (Kálnay's construction, exact core). -/
theorem boseBilinear_isFermionMode : IsFermionMode boseBilinear := by
  refine ⟨boseBilinear_mul_self, ?_⟩
  rw [star_boseBilinear]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boseBilinear, Matrix.add_apply]

/-- **[The number operator] `n = f† f = !![0,0;0,1]`** — the projector onto the occupied mode `|0,1⟩`. -/
theorem fermionNumber_boseBilinear : fermionNumber boseBilinear = !![0, 0; 0, 1] := by
  rw [fermionNumber, star_boseBilinear]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boseBilinear, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## §C — the realization -/

/-- **[The Kálnay composite fermion, concretely realized].** The Bose bilinear `f = a† b` on the single-quantum
two-mode sector is a fermion mode, with number operator the rank-one projector `!![0,0;0,1]`, and it records
the full abstract Pauli algebra of `kalnay_composite_fermion`:

* `f†² = 0`;
* `n = f† f` is self-adjoint and idempotent (`n² = n`) — Pauli exclusion;
* `f` lowers the number, `[n, f] = −f`.

This proves `IsFermionMode` as **realizable**: a genuine fermion built bilinearly from Bose operators,
making the Kálnay CAR construction non-vacuous. -/
theorem kalnay_bose_bilinear_realization :
    IsFermionMode boseBilinear
      ∧ fermionNumber boseBilinear = !![0, 0; 0, 1]
      ∧ star boseBilinear * star boseBilinear = 0
      ∧ star (fermionNumber boseBilinear) = fermionNumber boseBilinear
      ∧ fermionNumber boseBilinear * fermionNumber boseBilinear = fermionNumber boseBilinear
      ∧ fermionNumber boseBilinear * boseBilinear
          - boseBilinear * fermionNumber boseBilinear = -boseBilinear :=
  ⟨boseBilinear_isFermionMode, fermionNumber_boseBilinear,
    (kalnay_composite_fermion boseBilinear boseBilinear_isFermionMode).1,
    (kalnay_composite_fermion boseBilinear boseBilinear_isFermionMode).2.1,
    (kalnay_composite_fermion boseBilinear boseBilinear_isFermionMode).2.2.1,
    (kalnay_composite_fermion boseBilinear boseBilinear_isFermionMode).2.2.2⟩

end Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.BoseBilinearRealization

end
