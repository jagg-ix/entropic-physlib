/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenBenderDunneComplexMoment
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneSorkinJohnston
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition

/-!
# The Nagao–Nielsen complex coordinate *is* the Sorkin–Johnston Wightman two-point

`BenderDunneSorkinJohnston` showed the Bender–Dunne time-of-arrival kernel `(q+q')sgn(q−q')` is a
Pauli–Jordan function feeding the Sorkin–Johnston vacuum. `NagaoNielsenBenderDunneComplexMoment` put that time
operator on the **complexified phase space** `q = E/c + i·p` (Nagao–Nielsen). This module fuses the two: the
Hermitian pairing `q̄_j q_k` of the NN complex coordinates is *already* an SJ Wightman two-point function, split
canonically as

`q̄_j q_k = Re(q̄_j q_k) + i·Im(q̄_j q_k)  =  A(j,k) + (i/2)·Δ(j,k)`,

with `A = Re(q̄_j q_k)` the **symmetric Hadamard** part and `Δ = 2·Im(q̄_j q_k)` the **antisymmetric Pauli–Jordan**
part — the SJ decomposition `W = A + (i/2)Δ` (`SorkinJohnstonRegionState.wightmanTwoPoint`). Because the diagonal
`Re(q̄_k q_k) = |q_k|² ≥ 0` is automatically positive, the NN complex phase space realizes a Sorkin–Johnston state
**unconditionally** — no separate positivity input is needed.

Physically, `Δ(j,k) = 2 Im(q̄_j q_k) = (2/c)(E_j p_k − E_k p_j)` is the antisymmetric energy–momentum (symplectic)
pairing — the Peierls commutator on the complex phase space — while `A(j,k) = (E_j E_k)/c² + p_j p_k` is the
symmetric part. This closes the loop: NN complex coordinate → SJ Wightman → SJ state → (decoherence functional →
quantum measure `I₃ = 0`, `QuantumMeasureHistoryHilbert`).

* **§A — the three kernels.** `nnWightman q = q̄_j q_k`; `nnHadamard q = Re(q̄_j q_k)`; `nnPauliJordan q =
  2 Im(q̄_j q_k)`. **`nnWightman_isHermitian`**, with **`nnHadamard_symmetric`** / **`nnPauliJordan_isPauliJordan`**
  obtained as instances of the general `Re + i·Im` principle (`SorkinJohnstonHermitianDecomposition`).
* **§B — the SJ decomposition.** **`nnWightman_eq`** (`nnWightman = wightmanTwoPoint (nnHadamard) (nnPauliJordan)`),
  **`nnWightman_diag_re`** (`Re(q̄_k q_k) = |q_k|²`).
* **§C — the SJ state, unconditionally.** **`nnWightman_isSJState`** and its specialization
  **`nnComplexCoordinate_isSJState`** (the mass-shell coordinate `q = E/c + i·p` seeds an SJ vacuum).

**Honest layering.** All are exact `Complex`-part / `ring` identities. The downstream decoherence-functional and
`I₃ = 0` steps are `QuantumMeasureHistoryHilbert`'s existing results (cited terminus). This module supplies the
missing identification tying the Nagao–Nielsen complexification to the Sorkin–Johnston construction.

## References

* Nagao & Nielsen, arXiv:1304.4017; Johnston, arXiv:0909.0944; Sorkin, *Mod. Phys. Lett. A* **9** (1994) 3119.
  Merges `NagaoNielsenBenderDunneComplexMoment` with `BenderDunneSorkinJohnston`.


-/

set_option autoImplicit false

open Complex
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonHermitianDecomposition
open Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenBenderDunneComplexMoment

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenSorkinJohnston

variable {ι : Type*} {n : ℕ}


/-- The **Nagao–Nielsen Wightman two-point** `W(j,k) = q̄_j q_k` — the Hermitian pairing of the complex
phase-space coordinates. -/
noncomputable def nnWightman (q : ι → ℂ) (j k : ι) : ℂ := (starRingEnd ℂ) (q j) * q k

/-- The **Hadamard (symmetric) part** `A(j,k) = Re(q̄_j q_k) = (E_j E_k)/c² + p_j p_k`. -/
noncomputable def nnHadamard (q : ι → ℂ) (j k : ι) : ℝ := ((starRingEnd ℂ) (q j) * q k).re

/-- The **Pauli–Jordan (antisymmetric) part** `Δ(j,k) = 2 Im(q̄_j q_k) = (2/c)(E_j p_k − E_k p_j)` — the
symplectic energy–momentum pairing, the Peierls commutator on the complex phase space. -/
noncomputable def nnPauliJordan (q : ι → ℂ) (j k : ι) : ℝ := 2 * ((starRingEnd ℂ) (q j) * q k).im

/-- **The NN Wightman is a Hermitian kernel** `q̄_j q_k = conj(q̄_k q_j)` — so it falls under the general
`Re + i·Im` Sorkin–Johnston decomposition of `SorkinJohnstonHermitianDecomposition`, and the three kernels here
are its `hadamardPart` / `pauliJordanPart` (definitionally). -/
lemma nnWightman_isHermitian (q : ι → ℂ) : IsHermitianKernel (nnWightman q) := by
  intro j k
  simp only [nnWightman, map_mul, Complex.conj_conj]
  ring

/-- **The Hadamard part is a symmetric kernel** — the instance `hadamardPart_symmetric` of the general principle:
`nnHadamard q` is `Re(nnWightman q)`, symmetric because `nnWightman` is Hermitian. -/
lemma nnHadamard_symmetric (q : ι → ℂ) : IsSymmetricKernel (nnHadamard q) :=
  hadamardPart_symmetric (nnWightman_isHermitian q)

/-- **The Pauli–Jordan part is antisymmetric** — the instance `pauliJordanPart_isPauliJordan`: `nnPauliJordan q` is
`2·Im(nnWightman q)`, antisymmetric by Hermiticity; physically the symplectic `(2/c)(E_j p_k − E_k p_j)`. -/
lemma nnPauliJordan_isPauliJordan (q : ι → ℂ) : IsPauliJordan (nnPauliJordan q) :=
  pauliJordanPart_isPauliJordan (nnWightman_isHermitian q)


/-- **The NN Wightman is the SJ two-point of its own Hadamard/Pauli–Jordan parts**
`q̄_j q_k = A(j,k) + (i/2)Δ(j,k)` — the complex Hermitian pairing splits exactly into the symmetric real part plus
`i/2` the antisymmetric part, the Sorkin–Johnston form `wightmanTwoPoint`. -/
lemma nnWightman_eq (q : ι → ℂ) (j k : ι) :
    nnWightman q j k = wightmanTwoPoint (nnHadamard q) (nnPauliJordan q) j k :=
  congrFun (congrFun (wightmanTwoPoint_hadamardPart_pauliJordanPart (nnWightman q)).symm j) k

/-- **The diagonal is the squared norm** `Re(q̄_k q_k) = |q_k|²` — automatically non-negative, giving SJ positivity
for free. -/
lemma nnWightman_diag_re (q : ι → ℂ) (k : ι) : (nnWightman q k k).re = Complex.normSq (q k) := by
  simp only [nnWightman, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring


/-- **The Nagao–Nielsen complex coordinate seeds a Sorkin–Johnston state** `IsSJState (q̄_j q_k) Δ` — the Hermitian
pairing recovers the Pauli–Jordan commutator and is diagonally positive (`Re(q̄_k q_k) = |q_k|² ≥ 0`), so the NN
complex phase space realizes an SJ vacuum with **no** extra positivity hypothesis. -/
lemma nnWightman_isSJState (q : ι → ℂ) :
    IsSJState (nnWightman q) (nnPauliJordan q) :=
  hermitian_isSJState (nnWightman_isHermitian q)
    (fun k => by rw [nnWightman_diag_re]; exact Complex.normSq_nonneg _)

/-- **The mass-shell coordinate `q = E/c + i·p` seeds an SJ vacuum** — specializing `nnWightman_isSJState` to the
Nagao–Nielsen complex coordinate: the energy–momentum data of `NagaoNielsenBenderDunneComplexMoment` directly
supply a Sorkin–Johnston two-point function, whose Pauli–Jordan part is the symplectic `(2/c)(E_j p_k − E_k p_j)`
and whose Hadamard diagonal is `|q_k|² = (E_k/c)² + p_k²`. -/
lemma nnComplexCoordinate_isSJState (E p : Fin n → ℝ) (c : ℝ) :
    IsSJState (nnWightman (nnComplexCoordinate E p c))
      (nnPauliJordan (nnComplexCoordinate E p c)) :=
  nnWightman_isSJState _

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.NagaoNielsenSorkinJohnston
