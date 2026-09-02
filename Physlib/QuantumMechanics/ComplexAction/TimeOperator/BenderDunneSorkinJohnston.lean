/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneOperatorAnalytic
public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneDensity
public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
public import Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance

/-!
# The Bender–Dunne kernel is a Pauli–Jordan function: entry into the Sorkin–Johnston chain

The densely-defined (`BenderDunneDensity.benderDunneDomain_dense`) Bender–Dunne time-of-arrival operator
`T_{−1,1}` has kernel `(T_{−1,1})(q,q') = (q + q') sgn(q − q')` (`BenderDunneOperatorAnalytic.arrivalKernel`). Its
antisymmetric factor `sgn(q − q')` makes the whole kernel **antisymmetric** under `q ↔ q'` — it is a
**Pauli–Jordan function** (`SorkinJohnstonRegionState.IsPauliJordan`), the Peierls-commutator datum that seeds the
Sorkin–Johnston vacuum. This module makes that identification and threads it into the existing SJ / quantum-measure
edifice, giving the end-to-end chain

`antisymmetric kernel J = arrivalKernel` **(§A)**  →  `Pauli–Jordan kernel` **(§A)**  →
`SJ Wightman two-point W = A + (i/2)J` **(§C)**  →  `SJ state IsSJState` **(§C)**  →
`decoherence functional` / `quantum measure` obeying `I₃ = 0`
(`QuantumMeasureHistoryHilbert.sorkin_third_order_sum_rule`, the downstream target).

The link is sharp: `sgn(q − q')` is literally the **causal sign** of the order on `ℝ`
(`CausalSetIntervalAbundance.causalSign`, §B) — so the time/position order on the line is itself the causal-set
input that supplies the Pauli–Jordan function. The Bender–Dunne singular kernel and the SJ commutator function are
the same antisymmetric object.

* **§A — the kernel is Pauli–Jordan.** **`arrivalKernel_isPauliJordan`** (`arrivalKernel` is antisymmetric).
* **§B — it is the causal sign.** **`sign_sub_eq_causalSign`** (`sgn(q − q') = causalSign q' q`) and
  **`arrivalKernel_eq_causalSign`** (`arrivalKernel q q' = (q + q')·causalSign q' q`).
* **§C — the Sorkin–Johnston vacuum it seeds.** **`benderDunne_wightman_commutator`** (the two-point function
  recovers `iΔ`) and **`benderDunne_wightman_isSJState`** (with any positive Hadamard part `A`, `W = A + (i/2)J`
  is an SJ state) — the two-point datum feeding the decoherence functional and Sorkin's `I₃ = 0` quantum measure.

**Honest layering.** §A–§B are exact `Real.sign`/`ring` identities; §C instantiates the field-general SJ theorems
(`wightman_commutator`, `wightman_isSJState`) at `Δ = arrivalKernel`, so the SJ construction transports verbatim.
The final decoherence-functional / `I₃ = 0` step is `QuantumMeasureHistoryHilbert`'s existing result, which holds
for any decoherence functional built from such a two-point function; it is cited as the chain's terminus, not
re-proved here.

## References

* Bunao & Galapon, arXiv:1509.00340; Sorkin, *Mod. Phys. Lett. A* **9** (1994) 3119; Johnston, arXiv:0909.0944.
  Bridges `BenderDunneOperatorAnalytic` / `BenderDunneDensity` into `SorkinJohnstonRegionState`,
  `CausalSetIntervalAbundance`, and `QuantumMeasureHistoryHilbert`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneOperatorAnalytic
open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.CausalSetIntervalAbundance

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneSorkinJohnston


/-- **The Bender–Dunne time-of-arrival kernel is a Pauli–Jordan function** `arrivalKernel(q,q') =
−arrivalKernel(q',q)` — the symmetric factor `(q+q')` times the antisymmetric `sgn(q−q')` is antisymmetric under
`q ↔ q'`, so the singular kernel of `T_{−1,1}` is exactly a Peierls-commutator (Pauli–Jordan) datum. -/
lemma arrivalKernel_isPauliJordan : IsPauliJordan arrivalKernel := by
  intro x y
  unfold arrivalKernel
  rw [show y - x = -(x - y) from by ring, Real.sign_neg]
  ring

/-- **The kernel vanishes on the diagonal** `arrivalKernel(q,q) = 0` — a field commutes with itself; here the
`sgn(0) = 0` at coincident points. -/
lemma arrivalKernel_diag (q : ℝ) : arrivalKernel q q = 0 :=
  pauliJordan_self arrivalKernel arrivalKernel_isPauliJordan q


/-- **The Bender–Dunne sign kernel is the causal sign of the order on `ℝ`** `sgn(q − q') = causalSign q' q` — the
line's own time/position order is the causal-set datum supplying the Pauli–Jordan function. -/
lemma sign_sub_eq_causalSign (q q' : ℝ) : Real.sign (q - q') = causalSign q' q := by
  unfold causalSign
  rcases lt_trichotomy q' q with h | h | h
  · rw [Real.sign_of_pos (by linarith), if_pos h]
  · subst h; rw [sub_self, Real.sign_zero, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
  · rw [Real.sign_of_neg (by linarith), if_neg (not_lt.mpr h.le), if_pos h]

/-- **The kernel in causal-order form** `arrivalKernel q q' = (q + q')·causalSign q' q` — the Bender–Dunne kernel
factors as the symmetric weight times the causal sign of the order. -/
lemma arrivalKernel_eq_causalSign (q q' : ℝ) :
    arrivalKernel q q' = (q + q') * causalSign q' q := by
  unfold arrivalKernel; rw [sign_sub_eq_causalSign]


/-- **The SJ two-point function recovers the Bender–Dunne kernel as its commutator** `W(x,y) − W(y,x) =
i·arrivalKernel(x,y)` — for any symmetric Hadamard part `A`, the Peierls commutator of `W = A + (i/2)arrivalKernel`
is the Bender–Dunne kernel itself. -/
lemma benderDunne_wightman_commutator (A : ℝ → ℝ → ℝ) (hA : IsSymmetricKernel A) (x y : ℝ) :
    wightmanTwoPoint A arrivalKernel x y - wightmanTwoPoint A arrivalKernel y x
      = Complex.I * ((arrivalKernel x y : ℝ) : ℂ) :=
  wightman_commutator A arrivalKernel hA arrivalKernel_isPauliJordan x y

/-- **The Bender–Dunne kernel seeds a Sorkin–Johnston vacuum** `IsSJState (A + (i/2)arrivalKernel) arrivalKernel` —
with any symmetric, diagonally-positive Hadamard part `A` (the SJ choice being the positive part `½|iΔ|`), the
two-point function `W = A + (i/2)arrivalKernel` is a Sorkin–Johnston state: it recovers the Pauli–Jordan
commutator and is diagonally positive. This `W` is the two-point datum that enters the decoherence functional and
Sorkin's `I₃ = 0` quantum measure (`QuantumMeasureHistoryHilbert`). -/
lemma benderDunne_wightman_isSJState (A : ℝ → ℝ → ℝ) (hA : IsSymmetricKernel A)
    (hApos : ∀ x, 0 ≤ A x x) :
    IsSJState (wightmanTwoPoint A arrivalKernel) arrivalKernel :=
  wightman_isSJState A arrivalKernel hA arrivalKernel_isPauliJordan hApos

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneSorkinJohnston
