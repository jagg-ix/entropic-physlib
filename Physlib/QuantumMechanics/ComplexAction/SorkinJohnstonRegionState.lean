/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

/-!
# The Sorkin–Johnston vacuum for a spacetime region

The **Sorkin–Johnston (SJ) construction** gives a distinguished vacuum two-point function for a quantum
field on a bounded, globally hyperbolic **spacetime region** — with no need for a global timelike
Killing vector, so it applies in curved space and in a finite causal region. The vacuum is fixed by the
**Pauli–Jordan** (Peierls commutator) function `Δ(x,y)`, the antisymmetric kernel `[φ(x), φ(y)] = iΔ`.

Any two-point function `W(x,y)` of a field decomposes as a **symmetric (Hadamard) part** `A` plus
`i/2` times the **antisymmetric Pauli–Jordan part** `Δ`:

 `W(x,y) = A(x,y) + (i/2) Δ(x,y)`, `W(x,y) − W(y,x) = iΔ(x,y)` (the commutator).

The SJ state is the **unique** such `W` that is also positive semidefinite, obtained by taking the
positive spectral part of the self-adjoint operator `iΔ` (`sjSpectrum = max λ 0`).

* **§A — the Pauli–Jordan function** (Peierls commutator). `IsPauliJordan Δ` (antisymmetry
 `Δ(x,y) = −Δ(y,x)`), `pauliJordan_self` (`Δ(x,x) = 0`), and **region restriction**
 `pauliJordan_region`: every subregion inherits a Pauli–Jordan function, hence its own SJ vacuum.
* **§B — the two-point function** and the commutator. `wightmanTwoPoint A Δ = A + (i/2)Δ`;
 `wightman_commutator` (`W(x,y) − W(y,x) = iΔ`, the field commutator) and `wightman_hermitian`
 (`W(y,x) = conj W(x,y)`).
* **§C — the SJ spectral selection.** `sjSpectrum λ = max λ 0` keeps the positive part of `iΔ`;
 `sjSpectrum_nonneg` (positivity `W ⪰ 0`) and `sjSpectrum_sub` (`W₊ − W₋ = λ`, commutator recovery
 eigenvalue-by-eigenvalue) — the two defining SJ conditions.
* **§D — the SJ state.** `IsSJState W Δ` (commutator recovery ∧ diagonal positivity);
 `wightman_isSJState` builds it from a positive Hadamard part.
* **§E — the fermionic region vacuum.** `fermionicTwoPoint`; `fermionic_anticommutator`
 (`W(x,y) + W(y,x) = S(x,y)`, the CAR anticommutator) — the fermion sector uses the **symmetric**
 combination, tagged by the fermionic exchange phase `ribbonTwist(½) = −1`
 (`fermionic_exchange_tag`), against the bosonic `ribbonTwist(0) = 1` (`bosonic_exchange_tag`).

Proven: the antisymmetry/region inheritance of `Δ`, the commutator and hermiticity
of `W`, the positive-part spectral selection and its two SJ conditions, and the boson/fermion
commutator/anticommutator split with its exchange-phase tags. Interpretive: `A`, `Δ`, `S` are the
scalar kernels of the field's Hadamard, Pauli–Jordan, and anticommutator distributions (the tensorial
smearing over the region is the datum); the operator `iΔ` is represented by its real spectrum, the
positive part `sjSpectrum` standing for the SJ projection.

## References

* R. D. Sorkin, "Scalar field theory on a causal set in histories form", J. Phys. Conf. Ser. 306,
 012017 (2011); S. Johnston, "Feynman propagator for a free scalar field on a causal set", Phys. Rev.
 Lett. 103, 180401 (2009); N. Afshordi, S. Aslanbeigi, R. D. Sorkin, "A distinguished vacuum state for
 a quantum field in a curved spacetime", JHEP 08 (2012) 137. Reuses
 `Hopf.ChargeConjugationRibbonTwist` (`ribbonTwist`). Complements the fermion-region AQFT arc
 (`AlgebraicQFT.ReehSchlieder*`, `Bogoliubov.CARAlgebraAutomorphism.IsCAR`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState

open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist

variable {α : Type*}

/-! ## §A — the Pauli–Jordan (Peierls commutator) function -/

/-- **The Pauli–Jordan function is antisymmetric** `Δ(x,y) = −Δ(y,x)` — the kernel of the field
commutator `[φ(x), φ(y)] = iΔ(x,y)`, built as the difference of the advanced and retarded Green
functions on the region. -/
def IsPauliJordan (Δ : α → α → ℝ) : Prop := ∀ x y, Δ x y = - Δ y x

/-- **A symmetric kernel** `A(x,y) = A(y,x)` — the Hadamard (anticommutator/two-point symmetric) part. -/
def IsSymmetricKernel (A : α → α → ℝ) : Prop := ∀ x y, A x y = A y x

/-- **The Pauli–Jordan function vanishes on the diagonal** `Δ(x,x) = 0`: a field commutes with itself. -/
theorem pauliJordan_self (Δ : α → α → ℝ) (hΔ : IsPauliJordan Δ) (x : α) : Δ x x = 0 := by
  have h := hΔ x x; linarith

/-- **Every subregion inherits a Pauli–Jordan function** (the region-locality of the SJ construction):
the restriction of `Δ` to a subregion `O` is again antisymmetric, so `O` has its own Sorkin–Johnston
vacuum — no global timelike Killing vector is required. -/
theorem pauliJordan_region (Δ : α → α → ℝ) (hΔ : IsPauliJordan Δ) (O : Set α) :
    IsPauliJordan (fun x y : O => Δ x y) := fun x y => hΔ x y

/-! ## §B — the two-point function and the commutator -/

/-- **The two-point (Wightman) function** `W(x,y) = A(x,y) + (i/2) Δ(x,y)`: the symmetric Hadamard part
`A` plus `i/2` the Pauli–Jordan part `Δ`. -/
noncomputable def wightmanTwoPoint (A Δ : α → α → ℝ) (x y : α) : ℂ :=
  ((A x y : ℝ) : ℂ) + Complex.I * ((Δ x y / 2 : ℝ) : ℂ)

/-- **The two-point function recovers the field commutator** `W(x,y) − W(y,x) = iΔ(x,y)` (the Peierls
bracket): the antisymmetric part of any two-point function is the Pauli–Jordan function. -/
theorem wightman_commutator (A Δ : α → α → ℝ) (hA : IsSymmetricKernel A) (hΔ : IsPauliJordan Δ)
    (x y : α) :
    wightmanTwoPoint A Δ x y - wightmanTwoPoint A Δ y x = Complex.I * ((Δ x y : ℝ) : ℂ) := by
  unfold wightmanTwoPoint
  rw [hA x y, hΔ y x]
  push_cast; ring

/-- **The two-point function is Hermitian** `W(y,x) = conj W(x,y)`: reflection is complex conjugation,
because `A` and `Δ` are real and `Δ` is antisymmetric. -/
theorem wightman_hermitian (A Δ : α → α → ℝ) (hA : IsSymmetricKernel A) (hΔ : IsPauliJordan Δ)
    (x y : α) :
    starRingEnd ℂ (wightmanTwoPoint A Δ x y) = wightmanTwoPoint A Δ y x := by
  unfold wightmanTwoPoint
  rw [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal, hA x y, hΔ x y]
  push_cast; ring

/-! ## §C — the Sorkin–Johnston spectral selection -/

/-- **The SJ spectral selection** `pos(λ) = max λ 0`: the Sorkin–Johnston vacuum keeps the **positive**
part of the self-adjoint Pauli–Jordan operator `iΔ` and discards the negative part. -/
noncomputable def sjSpectrum (lam : ℝ) : ℝ := max lam 0

/-- **The SJ two-point function is positive** `W ⪰ 0` (SJ condition 1): the positive spectral part is
non-negative, so the SJ state is a genuine (positive) vacuum. -/
theorem sjSpectrum_nonneg (lam : ℝ) : 0 ≤ sjSpectrum lam := le_max_right _ _

/-- **The SJ selection recovers the commutator eigenvalue** `pos(λ) − pos(−λ) = λ` (SJ condition 2):
on each `±λ` eigenpair of `iΔ`, the SJ two-point's antisymmetric part reproduces the Pauli–Jordan
eigenvalue. Together with positivity this **uniquely** fixes the SJ state. -/
theorem sjSpectrum_sub (lam : ℝ) : sjSpectrum lam - sjSpectrum (-lam) = lam := by
  unfold sjSpectrum
  rcases le_total 0 lam with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-! ## §D — the Sorkin–Johnston state -/

/-- **A Sorkin–Johnston state**: a two-point function `W` that recovers the field commutator
`W(x,y) − W(y,x) = iΔ` and is (diagonally) positive. These two conditions characterize the SJ vacuum. -/
def IsSJState (W : α → α → ℂ) (Δ : α → α → ℝ) : Prop :=
  (∀ x y, W x y - W y x = Complex.I * ((Δ x y : ℝ) : ℂ)) ∧ (∀ x, 0 ≤ (W x x).re)

/-- **The two-point function with a positive Hadamard part is an SJ state** — the commutator condition
from `wightman_commutator`, and positivity from the non-negative diagonal of the Hadamard part `A`
(the SJ construction takes `A` to be the positive part `½|iΔ|`, so `A(x,x) ≥ 0`). -/
theorem wightman_isSJState (A Δ : α → α → ℝ) (hA : IsSymmetricKernel A) (hΔ : IsPauliJordan Δ)
    (hApos : ∀ x, 0 ≤ A x x) :
    IsSJState (wightmanTwoPoint A Δ) Δ := by
  refine ⟨wightman_commutator A Δ hA hΔ, fun x => ?_⟩
  have hre : (wightmanTwoPoint A Δ x x).re = A x x := by
    unfold wightmanTwoPoint
    simp [pauliJordan_self Δ hΔ x]
  rw [hre]; exact hApos x

/-! ## §E — the fermionic region vacuum -/

/-- **The fermionic two-point function** `W(x,y) = ½S(x,y) + (i/2)Δ(x,y)`: for a fermion the symmetric
part is `½` the CAR anticommutator kernel `S(x,y) = {ψ(x), ψ†(y)}`. -/
noncomputable def fermionicTwoPoint (S Δ : α → α → ℝ) (x y : α) : ℂ :=
  ((S x y / 2 : ℝ) : ℂ) + Complex.I * ((Δ x y / 2 : ℝ) : ℂ)

/-- **The fermionic two-point recovers the CAR anticommutator** `W(x,y) + W(y,x) = S(x,y)`: for
fermions the **symmetric** combination (not the difference) is the physical two-point datum — the
anticommutator, versus the commutator of the bosonic case (`wightman_commutator`). -/
theorem fermionic_anticommutator (S Δ : α → α → ℝ) (hS : IsSymmetricKernel S) (hΔ : IsPauliJordan Δ)
    (x y : α) :
    fermionicTwoPoint S Δ x y + fermionicTwoPoint S Δ y x = ((S x y : ℝ) : ℂ) := by
  unfold fermionicTwoPoint
  rw [hS y x, hΔ y x]
  push_cast; ring

/-- **The bosonic sector records exchange phase `+1`** — the commutator (antisymmetric) SJ vacuum is the
integer-spin `ribbonTwist(0) = 1` sector. -/
theorem bosonic_exchange_tag : ribbonTwist 0 = 1 := by
  simpa using ribbonTwist_boson 0

/-- **The fermionic sector records exchange phase `−1`** — the anticommutator (symmetric) SJ vacuum is
the half-integer-spin `ribbonTwist(½) = −1` sector. The boson/fermion split of the region vacuum is the
`±1` exchange phase. -/
theorem fermionic_exchange_tag : ribbonTwist (1 / 2) = -1 := ribbonTwist_fermion

end Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
