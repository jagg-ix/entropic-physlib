/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# The conjugate time operator in the spectral representation (`i[L, T] = I`)

Reference: B. Misra, I. Prigogine, M. Courbage, *Lyapounov variable: Entropy and
measurement in quantum mechanics*, Proc. Natl. Acad. Sci. USA **76**(10),
4768–4772 (1979), Eq. **[1.3]** realized in **§3** ("The entropy superoperator").

`LiouvillianTimeOperator` showed that in finite dimension the Liouvillian
`L = ad_H` has a symmetric, non-semibounded spectrum but admits no *exact*
conjugate time operator (the trace obstruction). MPC's internal-time operator —
the self-adjoint `T` "canonically conjugated to the generator `L`", `i[L, T] = I`
(Eq. **[1.3]**), called the operator of *internal time* — lives in the
**infinite-dimensional spectral representation**. MPC §3: when `H` has absolutely
continuous spectrum on `[0, ∞)`, `L` has continuous spectrum of uniform multiplicity
over all of `ℝ`, and *"in the spectral (direct integral) representation that
`diagonalizes` this operator `L` to make it correspond to the multiplication by the
real variable `λ`, this operator `T` can be taken to be the differentiation operator
`i d/dλ`."* That is exactly the construction here.

This is the canonical conjugate pair on a function space — structurally identical
to position/momentum (`x` and `−i d/dx`). On the dense domain of differentiable
functions it satisfies the canonical commutation relation exactly:

* `spectralLiouvillian f λ = λ · f λ`  (`L`, multiplication by the spectral
  variable `λ`),
* `ageOperator f λ = i · f'(λ)`  (`T = i d/dλ`, MPC's internal-time operator),
* `liouvillian_age_commutator` — `[L, T] f = −i f` (pointwise, for differentiable
  `f`),
* `liouvillian_age_ccr` — **`i[L, T] = I`** (MPC Eq. 1.3): the canonical conjugacy
  that makes `T` a genuine time operator conjugate to the (unbounded, full-real-line)
  Liouvillian. Monotone operator functions `M = f(T)` then satisfy the
  entropy-superoperator conditions Eq. 3.1 (`i[L, M] = D ≥ 0`) and Eq. 3.2
  (`[M, D] = 0`).

This realizes the conjugate time operator that finite dimension forbade: here `L`
has continuous spectrum filling `ℝ`, so `T = i d/dλ` exists and `i[L,T] = I` holds.
(The full Hilbert-space self-adjointness / Stone–von Neumann theory of these
unbounded operators, and the nonfactorizability of the resulting entropy
superoperator `M` of MPC §4, are beyond scope; the canonical commutation relation
on the dense domain is the rigorous core.)
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.RelationalTime

/-- The Liouvillian in its spectral representation (MPC §3): **multiplication by
the spectral variable** `λ`, `(L f)(λ) = λ · f(λ)`. The direct-integral form that
diagonalizes `L = ad_H` when `H` has absolutely continuous spectrum on `[0, ∞)`. -/
def spectralLiouvillian (f : ℝ → ℂ) : ℝ → ℂ := fun lam => (lam : ℂ) * f lam

/-- MPC's **internal-time operator** `T = i d/dλ`, `(T f)(λ) = i · f'(λ)`: the
self-adjoint operator canonically conjugate to the Liouvillian `L` in its spectral
representation (MPC §3, "the differentiation operator `i d/dλ`"). -/
noncomputable def ageOperator (f : ℝ → ℂ) : ℝ → ℂ := fun lam => Complex.I * deriv f lam

/-- **Canonical commutator** of the Liouvillian and its internal-time operator:
`[L, T] f = −i f` on the dense domain of differentiable functions (the content of
MPC Eq. 1.3, before multiplying through by `i`). -/
theorem liouvillian_age_commutator (f : ℝ → ℂ) (lam : ℝ)
    (hf : DifferentiableAt ℝ f lam) :
    spectralLiouvillian (ageOperator f) lam - ageOperator (spectralLiouvillian f) lam
      = -Complex.I * f lam := by
  have hx : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 lam := (hasDerivAt_id lam).ofReal_comp
  have hprod : HasDerivAt (spectralLiouvillian f)
      (1 * f lam + (lam : ℂ) * deriv f lam) lam := hx.mul hf.hasDerivAt
  simp only [spectralLiouvillian, ageOperator]
  rw [hprod.deriv]
  ring

/-- **The Misra–Prigogine canonical conjugacy `i[L, T] = I` (Eq. [1.3]).** Applying
`i` to the commutator returns the identity: the internal-time operator `T = i d/dλ`
is canonically conjugate to the Liouvillian `L = ` multiplication by `λ`. This is
the time operator that the finite-dimensional Liouvillian could not support (and
that Pauli's theorem, Eq. 2.7, forbade for the bounded-below `H`) — it exists
precisely because, in the spectral representation, `L` has continuous spectrum
filling the whole real line. Monotone operator functions `M = f(T)` of this `T`
are then the Lyapounov variables / entropy superoperators satisfying MPC Eqs.
3.1–3.2. -/
theorem liouvillian_age_ccr (f : ℝ → ℂ) (lam : ℝ) (hf : DifferentiableAt ℝ f lam) :
    Complex.I * (spectralLiouvillian (ageOperator f) lam
        - ageOperator (spectralLiouvillian f) lam) = f lam := by
  rw [liouvillian_age_commutator f lam hf, ← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg,
    one_mul]

end Physlib.QuantumMechanics.RelationalTime

end
