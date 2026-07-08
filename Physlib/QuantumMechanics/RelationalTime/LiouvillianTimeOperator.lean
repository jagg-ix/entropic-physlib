/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic

/-!
# The Liouvillian and the conjugate time operator (finite-dimensional foundation)

Reference: B. Misra, I. Prigogine, M. Courbage, *Lyapounov variable: Entropy and
measurement in quantum mechanics*, Proc. Natl. Acad. Sci. USA **76**(10),
4768–4772 (1979), Eq. **[2.8]** and **§3** ("The entropy superoperator").

MPC resolve the no-go of `LyapounovNoGo` (§2) by passing from the Hamiltonian `H`
to the **Liouvillian**, the generator of the time-translation group on density
operators (Eq. **[2.8]**, `L ρ = [H, ρ]`); the dynamical evolution is
`ρ ↦ e^{−iHt} ρ e^{iHt}`. The decisive observation opening §3 is that *"the
generator `L` of the time-translation group is no longer physically required to be
bounded from below. In fact if the spectrum of `H` extends from `0` to `+∞` the
spectrum of `L` is the entire real line."* Unlike `H` (bounded below, `H ≥ 0`), the
Liouvillian is **not semibounded** — its spectrum is symmetric about `0`. That is
exactly what allows a self-adjoint time operator `T` canonically conjugate to `L`
(Eq. **[1.3]**, `i[L, T] = I`) to exist, evading Pauli's theorem (Eq. 2.7), which
forbade one conjugate to the bounded-below `H`.

This file establishes the finite-dimensional structural foundation:

* `liouvillian` — `L X = [H, X]` (MPC Eq. 2.8), with `liouvillian_trace_zero`.
* `liouvillian_conjTranspose` — for Hermitian `H`, `(L X)ᴴ = − L Xᴴ`: the Liouvillian
 anti-commutes with conjugate-transposition.
* `liouvillian_eigen_neg` — **symmetric spectrum**: if `L X = μ X` with `μ` real
 (a Bohr frequency `E_i − E_j`) then `L Xᴴ = −μ Xᴴ`. So every nonzero eigenvalue
 comes paired with its negative — `L` is not semibounded, the structural condition
 for the conjugate time operator. (This is the finite analogue of MPC's §3 case
 (i): for `H` with purely discrete spectrum `L` too is discrete, the symmetric set
 of Bohr frequencies `Eᵢ − Eⱼ`.)

What is **not** done (scope): the operator `T` itself with `i[L,T] = I`
cannot exist in finite dimension — the same trace obstruction as in
`LyapounovNoGo` (`tr[L,T] = 0 ≠ tr(iI)`) applies at the superoperator level. Indeed
MPC's §3 case (i) is sharp: for discrete `H` no entropy superoperator exists; a
genuine `T` requires `H` with *absolutely continuous* spectrum on `[0, ∞)`, so that
`L` has continuous spectrum of uniform multiplicity over all of `ℝ`. In the spectral
representation `L` becomes multiplication by `λ ∈ ℝ` and `T = i d/dλ` — formalized
in `LiouvillianAgeOperator`. The finite-dimensional content here is precisely the
*necessary condition* — the non-semibounded, symmetric Liouvillian spectrum.
-/

set_option autoImplicit false

open scoped Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.RelationalTime

variable {d : Type*} [Fintype d]

/-- The **Liouvillian** `L X = [H, X] = H X − X H` (MPC Eq. 2.8, `L ρ = [H, ρ]`):
the generator of the unitary conjugation flow `ρ ↦ e^{−iHt} ρ e^{iHt}` on
operators, i.e. of the time-translation group in the Liouvillian formulation. -/
def liouvillian (H X : Matrix d d ℂ) : Matrix d d ℂ := H * X - X * H

/-- The Liouvillian has zero trace on every argument (`tr[H, X] = 0`): the trace
obstruction that, at the superoperator level, forbids a finite-dimensional time
operator with `i[L, T] = I` (MPC Eq. 1.3) — the reason MPC's §3 needs a genuinely
infinite system with continuous spectrum. -/
theorem liouvillian_trace_zero (H X : Matrix d d ℂ) : (liouvillian H X).trace = 0 := by
  simp only [liouvillian, Matrix.trace_sub, Matrix.trace_mul_comm H X, sub_self]

/-- **The Liouvillian anti-commutes with conjugate-transposition** (`H` Hermitian):
`(L X)ᴴ = − L Xᴴ`. -/
theorem liouvillian_conjTranspose {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (X : Matrix d d ℂ) : (liouvillian H X)ᴴ = - liouvillian H Xᴴ := by
  simp only [liouvillian, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hH.eq, neg_sub]

/-- **Symmetric Liouvillian spectrum** (the finite shadow of MPC's §3 remark that
the spectrum of `L` fills the whole real line). If `X` is an eigen-operator of the
Liouvillian with a real eigenvalue `μ` (a Bohr frequency `E_i − E_j`), then `Xᴴ` is
an eigen-operator with eigenvalue `−μ`. So the spectrum of `L` is symmetric about
`0`: every nonzero eigenvalue is paired with its negative, and `L` is **not
semibounded** — the structural condition (unavailable to the bounded-below `H`)
that permits a self-adjoint time operator `T` conjugate to `L` (Eq. 1.3). -/
theorem liouvillian_eigen_neg {H : Matrix d d ℂ} (hH : H.IsHermitian)
    (X : Matrix d d ℂ) (μ : ℝ) (heig : liouvillian H X = (μ : ℂ) • X) :
    liouvillian H Xᴴ = ((-μ : ℝ) : ℂ) • Xᴴ := by
  have key : liouvillian H Xᴴ = -(liouvillian H X)ᴴ := by
    rw [liouvillian_conjTranspose hH X, neg_neg]
  rw [key, heig, Matrix.conjTranspose_smul]
  simp [neg_smul]

end Physlib.QuantumMechanics.RelationalTime

end
