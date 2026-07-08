/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.ComplexHamiltonian

/-!
# The inner product `I_Q` (Born rule) and the Heisenberg picture (Nagao–Nielsen §4.2, §4.5)

This file links the periodic Q-Hermitian `Q`-formalism (`PeriodicQHermitian.Basic`) to two sections of
**K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys.
126(6) (2011) 1021 = arXiv:1104.3381** — the paper that *introduces* this `Q`-formalism
(§4.3, Eqs. (4.11)–(4.22): the proper inner product `I_Q(ψ₂,ψ₁) = ⟨ψ₂|Q|ψ₁⟩`, the
`Q`-conjugate `A^{†Q} = Q⁻¹A†Q`, and `Q`-Hermiticity `A^{†Q} = A`).

## §4.2 — Physical significance of an inner product (the Born rule)

The Born rule (§4.2): a state `|i⟩` time-developing to `|i(t_f)⟩ = e^{−iH(t_f−t_i)}|i⟩` is
measured in `|f⟩` with probability `|⟨f|i(t_f)⟩|²` — *which depends on the choice of inner
product*. Nagao–Nielsen argue the physical probability must use the proper `I_Q` (so the
non-orthogonal eigenstates of the non-Hermitian `H` become orthogonal, Eq. (4.12)), and
that `Q = Q†` (Eq. (4.15)). The observable content is that the `I_Q`-expectation of a
physical (`Q`-Hermitian) observable is **real**:

* `qInner Q ψ₂ ψ₁ = ⟨ψ₂|Q|ψ₁⟩` — the form `I_Q` (Eq. 4.11). `star_qInner_self` is the form's
  *paper fact* that `⟨ψ|M|ψ⟩^* = ⟨ψ|M†|ψ⟩`.
* `QmulA_isHermitian_of_qHermitian` — **§4.3, Eq. (4.21) remark**: `O` is `Q`-Hermitian iff
  `Q·O` is Hermitian (`QA = (QA)†`). *Formalized here.*
* `qExpect_qHermitian_real` — **the Born-rule reality**: for a `Q`-Hermitian observable `O`,
  `⟨ψ|Q O|ψ⟩ ∈ ℝ` (equals its own conjugate). *This work*, built from the paper's facts;
  it is the precise statement that `I_Q` makes measured expectation values real.

## §4.5 — The Heisenberg picture and the modified Heisenberg equation

In the `I_Q`-normalized theory (Eq. 4.34–4.36) the Heisenberg operator is
`O_QH(t) ∝ e^{(i/ℏ)H^{†Q}t} O e^{−(i/ℏ)Ht}` (Eq. 4.37), and its rate is the **modified
Heisenberg equation** (Eq. 4.39)

  `iℏ dO_QH/dt = [O_QH, H_Qh] + {O_QH, H_Qa − ⟨H_Qa⟩}`,

a commutator with the `Q`-Hermitian part *and* an anticommutator with the
anti-`Q`-Hermitian part. Its `−iℏ`-generator `O·H − H^{†Q}·O` is:

* `qDagger_eq_qHermPart_sub` — `H^{†Q} = H_Qh − H_Qa` (the dual of `H = H_Qh + H_Qa`).
* `heisenbergQ_split` — **Eq. (4.39) bare form**: `O·H − H^{†Q}·O = [O, H_Qh] + {O, H_Qa}`
  (commutator with `H_Qh`, anticommutator with `H_Qa`). *Formalized here.*
* `heisenbergQ_of_qHermitian` — **Eq. (4.41) limit**: when `H` is `Q`-Hermitian
  (`H_Qa = 0`) the rate is the ordinary commutator `[O, H]`, the standard Heisenberg
  equation — i.e. `(i/ℏ)·` of it is `PeriodicQHermitian.Ehrenfest.heisenbergGen ℏ H O`. *This work.*

So the `Q`-Hermitian part `H_Qh = H_R` drives the reversible (commutator) Heisenberg /
Ehrenfest dynamics, and the anti-`Q`-Hermitian `H_Qa = i P D_I P⁻¹` (= `−i H_I`,
`NonHermitianComplexAction.ComplexHamiltonian`) is the dissipative anticommutator correction — vanishing
exactly when `H_I = 0`.

Reference: K. Nagao, H. B. Nielsen, arXiv:1104.3381, §4.2 (Born rule), §4.3 (`I_Q`, `A^{†Q}`,
Eqs. 4.11–4.22), §4.4 (`Q`-normality, Eqs. 4.26–4.33), §4.5 (Heisenberg picture, Eqs.
4.34–4.41).
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## §4.2 / §4.3 — The proper inner product `I_Q` and Born-rule reality -/

/-- **The proper inner product `I_Q(ψ₂,ψ₁) = ⟨ψ₂|Q|ψ₁⟩`** (Nagao–Nielsen Eq. 4.11). -/
def qInner (Q : Matrix n n ℂ) (ψ₂ ψ₁ : n → ℂ) : ℂ := star ψ₂ ⬝ᵥ Q *ᵥ ψ₁

omit [DecidableEq n] in
/-- **`⟨ψ|M|ψ⟩^* = ⟨ψ|M†|ψ⟩`**: conjugating a diagonal matrix element transposes-conjugates
the operator (a property of the sesquilinear form). -/
theorem star_qInner_self (M : Matrix n n ℂ) (ψ : n → ℂ) :
    star (qInner M ψ ψ) = qInner Mᴴ ψ ψ := by
  rw [qInner, qInner, Matrix.star_dotProduct, star_star, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec]

/-- **`O` is `Q`-Hermitian iff `Q·O` is Hermitian** (Nagao–Nielsen §4.3, Eq. (4.21) remark:
"`QA = (QA)†`"). One direction: `O^{†Q} = O ⇒ (Q O)† = Q O`. -/
theorem QmulA_isHermitian_of_qHermitian {Q O : Matrix n n ℂ} (hQh : Qᴴ = Q)
    (hQ : IsUnit Q.det) (hO : qDagger Q O = O) : (Q * O)ᴴ = Q * O := by
  have hOQ : Oᴴ * Q = Q * O := by
    have h1 : Q * (Q⁻¹ * Oᴴ * Q) = Oᴴ * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQ, Matrix.one_mul]
    simp only [qDagger] at hO
    rw [← h1, hO]
  rw [Matrix.conjTranspose_mul, hQh, hOQ]

/-- **The Born-rule reality** (`I_Q` physical significance, §4.2): the `I_Q`-expectation of a
`Q`-Hermitian observable `O` is real (equals its own complex conjugate),
`⟨ψ|Q O|ψ⟩^* = ⟨ψ|Q O|ψ⟩`. This is what makes `|⟨f|i(t_f)⟩|²` a legitimate probability in the
non-Hermitian theory. -/
theorem qExpect_qHermitian_real (P : Matrix n n ℂ) {O : Matrix n n ℂ} (hP : IsUnit P.det)
    (hO : qDagger (qMetric P) O = O) (ψ : n → ℂ) :
    star (qInner (qMetric P * O) ψ ψ) = qInner (qMetric P * O) ψ ψ := by
  have hQunit : IsUnit (qMetric P).det := by
    have hmul : qMetric P * (P * Pᴴ) = 1 := by
      rw [qMetric, Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹ P, Matrix.nonsing_inv_mul P hP,
        Matrix.one_mul, Matrix.nonsing_inv_mul Pᴴ (isUnit_conjTranspose_det P hP)]
    have hd : (qMetric P).det * (P * Pᴴ).det = 1 := by
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, zero_mul] at hd
    exact zero_ne_one hd
  rw [star_qInner_self, QmulA_isHermitian_of_qHermitian (qMetric_isHermitian P) hQunit hO]

/-! ## §4.5 — The Heisenberg picture and the modified Heisenberg equation -/

variable (P : Matrix n n ℂ) (d : n → ℂ)

/-- **`H^{†Q} = H_Qh − H_Qa`** (dual of `H = H_Qh + H_Qa`, Eq. 4.26): the `Q`-adjoint flips
the sign of the anti-`Q`-Hermitian part. -/
theorem qDagger_eq_qHermPart_sub (Q A : Matrix n n ℂ) :
    qDagger Q A = qHermPart Q A - qAntiHermPart Q A := by
  unfold qHermPart qAntiHermPart; module

/-- The `−iℏ`-generator of the Heisenberg operator `O_QH` (Nagao–Nielsen Eq. 4.37, 4.39):
`O·H − H^{†Q}·O`. -/
noncomputable def heisenbergQ (H O : Matrix n n ℂ) : Matrix n n ℂ :=
  O * H - qDagger (qMetric P) H * O

/-- **The modified Heisenberg equation — bare form** (Nagao–Nielsen Eq. 4.39):
`O·H − H^{†Q}·O = [O, H_Qh] + {O, H_Qa}` — a commutator with the `Q`-Hermitian part `H_Qh`
plus an anticommutator with the anti-`Q`-Hermitian part `H_Qa`. (The `⟨H_Qa⟩` subtraction of
Eq. 4.39 is the state-dependent normalization term, omitted at this operator level.) -/
theorem heisenbergQ_split (O : Matrix n n ℂ) :
    heisenbergQ P (hamiltonian P d) O
      = commutator O (qHermPart (qMetric P) (hamiltonian P d))
        + (O * qAntiHermPart (qMetric P) (hamiltonian P d)
           + qAntiHermPart (qMetric P) (hamiltonian P d) * O) := by
  set a := qHermPart (qMetric P) (hamiltonian P d)
  set b := qAntiHermPart (qMetric P) (hamiltonian P d)
  have hH : hamiltonian P d = a + b :=
    (qHermPart_add_qAntiHermPart (qMetric P) (hamiltonian P d)).symm
  have hHd : qDagger (qMetric P) (hamiltonian P d) = a - b :=
    qDagger_eq_qHermPart_sub (qMetric P) (hamiltonian P d)
  rw [heisenbergQ, hHd, hH, commutator, Matrix.mul_add, Matrix.sub_mul]
  abel

/-- **The Heisenberg equation in the `Q`-Hermitian / classical limit** (Nagao–Nielsen
Eq. 4.41): when `Ĥ` is `Q`-Hermitian (`H_Qa = 0`) the generator is the ordinary commutator
`[O, Ĥ]` — the standard Heisenberg equation. Then `(i/ℏ)·` of it is
`PeriodicQHermitian.Ehrenfest.heisenbergGen ℏ Ĥ O`, the reversible dynamics driven by
`H_Qh = H_R`. -/
theorem heisenbergQ_of_qHermitian (O : Matrix n n ℂ)
    (hH : qDagger (qMetric P) (hamiltonian P d) = hamiltonian P d) :
    heisenbergQ P (hamiltonian P d) O = commutator O (hamiltonian P d) := by
  rw [heisenbergQ, hH, commutator]

end Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

end
