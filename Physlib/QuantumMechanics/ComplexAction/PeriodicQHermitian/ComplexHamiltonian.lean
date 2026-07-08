/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Ehrenfest

/-!
# The Q-Hermitian split realizes the complex Hamiltonian `H_C = H_R − i H_I`

This file proves that the `Q`-Hermitian decomposition of a complex-action-theory
Hamiltonian *is* the non-Hermitian split `H_C = H_R − i H_I`, and traces the consequence to
the imaginary action `S_I` and the probability decay. The two decompositions come from two
different lines of the literature; the **identification** of them is what is established
here.

## Provenance — forms from the papers vs. forms established in this work

**From the papers (used as given here, not re-derived):**

* *The `Q`-metric formalism* — the metric `Q = (P†)⁻¹P⁻¹`, the `Q`-adjoint
  `A^{†Q} = Q⁻¹A†Q`, the `Q`-Hermitian/anti-`Q`-Hermitian split `Ĥ = Ĥ_Qh + Ĥ_Qa` with
  `Ĥ_Qh = (Ĥ + Ĥ^{†Q})/2`, `Ĥ_Qa = (Ĥ − Ĥ^{†Q})/2`, and the eigenbasis relation
  `Ĥ^{†Q} = P D† P⁻¹` — is **Nagao–Nielsen, *Reality from maximizing overlap in the
  periodic complex action theory*, arXiv:2203.07795, §2** (their `P⁻¹Ĥ^{†Q}P = D†`).
  Formalized in `PeriodicQHermitian.Basic`; here we only consume it.
* *The complex Hamiltonian form* `H_C = H_R − i H_I`, with `H_R = H_R†` Hermitian and
  `H_I = H_I† ≥ 0` positive, and the **norm decay** `d‖ψ‖²/dt = −(2/ℏ)⟨H_I⟩`, are
  **Sergi & Giaquinta 2016, *Linear Quantum Entropy and Non-Hermitian Hamiltonians*,
  Entropy 18(12) 451, doi:10.3390/e18120451** (their Eq. (1) `Ĥ = Ĥ − iΓ̂`, "no-½"
  convention; §II), and — in the rescaled `E_n − iΓ_n/2` convention — **Nagao & Nielsen,
  *Formulation of Complex Action Theory*, Prog. Theor. Phys. 126(6) (2011) 1021**. The
  operator-level structure and the norm decay are `FiniteTarget.NagaoNielsenSchrodinger`.
* *The complex action* `S = S_R + i S_I` and the weight `e^{iS/ℏ}` are Nagao–Nielsen's
  (the complex-action papers above); the modulus `e^{−S_I/ℏ}` is this development's entropic-time
  damping (`RelationalTime.EntropicDamping`, `NonHermitianComplexAction.EntropicDampingEquivalence`; Page–Wootters /
  Lindblad base).

The eigenvalue forms are the paper's: with `D = D_R + i D_I`, `D_R = diagonal(Re λ)`,
`D_I = diagonal(Im λ)` (Eq. 4.29–4.31), Nagao–Nielsen write `H_Qh = P D_R P⁻¹` and
`H_Qa = i P D_I P⁻¹` — **K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*,
Prog. Theor. Phys. 126(6) (2011) 1021 = arXiv:1104.3381, §4.4, Eqs. (4.26)–(4.33)**. So
`qHermPart_eq_HR`/`qAntiHermPart_eq_HI` below are the *formalization* of (4.32)/(4.33), not
new physics; `H_I` here is `−P D_I P⁻¹` so that `−i H_I = i P D_I P⁻¹ = H_Qa`.

**Established in this work (the content of this file):**

* the Lean matrix realization of the above in `Matrix n n ℂ`
  (`hamiltonianHR = P·diagonal(Re λ)·P⁻¹`, `hamiltonianHI = P·diagonal(−Im λ)·P⁻¹`);
* `qHermPart_eq_HR`, `qAntiHermPart_eq_HI`, `hamiltonian_eq_HR_sub_I_HI` — proofs of
  Eqs. (4.32), (4.33), (4.26)+(4.29) and the **sign bridge** to the Sergi–Giaquinta
  packaging `H_C = H_R − i H_I` (`H_I ≥ 0`), which the 1104.3381 convention `H = H_Qh + H_Qa
  = P D_R P⁻¹ + i P D_I P⁻¹` does not write in that form;
* `hamiltonian_sub_qDagger_eq : Ĥ − Ĥ^{†Q} = −2i H_I` and `trace_dissipative_hamiltonian`
  — the new connection identifying the periodic Q-Hermitian probability-decay rate with the
  Sergi–Giaquinta / `NagaoNielsenSchrodinger` norm decay (and the EPT weight `e^{−S_I/ℏ}`).

## The reasoning

`Ĥ = P D P⁻¹` is diagonalized with complex eigenvalues `λ_i = d_i = Re λ_i + i Im λ_i`.
Nagao–Nielsen's `Q`-adjoint conjugates only the eigenvalues, `Ĥ^{†Q} = P D† P⁻¹`
(arXiv:2203.07795 §2; `PeriodicQHermitian.Basic.hamiltonian_qDagger`). So the `Q`-split acts
eigenvalue-by-eigenvalue, and the elementary complex identities `(z + z̄)/2 = Re z` and
`(z − z̄)/2 = i·Im z` give:

* `Ĥ_Qh = P·diagonal((λ + λ̄)/2)·P⁻¹ = P·diagonal(Re λ)·P⁻¹` — a real-diagonal (Hermitian in
  the eigenbasis) generator: this is **`H_R`**. [`qHermPart_eq_HR`]
* `Ĥ_Qa = P·diagonal((λ − λ̄)/2)·P⁻¹ = P·diagonal(i·Im λ)·P⁻¹`; writing it as `−i H_I` with
  `H_I = P·diagonal(−Im λ)·P⁻¹` makes `H_I` `Q`-Hermitian (real eigenvalues `−Im λ`).
  [`qAntiHermPart_eq_HI`]

Adding the two parts (`PeriodicQHermitian.Basic.qHermPart_add_qAntiHermPart`),
`Ĥ = Ĥ_Qh + Ĥ_Qa = H_R + (−i H_I) = H_R − i H_I` — **exactly Sergi–Giaquinta's Eq. (1) /
the NN complex Hamiltonian**. [`hamiltonian_eq_HR_sub_I_HI`]

*Signs and convergence.* For `∫ e^{iS/ℏ}𝒟path` to converge the imaginary parts of the
eigenvalues are bounded above (Nagao–Nielsen); the decaying régime is `Im λ ≤ 0`, i.e.
`H_I` has eigenvalues `−Im λ ≥ 0`, i.e. `H_I ≥ 0` — the positivity Sergi–Giaquinta require
of `Γ̂`.

*Action and damping.* The complex action `S = ∫(p q̇ − H_C)dt` inherits `H_C`'s split into
`S = S_R + i S_I`; the weight modulus `e^{−S_I/ℏ}` (`NonHermitianComplexAction.EntropicDampingEquivalence`) is real damping
sourced by `H_I`. At the density-matrix level the anti-`Q`-Hermitian part is the *only*
obstruction to probability conservation: `Ĥ − Ĥ^{†Q} = −2i H_I`
(`hamiltonian_sub_qDagger_eq`), so the dissipative trace rate is `Tr(ρ̇) = −(2/ℏ)⟨H_I⟩`
(`trace_dissipative_hamiltonian`) — the same `−(2/ℏ)⟨H_I⟩` as the operator norm decay of
`NagaoNielsenSchrodinger` (Sergi–Giaquinta §II). Probability is conserved precisely when
`H_I = 0` (`Ĥ` `Q`-Hermitian, `S_I = 0`, `H_C = H_R`).

## References

* K. Nagao, H. B. Nielsen, *Reality from maximizing overlap in the periodic complex action
  theory*, arXiv:2203.07795, §2 — the `Q`-metric formalism and `Ĥ = Ĥ_Qh + Ĥ_Qa`.
* K. Nagao, H. B. Nielsen, *Formulation of Complex Action Theory*, Prog. Theor. Phys.
  126(6) (2011) 1021 — the complex action `S = S_R + i S_I`; `E_n − iΓ_n/2` convention.
* Sergi & Giaquinta, *Linear Quantum Entropy and Non-Hermitian Hamiltonians*, Entropy
  18(12) (2016) 451, doi:10.3390/e18120451, arXiv:1612.05917 — `H_C = H_R − i H_I` (Eq. 1)
  and the norm decay `d‖ψ‖²/dt = −(2/ℏ)⟨H_I⟩` (§II).
* This development: `PeriodicQHermitian.Basic` (`Q`-formalism), `NagaoNielsenSchrodinger`
  (operator `H_C`, norm decay), `EntropicDamping` / `NonHermitianComplexAction.EntropicDampingEquivalence` (`e^{−S_I/ℏ}`).
-/

set_option autoImplicit false

open Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

variable {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (d : n → ℂ)

/-! ## Conjugation is linear -/

theorem mconj_add (X Y : Matrix n n ℂ) : mconj P (X + Y) = mconj P X + mconj P Y := by
  simp only [mconj, Matrix.mul_add, Matrix.add_mul]

theorem mconj_sub (X Y : Matrix n n ℂ) : mconj P (X - Y) = mconj P X - mconj P Y := by
  simp only [mconj, Matrix.mul_sub, Matrix.sub_mul]

theorem mconj_smul (c : ℂ) (X : Matrix n n ℂ) : mconj P (c • X) = c • mconj P X := by
  simp only [mconj]; rw [mul_smul_comm, smul_mul_assoc]

omit [Fintype n] in
theorem diagonal_ofReal_isHermitian (r : n → ℝ) :
    (diagonal (fun i => (r i : ℂ)))ᴴ = diagonal (fun i => (r i : ℂ)) := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

/-! ## The real and imaginary Hamiltonian parts -/

/-- **`H_R`**: the real-energy (`Q`-Hermitian) part, eigenvalues `Re λ`. -/
noncomputable def hamiltonianHR : Matrix n n ℂ :=
  mconj P (diagonal (fun i => ((Complex.re (d i) : ℝ) : ℂ)))

/-- **`H_I`**: the imaginary part of `H_C = H_R − iH_I`, eigenvalues `−Im λ`. -/
noncomputable def hamiltonianHI : Matrix n n ℂ :=
  mconj P (diagonal (fun i => ((-(Complex.im (d i)) : ℝ) : ℂ)))

/-- `H_R` is `Q`-Hermitian. -/
theorem hamiltonianHR_qHermitian (hP : IsUnit P.det) :
    qDagger (qMetric P) (hamiltonianHR P d) = hamiltonianHR P d :=
  qDagger_mconj_isHermitian P hP (diagonal_ofReal_isHermitian (fun i => Complex.re (d i)))

/-- `H_I` is `Q`-Hermitian (and `Q`-positive when `Im λ ≤ 0`). -/
theorem hamiltonianHI_qHermitian (hP : IsUnit P.det) :
    qDagger (qMetric P) (hamiltonianHI P d) = hamiltonianHI P d :=
  qDagger_mconj_isHermitian P hP (diagonal_ofReal_isHermitian (fun i => -(Complex.im (d i))))

/-! ## The link: `Ĥ_Qh = H_R`, `Ĥ_Qa = −i H_I`, `Ĥ = H_R − i H_I` -/

/-- **`Ĥ_Qh = H_R = P D_R P⁻¹`** — Nagao–Nielsen Eq. (4.32) (arXiv:1104.3381 §4.4), with
`D_R = diagonal(Re λ)`. Formalization here; reasoning: `(λ + λ̄)/2 = Re λ`, so the
`Q`-Hermitian part has the real energies as eigenvalues. -/
theorem qHermPart_eq_HR (hP : IsUnit P.det) :
    qHermPart (qMetric P) (hamiltonian P d) = hamiltonianHR P d := by
  simp only [qHermPart]
  rw [hamiltonian_qDagger P d hP]
  simp only [hamiltonian, hamiltonianHR]
  rw [← mconj_add P, ← mconj_smul P]
  congr 1
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.diagonal_apply_eq, smul_eq_mul,
      Pi.star_apply]
    rw [← starRingEnd_apply, Complex.re_eq_add_conj]; ring
  · simp [Matrix.smul_apply, Matrix.diagonal_apply_ne _ h]

/-- **`Ĥ_Qa = i P D_I P⁻¹ = −i·H_I`** — Nagao–Nielsen Eq. (4.33) (arXiv:1104.3381 §4.4),
`D_I = diagonal(Im λ)`, re-expressed with `H_I = −P D_I P⁻¹` (eigenvalues `−Im λ ≥ 0` when
`Im λ ≤ 0`) to match Sergi–Giaquinta's `H_C = H_R − i H_I`. Reasoning: `(λ − λ̄)/2 = i·Im λ`. -/
theorem qAntiHermPart_eq_HI (hP : IsUnit P.det) :
    qAntiHermPart (qMetric P) (hamiltonian P d) = -Complex.I • hamiltonianHI P d := by
  simp only [qAntiHermPart]
  rw [hamiltonian_qDagger P d hP]
  simp only [hamiltonian, hamiltonianHI]
  rw [← mconj_sub P, ← mconj_smul P, ← mconj_smul P]
  congr 1
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq, smul_eq_mul,
      Pi.star_apply]
    rw [← starRingEnd_apply, Complex.sub_conj]; push_cast; ring
  · simp [Matrix.smul_apply, Matrix.diagonal_apply_ne _ h]

/-- **`Ĥ = H_R − i H_I`** (this work): the complex Hamiltonian form of Sergi & Giaquinta
2016 (Eq. (1), `H_I ≥ 0`) and Nagao–Nielsen 2011, recovered from the periodic Q-Hermitian
`Q`-split `Ĥ = Ĥ_Qh + Ĥ_Qa` (arXiv:2203.07795 §2) via `qHermPart_eq_HR` and
`qAntiHermPart_eq_HI`. This is the bridge between the two papers' formulations. -/
theorem hamiltonian_eq_HR_sub_I_HI (hP : IsUnit P.det) :
    hamiltonian P d = hamiltonianHR P d - Complex.I • hamiltonianHI P d := by
  have hsum := qHermPart_add_qAntiHermPart (qMetric P) (hamiltonian P d)
  rw [qHermPart_eq_HR P d hP, qAntiHermPart_eq_HI P d hP] at hsum
  rw [← hsum, neg_smul, ← sub_eq_add_neg]

/-! ## The damping: `Ĥ − Ĥ^{†Q} = −2i H_I` and the decay rate -/

/-- **`Ĥ − Ĥ^{†Q} = −2i·H_I`**: the difference of `Ĥ` and its `Q`-adjoint is `−2i` times the
imaginary part — the anti-`Q`-Hermitian obstruction to probability conservation. -/
theorem hamiltonian_sub_qDagger_eq (hP : IsUnit P.det) :
    hamiltonian P d - qDagger (qMetric P) (hamiltonian P d)
      = -(2 * Complex.I) • hamiltonianHI P d := by
  have h2 : hamiltonian P d - qDagger (qMetric P) (hamiltonian P d)
      = (2 : ℂ) • qAntiHermPart (qMetric P) (hamiltonian P d) := by
    simp only [qAntiHermPart]; rw [smul_smul, show (2 : ℂ) * 2⁻¹ = 1 by norm_num, one_smul]
  rw [h2, qAntiHermPart_eq_HI P d hP, smul_smul]
  congr 1
  ring

/-- **The probability-decay rate is `−(2/ℏ)·⟨H_I⟩`** — the imaginary-part expectation. This
is exactly the Nagao–Nielsen norm decay `d‖ψ‖²/dt = −(2/ℏ)⟨H_I⟩` of
`FiniteTarget.NagaoNielsenSchrodinger`, recovered from the periodic Q-Hermitian trace rate. -/
theorem trace_dissipative_hamiltonian (hP : IsUnit P.det) (ℏ : ℂ) (ρ : Matrix n n ℂ) :
    (dissipativeGen P ℏ (hamiltonian P d) ρ).trace
      = -(2 / ℏ) * (hamiltonianHI P d * ρ).trace := by
  rw [trace_dissipativeGen, hamiltonian_sub_qDagger_eq P d hP, smul_mul_assoc,
    Matrix.trace_smul, smul_eq_mul,
    show -(Complex.I / ℏ) * (-(2 * Complex.I) * (hamiltonianHI P d * ρ).trace)
       = 2 * (Complex.I * Complex.I) / ℏ * (hamiltonianHI P d * ρ).trace by ring,
    Complex.I_mul_I]
  ring

end Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic

end
