/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.BargmannFockCCR
public import Mathlib.Tactic.FieldSimp

/-!
# The Weyl-shift relation realized on the Bargmann–Fock polynomials

The faithful realization of the `WeylAnnihilatorSystem` axioms
(`QFT.HamiltonianRenormalisation.WeylAnnihilatorSystem`, Eqs. 3.113/3.115 of Lang–Liegener–
Thiemann, *Hamiltonian renormalisation II*, arXiv:1711.06727v2), built entirely from
infrastructure already in the library: on the Bargmann–Fock polynomial core of
`OperatorAlgebra.BargmannFockCCR` — annihilators `ann a = ∑ᵢ aᵢ∂ᵢ` as derivations, creation
fields `crePoly b = ⟨z, b⟩`, and Stochel's CCR `[A_a⁻, A_b⁺] = ⟨a,b⟩·I`
(`generalised_ccr_bargmann`) — the axioms of the abstract system are *theorems*:

* the vacuum is the constant polynomial `1`, annihilated by every `ann a`
  (`Derivation.map_one_eq_zero` — nothing to add);
* the Weyl element on the vacuum is the coherent state `e^{⟨z,b⟩}`, whose polynomial
  truncations are `coherentPoly N b = ∑_{k≤N} (k!)⁻¹ (crePoly b)^k`;
* `ann_coherentPoly` — **coherent vectors are annihilator eigenvectors**:
  `A_a⁻ (coherentPoly (N+1) b) = ⟨a,b⟩ · coherentPoly N b`, exactly, at every truncation
  order (the eigenvalue equation of Eq. 3.115 applied to the vacuum, with the truncation
  index dropping by one — the trace of the cut series, gone in the completed Bargmann space);
* `coherentPoly_shift` — **the Weyl-shift relation as a theorem**:
  `A_a⁻ (W_N · f) = W_N · A_a⁻ f + ⟨a,b⟩ · (W_{N−1} · f)` — Eq. 3.115,
  `a(g) W(f) = W(f) a(g) + c·W(f)`, derived from the Leibniz rule and the iterated CCR
  (`ann_crePoly_pow`), rather than postulated.

The dictionary to the abstract system: the direction `b` encodes the paper's smearing
`ω^{−1/2}f` and the inner product `⟨a, b⟩` its shift constant `i·s·⟨g, ω^{−1/2}f⟩`; scaling
and phase are absorbed into the complex direction.

**Honest layering.**  Exact derivation algebra on `MvPolynomial`; every statement holds at
every truncation order with the index bookkeeping made explicit.  The completion — the
Bargmann space of holomorphic functions where `coherentPoly N b → e^{⟨z,b⟩}` in the Fock norm,
the Weyl elements become bounded-below operators and the truncation index disappears — is the
remaining analytic layer (the Fock–Sobolev forms of `OperatorAlgebra.HankelFockSobolev`, whose
`mittagLeffler 1 1 = exp` is this exponential, are the natural home).

## References

* J. B. Stochel, *Representation of generalised creation and annihilation operators in Fock
  space* (1997); T. Lang, K. Liegener, T. Thiemann, arXiv:1711.06727v2, Eqs. 3.113–3.115.
  Builds on `OperatorAlgebra.BargmannFockCCR`; realizes the axioms of
  `QFT.HamiltonianRenormalisation.WeylAnnihilatorSystem`.
-/

set_option autoImplicit false

open Finset

@[expose] public section

namespace Physlib.QFT.HamiltonianRenormalisation

open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.BargmannFockCCR

variable {n : ℕ}

/-- **The iterated CCR** (the `k`-th Baker–Campbell–Hausdorff layer): the annihilator applied
to the `(k+1)`-st power of the creation field, `A_a⁻ ⟨z,b⟩^{k+1} = (k+1)·⟨a,b⟩·⟨z,b⟩^k`. -/
lemma ann_crePoly_pow (a b : Fin n → ℂ) (k : ℕ) :
    ann a (crePoly b ^ (k+1))
      = (((k+1 : ℕ) : ℂ) * bargmannInner a b) • crePoly b ^ k := by
  induction k with
  | zero =>
    simpa using ann_crePoly a b
  | succ j ih =>
    calc ann a (crePoly b ^ (j+2))
        = ann a (crePoly b * crePoly b ^ (j+1)) := by rw [← pow_succ']
      _ = crePoly b * ann a (crePoly b ^ (j+1))
          + crePoly b ^ (j+1) * ann a (crePoly b) := by
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      _ = crePoly b * ((((j+1 : ℕ) : ℂ) * bargmannInner a b) • crePoly b ^ j)
          + crePoly b ^ (j+1) * (bargmannInner a b • (1 : BargmannPoly n)) := by
          rw [ih, ann_crePoly]
      _ = (((j+1 : ℕ) : ℂ) * bargmannInner a b) • crePoly b ^ (j+1)
          + bargmannInner a b • crePoly b ^ (j+1) := by
          rw [mul_smul_comm, mul_smul_comm, mul_one, ← pow_succ']
      _ = (((j+2 : ℕ) : ℂ) * bargmannInner a b) • crePoly b ^ (j+1) := by
          rw [← add_smul]
          push_cast
          ring_nf

/-- **The truncated coherent state** `∑_{k ≤ N} (k!)⁻¹ ⟨z,b⟩^k` — the polynomial truncation of
the Bargmann coherent vector `e^{⟨z,b⟩} = W(b)Ω`. -/
noncomputable def coherentPoly (N : ℕ) (b : Fin n → ℂ) : BargmannPoly n :=
  ∑ k ∈ range (N+1), ((k.factorial : ℂ))⁻¹ • crePoly b ^ k

@[simp] lemma coherentPoly_zero (b : Fin n → ℂ) : coherentPoly 0 b = 1 := by
  simp [coherentPoly]

/-- **Coherent vectors are annihilator eigenvectors** (Eq. 3.115 applied to the vacuum): the
annihilator maps the order-`(N+1)` truncated coherent state to `⟨a,b⟩` times the order-`N`
truncation — exactly, the factorials telescoping against the iterated CCR. -/
theorem ann_coherentPoly (a b : Fin n → ℂ) (N : ℕ) :
    ann a (coherentPoly (N+1) b) = bargmannInner a b • coherentPoly N b := by
  unfold coherentPoly
  have hsum : ann a (∑ k ∈ range (N+1+1), ((k.factorial : ℂ))⁻¹ • crePoly b ^ k)
      = ∑ k ∈ range (N+1+1), ann a (((k.factorial : ℂ))⁻¹ • crePoly b ^ k) :=
    map_sum (ann a).toLinearMap _ _
  rw [hsum, Finset.sum_range_succ', smul_sum]
  have h0 : ann a (((Nat.factorial 0 : ℂ))⁻¹ • crePoly b ^ 0) = 0 := by
    simp
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.map_smul, ann_crePoly_pow, smul_smul]
  have hfac : (((j+1).factorial : ℂ))⁻¹ * (((j+1 : ℕ) : ℂ) * bargmannInner a b)
      = bargmannInner a b * ((j.factorial : ℂ))⁻¹ := by
    have hj1 : ((j+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
    have hjf : ((j.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  rw [hfac, ← smul_smul]

/-- **The Weyl-shift relation, as a theorem** (Eq. 3.115): on the Bargmann polynomials the
annihilator conjugated through the truncated Weyl element picks up the c-number shift,
`A_a⁻ (W_N f) = W_N (A_a⁻ f) + ⟨a,b⟩·(W_{N−1} f)` — derived from the Leibniz rule and the
coherent eigenvector identity, rather than postulated as in the abstract
`WeylAnnihilatorSystem`. -/
theorem coherentPoly_shift (a b : Fin n → ℂ) (N : ℕ) (f : BargmannPoly n) :
    ann a (coherentPoly (N+1) b * f)
      = coherentPoly (N+1) b * ann a f
        + bargmannInner a b • (coherentPoly N b * f) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, ann_coherentPoly, mul_smul_comm,
    mul_comm f (coherentPoly N b)]

end Physlib.QFT.HamiltonianRenormalisation

end
