/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.RelationalTime.LiouvillianAgeOperator
public import Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4
public import Mathlib.LinearAlgebra.Matrix.Hermitian
meta import Zil

/-!
# Multiple solutions to the time-energy CCR: the characteristic time operator on a discrete spectrum

The time-energy canonical commutation relation (TE-CCR) analysis of Caballar & Galapon, *Characterizing Multiple
Solutions to the Time-Energy Canonical Commutation Relation via Quantum Dynamics* (arXiv:1005.2870, 2010). A given
Hamiltonian can have several conjugate time operators; they split into two categories by the *sign* of the CCR:

* **PTT** (passage-time-type): `[T, H] ψ = iℏ ψ` (equivalently `[H, T] ψ = −iℏ ψ`),
* **TAT** (time-of-arrival-type): `[H, T] ψ = iℏ ψ`.

This complements `RelationalTime.LiouvillianAgeOperator`, whose (unbounded) Misra time `T = i d/dλ` satisfies
`[L, T] = −iI` — a **PTT** operator on the *continuous* spectrum. Here the paper's **characteristic time
operator** (CTO, §V) is the *discrete-spectrum* PTT solution: a **bounded, self-adjoint** matrix conjugate to the
diagonal Hamiltonian of a particle confined to `[−l, l]`, existing on a discrete, semibounded spectrum precisely
*because* it is bounded — a concrete counterexample to Pauli's theorem (the tension noted for the finite Zeno
dissipator).

Formalized for a finite index set (`Fin n`) with distinct energies `E : Fin n → ℝ`:

* **§A — the CTO in the energy representation (§V).** `ctoOperator E ℏ`, `T_{k,l} = iℏ/(E_k − E_l)` (`k ≠ l`),
  `T_{k,k} = 0`; **`ctoOperator_isHermitian`** (`Tᴴ = T`, self-adjoint).
* **§B — the commutator with the Hamiltonian.** **`cto_commutator_offdiag`** (`[H, T]_{k,l} = iℏ` for `k ≠ l`,
  `0` on the diagonal), `H = diag(E)`.
* **§C — the TE-CCR on the canonical domain.** **`cto_teccr_canonical_domain`** — on the canonical domain
  `Σ_k ψ_k = 0`, `[H, T] ψ = −iℏ ψ`, i.e. `[T, H] ψ = iℏ ψ`: the CTO is a **PTT** time operator (same category as
  the Misra `T`), realizing the TE-CCR exactly on a discrete, bounded-below spectrum.
* **§D — the `Σψ = 0` canonical domain as a subspace.** `canonicalDomain = ker(sumForm)`, the `ℂ`-subspace
  `{ψ : ∑ψ = 0}`; **`mem_canonicalDomain_iff`** (`∈ ↔ ∑ψ = 0`), **`mem_canonicalDomain_iff_affineWeight`**
  (`∈ ↔ IsAffineWeight ψ`, the *same* `∑ = 0` tracelessness as `LeviCivita.SorkinSimplecticNetR4`),
  **`cto_teccr_on_canonicalDomain`** (the CCR over genuine membership), and **`canonicalDomain_finrank`**
  (`dim = n − 1`, codimension one, by rank–nullity).

**Honest layering.** All are exact `Matrix`/`Finset.sum`/`LinearMap` identities in the energies `E` (injective).
The `Σψ = 0` canonical domain is formalized as the genuine subspace `ker(sumForm)` (= the affine-weight/traceless
subspace, codimension one). The Hilbert–Schmidt / compactness and the dynamical PTT-vs-TAT distinction (transition
probabilities of the evolving eigenfunctions) are the paper's results, recorded not formalized.

## References

* Caballar & Galapon, arXiv:1005.2870 (2010), §II, §V. Complements `RelationalTime.LiouvillianAgeOperator`
  (`liouvillian_age_ccr`, the continuous-spectrum PTT).


-/

set_option autoImplicit false

open Matrix Complex
open Physlib.QuantumMechanics.RelationalTime
open Physlib.QuantumMechanics.ComplexAction.LeviCivita.SorkinSimplecticNetR4

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions

variable {n : ℕ}


/-- The **Hamiltonian in the energy representation** `H = diag(E_k)` — a particle confined to `[−l, l]` has a
discrete, semibounded energy spectrum `E : Fin n → ℝ`. -/
noncomputable def energyHamiltonian (E : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun k => (E k : ℂ))

/-- The **characteristic time operator (CTO)** in the energy representation (§V) — `T_{k,l} = iℏ/(E_k − E_l)` for
`k ≠ l` and `T_{k,k} = 0`, the off-diagonal energy-difference kernel of the paper's `T_{2,γ}`. -/
noncomputable def ctoOperator (E : Fin n → ℝ) (ℏ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun k l => if k = l then 0 else Complex.I * (ℏ : ℂ) / ((E k : ℂ) - (E l : ℂ))

/-- **The CTO is self-adjoint** `Tᴴ = T` — the energy-difference kernel is Hermitian (`T_{l,k} = conj T_{k,l}`),
so the characteristic time operator is a genuine self-adjoint observable. -/
lemma ctoOperator_isHermitian (E : Fin n → ℝ) (ℏ : ℝ) :
    (ctoOperator E ℏ)ᴴ = ctoOperator E ℏ := by
  ext k l
  rw [Matrix.conjTranspose_apply]
  unfold ctoOperator
  rcases eq_or_ne k l with h | h
  · subst h; simp
  · rw [if_neg h, if_neg (fun hlk => h hlk.symm)]
    have e1 : star (Complex.I * (ℏ : ℂ)) = -(Complex.I * (ℏ : ℂ)) := by simp
    have e2 : star ((E l : ℂ) - (E k : ℂ)) = (E l : ℂ) - (E k : ℂ) := by simp
    rw [star_div₀, e1, e2, neg_div,
      show (E k : ℂ) - (E l : ℂ) = -((E l : ℂ) - (E k : ℂ)) from by ring, div_neg]


/-- **The commutator `[H, T]` is `iℏ` off the diagonal** `[H, T]_{k,l} = iℏ` for `k ≠ l`, `= 0` on the diagonal —
since `H = diag(E)`, `[H, T]_{k,l} = (E_k − E_l)·T_{k,l}`, and the energy difference cancels the kernel
denominator (`E` injective, so `E_k ≠ E_l`). -/
lemma cto_commutator_offdiag (E : Fin n → ℝ) (ℏ : ℝ) (hE : Function.Injective E)
    (k l : Fin n) :
    (energyHamiltonian E * ctoOperator E ℏ - ctoOperator E ℏ * energyHamiltonian E) k l
      = if k = l then 0 else Complex.I * (ℏ : ℂ) := by
  rw [Matrix.sub_apply, energyHamiltonian, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases h : k = l
  · subst h; simp [ctoOperator]
  · rw [if_neg h]
    simp only [ctoOperator, if_neg h]
    have hEne : (E k : ℂ) - (E l : ℂ) ≠ 0 := by
      simp only [sub_ne_zero, ne_eq, Complex.ofReal_inj]
      exact fun hkl => h (hE hkl)
    field_simp


/-- **The CTO realizes the TE-CCR on the canonical domain** `[H, T] ψ = −iℏ ψ` whenever `Σ_k ψ_k = 0` — the
off-diagonal `iℏ` commutator, summed against a canonical-domain vector, collapses to `−iℏ ψ`: the characteristic
time operator is a **passage-time-type (PTT)** solution `[T, H] ψ = iℏ ψ`, the same category as the Misra
time operator, but on a discrete bounded-below spectrum. -/
lemma cto_teccr_canonical_domain (E : Fin n → ℝ) (ℏ : ℝ) (hE : Function.Injective E)
    (ψ : Fin n → ℂ) (hψ : ∑ k, ψ k = 0) (k : Fin n) :
    ((energyHamiltonian E * ctoOperator E ℏ - ctoOperator E ℏ * energyHamiltonian E).mulVec ψ) k
      = -(Complex.I * (ℏ : ℂ)) * ψ k := by
  rw [Matrix.mulVec, dotProduct]
  have hrw : ∀ l, (energyHamiltonian E * ctoOperator E ℏ
        - ctoOperator E ℏ * energyHamiltonian E) k l * ψ l
      = Complex.I * (ℏ : ℂ) * ψ l - (if l = k then Complex.I * (ℏ : ℂ) * ψ l else 0) := by
    intro l
    rw [cto_commutator_offdiag E ℏ hE k l]
    rcases eq_or_ne k l with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (fun hlk => h hlk.symm)]; ring
  rw [Finset.sum_congr rfl (fun l _ => hrw l), Finset.sum_sub_distrib, ← Finset.mul_sum, hψ,
    mul_zero, zero_sub, Finset.sum_ite_eq' Finset.univ k (fun l => Complex.I * (ℏ : ℂ) * ψ l)]
  simp


/-- The **sum functional** `ψ ↦ ∑_k ψ_k` as a `ℂ`-linear map (the constant-vector pairing). -/
noncomputable def sumForm : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun ψ := ∑ i, ψ i
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum]

@[simp] lemma sumForm_apply (ψ : Fin n → ℂ) : sumForm ψ = ∑ i, ψ i := rfl

/-- The **canonical domain** `𝒟_c = {ψ : ∑_k ψ_k = 0}` of the CTO (the paper's dense-category domain) — the
kernel of the sum functional, the codimension-one subspace orthogonal to the constant vector `(1,…,1)`. -/
noncomputable def canonicalDomain : Submodule ℂ (Fin n → ℂ) := LinearMap.ker sumForm

/-- **Membership in the canonical domain is `∑ψ = 0`**. -/
lemma mem_canonicalDomain_iff (ψ : Fin n → ℂ) : ψ ∈ canonicalDomain ↔ ∑ i, ψ i = 0 := by
  rw [canonicalDomain, LinearMap.mem_ker, sumForm_apply]

/-- **The canonical domain is the affine-weight (traceless) subspace** — `ψ ∈ canonicalDomain ↔ IsAffineWeight ψ`,
the *same* `∑ = 0` condition as the `su(N)` tracelessness / affine-weight system of
`LeviCivita.SorkinSimplecticNetR4`. The CTO's domain is the traceless subspace. -/
lemma mem_canonicalDomain_iff_affineWeight (ψ : Fin n → ℂ) :
    ψ ∈ canonicalDomain ↔ IsAffineWeight ψ :=
  mem_canonicalDomain_iff ψ

/-- **The CTO realizes the TE-CCR on the canonical domain (subspace form)** `[H, T] ψ = −iℏ ψ` for
`ψ ∈ canonicalDomain` — the passage-time-type time-energy CCR as a genuine subspace-domain statement, not a bare
`∑ψ = 0` hypothesis. -/
lemma cto_teccr_on_canonicalDomain (E : Fin n → ℝ) (ℏ : ℝ) (hE : Function.Injective E)
    (ψ : Fin n → ℂ) (hψ : ψ ∈ canonicalDomain) (k : Fin n) :
    ((energyHamiltonian E * ctoOperator E ℏ - ctoOperator E ℏ * energyHamiltonian E).mulVec ψ) k
      = -(Complex.I * (ℏ : ℂ)) * ψ k :=
  cto_teccr_canonical_domain E ℏ hE ψ ((mem_canonicalDomain_iff ψ).mp hψ) k

/-- **The canonical domain has codimension one** `dim 𝒟_c = n − 1` — the sum functional is surjective onto `ℂ`
(rank `1`), so by rank–nullity the traceless subspace is the complement of the single constant direction: the CTO
is a time operator on the `(n−1)`-dimensional canonical domain. -/
lemma canonicalDomain_finrank [NeZero n] :
    Module.finrank ℂ (canonicalDomain : Submodule ℂ (Fin n → ℂ)) = n - 1 := by
  have hsurj : Function.Surjective (sumForm : (Fin n → ℂ) →ₗ[ℂ] ℂ) := fun r =>
    ⟨fun i => if i = (0 : Fin n) then r else 0, by rw [sumForm_apply]; simp⟩
  have hrange : Module.finrank ℂ (LinearMap.range (sumForm : (Fin n → ℂ) →ₗ[ℂ] ℂ)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hdom : Module.finrank ℂ (Fin n → ℂ) = n := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hrn := (sumForm : (Fin n → ℂ) →ₗ[ℂ] ℂ).finrank_range_add_finrank_ker
  rw [hrange, hdom] at hrn
  show Module.finrank ℂ (LinearMap.ker sumForm) = n - 1
  omega

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.ctoOperator_isHermitian where
  formalizes @ "claim:the-characteristic-time-operator-on-a-discrete-energy-spectrum-is-hermitian",
  supported_by @ "paper:caballar-galapon-arxiv-1005-2870-characterizing-multiple-solutions-to-the-time-energy-canonical-commutation-relation"

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.cto_commutator_offdiag where
  supported_by @ "lean:HermitianMat.diagonal_mul",
  formalizes @ "claim:the-commutator-of-the-hamiltonian-with-the-characteristic-time-operator-is-i-hbar-off-the-diagonal-and-zero-on-it-the-energy-difference-cancelling-the-kernel-denominator"

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.cto_teccr_on_canonicalDomain where
  supported_by @ "lean:IsProjectionTensor.complement",
  formalizes @ "claim:the-characteristic-time-operator-realizes-the-passage-time-type-time-energy-canonical-commutation-relation-h-t-psi-equals-minus-i-hbar-psi-on-the-canonical-domain-of-traceless-states",
  requires @ "claim:the-commutator-of-the-hamiltonian-with-the-characteristic-time-operator-is-i-hbar-off-the-diagonal-and-zero-on-it-the-energy-difference-cancelling-the-kernel-denominator"

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.canonicalDomain_finrank where
  formalizes @ "claim:the-canonical-domain-of-the-characteristic-time-operator-has-codimension-one-dimension-n-minus-one-the-traceless-complement-of-the-single-constant-direction"

zil_file_contract physlib.timeEnergyCCRMultipleSolutions where
  promises "The time-energy canonical commutation relation (TE-CCR) analysis of Caballar and Galapon (arXiv:1005.2870): a Hamiltonian can have several conjugate time operators, split by the sign of the CCR into passage-time-type and time-of-arrival-type. On a discrete energy spectrum the characteristic time operator (CTO) is Hermitian (ctoOperator_isHermitian) and its commutator with the diagonal Hamiltonian is i hbar off the diagonal and zero on it (cto_commutator_offdiag), because the energy difference cancels the kernel denominator. On the canonical domain of traceless states (sum of amplitudes zero) the CTO realizes the passage-time-type TE-CCR [H,T]psi = -i hbar psi as a genuine subspace statement (cto_teccr_on_canonicalDomain), and that domain has codimension one, dimension n-1 (canonicalDomain_finrank) -- the resolution of the Pauli objection on a discrete spectrum."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.ctoOperator",
    "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.canonicalDomain"]
  forbids_substitutes ["the continuous-spectrum functional analysis and self-adjointness domains of unbounded time operators, which are outside the finite discrete-spectrum model carried here",
    "any claim that a self-adjoint time operator exists for a semibounded Hamiltonian, only the discrete-spectrum characteristic time operator and its traceless domain are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.ctoOperator_isHermitian,
    Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.cto_commutator_offdiag,
    Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.cto_teccr_on_canonicalDomain,
    Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.canonicalDomain_finrank]

/- ZIL-END -/
