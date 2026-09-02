/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions
meta import Zil

/-!
# The Bender–Dunne time-of-arrival operator domain: two moment conditions

The domain structure of the Bender–Dunne / time-of-arrival operators of Bunao & Galapon, *The Bender–Dunne basis
operators as Hilbert space operators* (arXiv:1509.00340, 2015). The Bender–Dunne operators
`T_{m,n} = 2^{-n} Σ_{k=0}^n C(n,k) qᵏ pᵐ q^{n−k}` (Weyl-ordered quantizations of `qⁿpᵐ`) are the basis in which the
time-of-arrival operator `T` solving the time-energy CCR `[T, H] = iℏ` is expanded. The paper proves `T_{−1,1}`
(the free time-of-arrival operator, `(T_{−1,1}φ)(q) = ∫(q+q')sgn(q−q')φ(q')dq'`) is densely defined; its domain is
the pair of **moment conditions** (Eq. 11)

`∫φ(q)dq = 0`  and  `∫ q φ(q) dq = 0`.

This is the **two-moment** extension of the CTO canonical domain of `TimeEnergyCCRMultipleSolutions`
(`canonicalDomain = {ψ : ∑ψ = 0}`, one moment): `D(T_{−1,1})` is the intersection of the zeroth- and
first-moment kernels, formalized abstractly (a module with two linear functionals `m₀, m₁`).

* **§A — the Weyl-ordering normalization (Eqs. 1–2).** **`benderDunne_weight_normalization`**
  (`Σ_{k=0}^n C(n,k) = 2ⁿ`): the symmetric Weyl weights `2^{-n} C(n,k)` of `T_{m,n}` sum to one.
* **§B — the two-moment domain (Eq. 11).** `benderDunneDomain m₀ m₁ = ker m₀ ⊓ ker m₁`, the codimension-≤2
  subspace `{φ : m₀ φ = 0 ∧ m₁ φ = 0}`; **`mem_benderDunneDomain_iff`**.
* **§C — the antisymmetric basis construction.** **`antisym_mem_ker`** (`I(b)·a − I(a)·b ∈ ker I`): the mechanism
  by which the paper's basis vectors `ψ⁽¹⁾_{m,n} = A_n ψ_{2m} − A_m ψ_{2n}` (`A_k = ∫ψ_{2k}`) automatically satisfy
  the zeroth-moment condition.
* **§D — the determinant solvability (Eq. 13).** **`benderDunne_basis_mem_domain`** — the antisymmetric combination
  `(m₀ φ₂)·φ₁ − (m₀ φ₁)·φ₂` (zeroth moment vanishing by §C) lies in `D(T_{−1,1})` iff
  `m₀ φ₁ · m₁ φ₂ = m₀ φ₂ · m₁ φ₁`, the vanishing-determinant condition for a two-vector solution.

**Honest layering.** All are exact `LinearMap`/`Finset`/`ring` identities in the abstract module of moment
functionals. The `L²(ℝ)` density of `T_{−1,1}` (the square-integrability estimates Eqs. 9–12), the integral-kernel
form (Eqs. 6–8) and the specific Hermite-function coefficients `A⁽¹⁾_n, A⁽²⁾_n` (Eqs. 16–17, tabulated integrals)
are the paper's analytic results, not formalized.

## References

* Bunao & Galapon, arXiv:1509.00340 (2015), Eqs. 1–2, 8, 11, 13. Extends the CTO canonical domain of
  `Particles`/`TimeOperator.TimeEnergyCCRMultipleSolutions`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain


/-- **The Bender–Dunne Weyl weights sum to `2ⁿ`** `Σ_{k=0}^n C(n,k) = 2ⁿ` — the symmetric ordering `T_{m,n} =
2^{-n} Σ_{k=0}^n C(n,k) qᵏ pᵐ q^{n−k}` (Eqs. 1–2) has weights `2^{-n} C(n,k)` that form a (binomial) probability
distribution, the normalization of the Weyl-quantized monomial. -/
lemma benderDunne_weight_normalization (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), n.choose k = 2 ^ n :=
  Nat.sum_range_choose n


variable {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M]

/-- The **Bender–Dunne / time-of-arrival domain** `D(T_{−1,1}) = {φ : m₀ φ = 0 ∧ m₁ φ = 0}` (Eq. 11) — the
intersection of the zeroth-moment (`m₀ = ∫·`) and first-moment (`m₁ = ∫ q·`) kernels, the two-moment extension of
the CTO one-moment `canonicalDomain`. -/
def benderDunneDomain (m₀ m₁ : M →ₗ[𝕜] 𝕜) : Submodule 𝕜 M :=
  LinearMap.ker m₀ ⊓ LinearMap.ker m₁

/-- **Membership in the domain is the pair of moment conditions** `φ ∈ D(T_{−1,1}) ↔ m₀ φ = 0 ∧ m₁ φ = 0`. -/
lemma mem_benderDunneDomain_iff (m₀ m₁ : M →ₗ[𝕜] 𝕜) (φ : M) :
    φ ∈ benderDunneDomain m₀ m₁ ↔ m₀ φ = 0 ∧ m₁ φ = 0 := by
  simp [benderDunneDomain, Submodule.mem_inf, LinearMap.mem_ker]


/-- **The antisymmetric combination lies in the kernel** `I(b)·a − I(a)·b ∈ ker I` — the mechanism by which the
Bender–Dunne basis vectors `ψ⁽¹⁾_{m,n} = A_n ψ_{2m} − A_m ψ_{2n}` (with `A_k = I(ψ_{2k})`, `I` the zeroth moment)
satisfy the moment condition `∫ψ⁽¹⁾ = 0` by construction. -/
lemma antisym_mem_ker (I : M →ₗ[𝕜] 𝕜) (a b : M) :
    (I b) • a - (I a) • b ∈ LinearMap.ker I := by
  rw [LinearMap.mem_ker, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring


/-- **The zeroth moment of the antisymmetric basis vector vanishes** `m₀((m₀ φ₂)·φ₁ − (m₀ φ₁)·φ₂) = 0` — always,
by antisymmetry (a special case of `antisym_mem_ker`). -/
lemma benderDunne_basis_zeroth_moment (m₀ : M →ₗ[𝕜] 𝕜) (φ₁ φ₂ : M) :
    m₀ ((m₀ φ₂) • φ₁ - (m₀ φ₁) • φ₂) = 0 :=
  LinearMap.mem_ker.mp (antisym_mem_ker m₀ φ₁ φ₂)

/-- **The basis vector lies in the domain iff the Bender–Dunne determinant vanishes (Eq. 13)** — the antisymmetric
combination `v = (m₀ φ₂)·φ₁ − (m₀ φ₁)·φ₂` (whose zeroth moment already vanishes) also satisfies the first-moment
condition `m₁ v = 0` — hence `v ∈ D(T_{−1,1})` — exactly when `m₀ φ₁ · m₁ φ₂ = m₀ φ₂ · m₁ φ₁`, the vanishing
determinant of the `2×2` moment matrix that gives a nontrivial two-vector solution. -/
lemma benderDunne_basis_mem_domain (m₀ m₁ : M →ₗ[𝕜] 𝕜) (φ₁ φ₂ : M) :
    ((m₀ φ₂) • φ₁ - (m₀ φ₁) • φ₂) ∈ benderDunneDomain m₀ m₁
      ↔ m₀ φ₁ * m₁ φ₂ = m₀ φ₂ * m₁ φ₁ := by
  rw [mem_benderDunneDomain_iff]
  have hm0 : m₀ ((m₀ φ₂) • φ₁ - (m₀ φ₁) • φ₂) = 0 := benderDunne_basis_zeroth_moment m₀ φ₁ φ₂
  have hm1 : m₁ ((m₀ φ₂) • φ₁ - (m₀ φ₁) • φ₂) = m₀ φ₂ * m₁ φ₁ - m₀ φ₁ * m₁ φ₂ := by
    simp only [map_sub, map_smul, smul_eq_mul]
  constructor
  · rintro ⟨-, h2⟩; rw [hm1] at h2; exact (sub_eq_zero.mp h2).symm
  · intro h; exact ⟨hm0, hm1.trans (sub_eq_zero.mpr h.symm)⟩

end Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.benderDunne_weight_normalization where
  formalizes @ "claim:the-bender-dunne-weyl-ordering-weights-the-binomial-coefficients-sum-to-two-to-the-n-the-normalization-of-the-weyl-quantization-of-q-to-the-n-p-to-the-m",
  supported_by @ "paper:bunao-galapon-arxiv-1509-00340-the-bender-dunne-basis-operators-as-hilbert-space-operators"

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.antisym_mem_ker where
  formalizes @ "claim:the-antisymmetric-combination-i-b-times-a-minus-i-a-times-b-lies-in-the-kernel-of-i-the-mechanism-by-which-the-bender-dunne-basis-vectors-satisfy-the-zeroth-moment-condition-by-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.benderDunne_basis_zeroth_moment where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.antisym_mem_ker",
  formalizes @ "claim:the-zeroth-moment-of-the-antisymmetric-bender-dunne-basis-vector-vanishes-always-by-antisymmetry-so-the-basis-vectors-satisfy-the-first-moment-condition-alone",
  requires @ "claim:the-antisymmetric-combination-i-b-times-a-minus-i-a-times-b-lies-in-the-kernel-of-i-the-mechanism-by-which-the-bender-dunne-basis-vectors-satisfy-the-zeroth-moment-condition-by-construction"

zil attach Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.benderDunne_basis_mem_domain where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.benderDunne_basis_zeroth_moment",
  supported_by @ "lean:IsGloballyComptonCalibrated.symm",
  supported_by @ "lean:IsGloballyComptonCalibrated.trans",
  formalizes @ "claim:the-antisymmetric-bender-dunne-basis-vector-lies-in-the-time-of-arrival-domain-exactly-when-the-two-by-two-moment-determinant-vanishes-giving-a-nontrivial-two-vector-solution",
  requires @ "claim:the-zeroth-moment-of-the-antisymmetric-bender-dunne-basis-vector-vanishes-always-by-antisymmetry-so-the-basis-vectors-satisfy-the-first-moment-condition-alone"

zil_file_contract physlib.benderDunneTimeOperatorDomain where
  promises "The domain structure of the Bender-Dunne / time-of-arrival operators (Bunao and Galapon, arXiv:1509.00340). The Bender-Dunne operators are the Weyl-ordered quantizations of q^n p^m in which the time-of-arrival operator solving the time-energy CCR is expanded, and their weights (binomial coefficients) sum to 2^n (benderDunne_weight_normalization). The time-of-arrival domain is the pair of moment conditions -- the zeroth and first moments both vanish -- the two-moment extension of the CTO's one-moment canonical domain. The antisymmetric combination automatically lies in the zeroth-moment kernel (antisym_mem_ker), so the zeroth moment of the antisymmetric basis vector always vanishes (benderDunne_basis_zeroth_moment), and the antisymmetric basis vector lies in the full domain exactly when the 2x2 moment determinant vanishes (benderDunne_basis_mem_domain)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.benderDunneDomain",
    "lean:Physlib.QuantumMechanics.ComplexAction.TimeOperator.TimeEnergyCCRMultipleSolutions.canonicalDomain"]
  forbids_substitutes ["the integral-operator analysis of the free time-of-arrival kernel and its dense-domain self-adjointness, which are the cited functional-analytic inputs abstracted here to linear moment functionals",
    "any spectral resolution of the time-of-arrival operator, only the moment-condition domain structure is carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.benderDunne_weight_normalization,
    Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.antisym_mem_ker,
    Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.benderDunne_basis_zeroth_moment,
    Physlib.QuantumMechanics.ComplexAction.TimeOperator.BenderDunneTimeOperatorDomain.benderDunne_basis_mem_domain]

/- ZIL-END -/
