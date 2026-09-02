/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracOperator

meta import Zil

/-!
# The signature of the twist: no real-structure conjugation, and the real-phase kernel

The two exact observations of Aastrup–Grimstrup arXiv:2501.00005 §6 (*Discussion*),
closing the paper's formalization arc.

## §A — the twist is not a conjugation (the paper's open question, sharpened)

The paper asks what the twist `c(ψ) ↦ c(iψ)` signifies mathematically, noting it *"is
not a conjugation with a real structure, as is the case in the work by Chamseddine
and Connes"*. That distinction is a theorem:

* `cliffordMul_twist_sq` — the twist **squares to `−1`** on the Clifford generators:
  `c(i(iψ)) = −c(ψ)` (derived from the antilinearity of `int` alone).
* `conjugation_involutive` — conjugation by any element with `u² = ±1` (the square of
  a real structure `J² = ε`) is **involutive**: applying it twice is the identity.
* `twist_not_conjugation` — hence **no element with `u² = ±1` implements the twist by
  conjugation**: if `u·c(ψ)·u' = c(iψ)` for all `ψ`, then twice-conjugating forces
  `c(ψ) = −c(ψ)`, so `c(ψ) = 0` — contradiction on any nonzero generator. The twist
  is an operation of genuinely different signature (order `4`, not `2`) from a
  real-structure conjugation; the two operations "involving the complex nature of the
  spinors" that the paper distinguishes are formally inequivalent.

## §B — the kernel phases: complex for the untwisted, real for the twisted

The paper observes that the ground state of [7] is a **complex phase** involving the
Chern–Simons term (Kodama-like), while *"the kernel of the fluctuated Dirac operator
(6) will be a real phase involving the Chern–Simons term"*. Both halves, exactly:

* `untwisted_kernel_unitary_transport` — the untwisted inner fluctuation is plain
  conjugation, `D + u[D,u⁻¹] = uDu⁻¹`, so its kernel is the **unitary transport**
  `u·ker D`: with `u = e^{iCS}` the kernel states are the complex-phase (Kodama-like)
  dressings.
* `twisted_kernel_real_phase` — the twisted operator
  `D̃₁ = Σᵢ(c̄(ψᵢ)∇ᵢ − c(ψᵢ)sᵢ)` (the `i[D₂,CS]` fluctuation term rewritten through
  the twist: `i·c̄(iψ) = −c(ψ)`, `sᵢ` the Chern–Simons gradient `∂ᵢCS`) **annihilates
  the real-phase dressed vacuum** `g·Ω` where `[∇ᵢ, g] = g·sᵢ` (the defining property
  of `g = e^{CS}`) and `Ω` is the Fock vacuum (`int(ψᵢ)Ω = 0`, `∇ᵢΩ = 0`): the
  gradient term produced by `∇ᵢ` hitting `e^{CS}` combines with the fluctuation term
  into `c̄ − c = −2·int`, which kills the vacuum. The dressing is `e^{+CS}` — a real
  phase, exactly the paper's counterbalancing observation for the Hilbert-space
  representation question.

## Honest scope

Ring-level: `g` is an abstract element with the `e^{CS}` commutation property (no
exponential is constructed), the vacuum is an element annihilated by the `int`s and
`∇`s (no Fock-space measure), and the commutation hypotheses (functions commute among
themselves and with the Clifford elements) are the flat/trivial-geometry setting of
paper §4. The antilinear (rather than unitary-linear) implementation of a real
structure is discussed but its conjugation on the *algebra* is linear, which is the
case covered. The representation-theoretic question the paper leaves open (whether
the metric on the configuration space can counterbalance the real phase to give a
normalizable state) remains open here too.

## References

* J. Aastrup, J. M. Grimstrup, arXiv:2501.00005 §6; [7] arXiv:2309.06374 (the
  Kodama-like ground state); H. Kodama, Prog. Theor. Phys. **80** (1988) 1024;
  L. Smolin, arXiv:hep-th/0209079.
* Carriers: `AlgebraicQFT.ConfigurationSpaceDiracFluctuation` (Clifford pair, twist),
  `AlgebraicQFT.ConfigurationSpaceDiracOperator` (Dirac blocks).
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.CARAlgebraAutomorphism
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {A : Type*} [Ring A] [StarRing A] [Module ℂ A]

/-! ## §A — the twist is not a conjugation -/

/-- **The twist squares to `−1`**: `c(i(iψ)) = −c(ψ)` — applying the twist twice
negates the Clifford generator, so the twist has order `4`, not `2`. Derived from the
antilinearity of `int` alone. -/
theorem cliffordMul_twist_sq [StarModule ℂ A] {B : K → A}
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ)) (ψ : K) :
    cliffordMul B (Complex.I • (Complex.I • ψ)) = -(cliffordMul B ψ) := by
  rw [cliffordMul_twist hanti, cliffordMulBar_twist hanti, smul_smul, Complex.I_mul_I,
    neg_one_smul]

/-- **Conjugation by a square-`±1` element is involutive**: for `u·u' = 1`, `u'·u = 1`
and `u² = ±1` (the square of a real structure), conjugating twice is the identity. -/
theorem conjugation_involutive {R : Type*} [Ring R] {u u' : R}
    (hu' : u' * u = 1) (h2 : u * u = 1 ∨ u * u = -1) (x : R) :
    u * (u * x * u') * u' = x := by
  rcases h2 with h | h
  · have hue : u' = u := by
      calc u' = u' * (u * u) := by rw [h, mul_one]
        _ = (u' * u) * u := by noncomm_ring
        _ = u := by rw [hu', one_mul]
    rw [hue]
    calc u * (u * x * u) * u = (u * u) * x * (u * u) := by noncomm_ring
      _ = x := by rw [h]; noncomm_ring
  · have hue : u' = -u := by
      have h1 : u' * (u * u) = -u' := by rw [h, mul_neg, mul_one]
      have h3 : (u' * u) * u = -u' := by rw [← h1]; noncomm_ring
      rw [hu', one_mul] at h3
      rw [h3, neg_neg]
    rw [hue]
    calc u * (u * x * -u) * -u = (u * u) * x * (u * u) := by noncomm_ring
      _ = x := by rw [h]; noncomm_ring

/-- **The twist cannot be implemented by conjugation with any square-`±1` element**
(the paper's §6 distinction, sharpened to a theorem): if `u·c(ψ)·u' = c(iψ)` for all
`ψ` with `u² = ±1`, then double conjugation gives `c(ψ) = c(−ψ) = −c(ψ)`, forcing
`c(ψ) = 0` — impossible on a nonzero generator. The twist and a real-structure
conjugation are operations of different signature. -/
theorem twist_not_conjugation [StarModule ℂ A] {B : K → A}
    (hanti : ∀ ψ, B (Complex.I • ψ) = -(Complex.I • B ψ)) {u u' : A}
    (hu' : u' * u = 1) (h2 : u * u = 1 ∨ u * u = -1)
    (himpl : ∀ ψ, u * cliffordMul B ψ * u' = cliffordMul B (Complex.I • ψ))
    {ψ : K} (hne : cliffordMul B ψ ≠ 0) : False := by
  have hdouble : cliffordMul B ψ = -(cliffordMul B ψ) := by
    calc cliffordMul B ψ
        = u * (u * cliffordMul B ψ * u') * u' :=
          (conjugation_involutive hu' h2 _).symm
      _ = u * cliffordMul B (Complex.I • ψ) * u' := by rw [himpl]
      _ = cliffordMul B (Complex.I • (Complex.I • ψ)) := himpl _
      _ = -(cliffordMul B ψ) := cliffordMul_twist_sq hanti ψ
  apply hne
  have h2c : (2 : ℂ) • cliffordMul B ψ = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hdouble]
    exact add_neg_cancel _
  have hhalf := congrArg (fun x => (2 : ℂ)⁻¹ • x) h2c
  simpa [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)] using hhalf

/-! ## §B — the kernel phases -/

/-- **The untwisted fluctuation's kernel is the unitary transport of the free
kernel**: `D + u[D,u⁻¹] = uDu⁻¹` annihilates `u·x` whenever `D` annihilates `x` —
with `u = e^{iCS}`, the kernel states are the **complex-phase** (Kodama-like)
dressings of the free ones (paper §6, referring to [7]). -/
theorem untwisted_kernel_unitary_transport {R : Type*} [Ring R] {u u' D x : R}
    (hu' : u' * u = 1) (hx : D * x = 0) :
    (u * D * u') * (u * x) = 0 := by
  calc (u * D * u') * (u * x) = u * D * (u' * u) * x := by noncomm_ring
    _ = u * (D * x) := by rw [hu']; noncomm_ring
    _ = 0 := by rw [hx, mul_zero]

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Module ℂ A] in
/-- `c̄(ψ) − c(ψ) = −2·int(ψ)` — the odd-minus-even Clifford combination is the pure
annihilator, the mechanism that kills the dressed vacuum. -/
theorem cliffordMulBar_sub_cliffordMul (B : K → A) (ψ : K) :
    cliffordMulBar B ψ - cliffordMul B ψ = -(B ψ + B ψ) := by
  unfold cliffordMul cliffordMulBar
  abel

omit [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Module ℂ A] in
/-- **The twisted Dirac operator annihilates the real-phase dressed vacuum** (paper
§6): for `D̃₁ = Σᵢ(c̄(ψᵢ)∇ᵢ − c(ψᵢ)sᵢ)` — the twisted-fluctuated block, with `sᵢ`
the Chern–Simons gradient — and `g` with the `e^{CS}` property `[∇ᵢ, g] = g·sᵢ`,

`D̃₁ (g·Ω) = 0`

for any vacuum `Ω` with `int(ψᵢ)Ω = 0` and `∇ᵢΩ = 0`: the gradient produced by `∇ᵢ`
hitting the dressing combines with the fluctuation term into `c̄ − c = −2·int`, which
annihilates the vacuum. The kernel dressing is the **real phase** `e^{+CS}`, in
contrast to the untwisted complex-phase transport — the paper's Hilbert-space
counterbalancing observation. -/
theorem twisted_kernel_real_phase {n : ℕ} (B : K → A) (ψ : Fin n → K)
    (dv s : Fin n → A) (g Ω : A)
    (hgrad : ∀ i, dv i * g = g * s i + g * dv i)
    (hvacd : ∀ i, dv i * Ω = 0)
    (hvacB : ∀ i, B (ψ i) * Ω = 0)
    (hcbg : ∀ i, cliffordMulBar B (ψ i) * g = g * cliffordMulBar B (ψ i))
    (hcbs : ∀ i j, cliffordMulBar B (ψ i) * s j = s j * cliffordMulBar B (ψ i))
    (hcg : ∀ i, cliffordMul B (ψ i) * g = g * cliffordMul B (ψ i))
    (hcs : ∀ i j, cliffordMul B (ψ i) * s j = s j * cliffordMul B (ψ i))
    (hsg : ∀ i, s i * g = g * s i) :
    (∑ i, (cliffordMulBar B (ψ i) * dv i - cliffordMul B (ψ i) * s i)) * (g * Ω)
      = 0 := by
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  have e1 : cliffordMulBar B (ψ i) * dv i * (g * Ω)
      = g * (s i * (cliffordMulBar B (ψ i) * Ω)) := by
    calc cliffordMulBar B (ψ i) * dv i * (g * Ω)
        = cliffordMulBar B (ψ i) * ((dv i * g) * Ω) := by noncomm_ring
      _ = cliffordMulBar B (ψ i) * ((g * s i + g * dv i) * Ω) := by rw [hgrad i]
      _ = cliffordMulBar B (ψ i) * (g * (s i * Ω)) + cliffordMulBar B (ψ i)
            * (g * (dv i * Ω)) := by noncomm_ring
      _ = cliffordMulBar B (ψ i) * (g * (s i * Ω)) := by
          rw [hvacd i, mul_zero, mul_zero, add_zero]
      _ = (cliffordMulBar B (ψ i) * g) * (s i * Ω) := by noncomm_ring
      _ = (g * cliffordMulBar B (ψ i)) * (s i * Ω) := by rw [hcbg i]
      _ = g * ((cliffordMulBar B (ψ i) * s i) * Ω) := by noncomm_ring
      _ = g * ((s i * cliffordMulBar B (ψ i)) * Ω) := by rw [hcbs i i]
      _ = g * (s i * (cliffordMulBar B (ψ i) * Ω)) := by noncomm_ring
  have e2 : cliffordMul B (ψ i) * s i * (g * Ω)
      = g * (s i * (cliffordMul B (ψ i) * Ω)) := by
    calc cliffordMul B (ψ i) * s i * (g * Ω)
        = cliffordMul B (ψ i) * ((s i * g) * Ω) := by noncomm_ring
      _ = cliffordMul B (ψ i) * ((g * s i) * Ω) := by rw [hsg i]
      _ = (cliffordMul B (ψ i) * g) * (s i * Ω) := by noncomm_ring
      _ = (g * cliffordMul B (ψ i)) * (s i * Ω) := by rw [hcg i]
      _ = g * ((cliffordMul B (ψ i) * s i) * Ω) := by noncomm_ring
      _ = g * ((s i * cliffordMul B (ψ i)) * Ω) := by rw [hcs i i]
      _ = g * (s i * (cliffordMul B (ψ i) * Ω)) := by noncomm_ring
  have hkill : (cliffordMulBar B (ψ i) - cliffordMul B (ψ i)) * Ω = 0 := by
    rw [cliffordMulBar_sub_cliffordMul, neg_mul, add_mul, hvacB i, add_zero, neg_zero]
  calc (cliffordMulBar B (ψ i) * dv i - cliffordMul B (ψ i) * s i) * (g * Ω)
      = cliffordMulBar B (ψ i) * dv i * (g * Ω)
          - cliffordMul B (ψ i) * s i * (g * Ω) := by noncomm_ring
    _ = g * (s i * ((cliffordMulBar B (ψ i) - cliffordMul B (ψ i)) * Ω)) := by
        rw [e1, e2]; noncomm_ring
    _ = 0 := by rw [hkill, mul_zero, mul_zero]

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature.twist_not_conjugation where
  formalizes @ "claim:no-square-plus-or-minus-one-element-no-real-structure-with-j-squared-equals-plus-or-minus-one-implements-the-spinor-twist-c-of-psi-mapsto-c-of-i-psi-by-conjugation-the-twist-has-order-four-not-two-so-it-is-genuinely-distinct-from-a-chamseddine-connes-real-structure-conjugation",
  supported_by @ "paper:aastrup-grimstrup-arxiv-2410-07290-dirac-operators-on-configuration-spaces"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature.cliffordMul_twist_sq where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation.cliffordMulBar_twist",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation.cliffordMul_twist",
  formalizes @ "claim:applying-the-spinor-twist-twice-negates-the-clifford-generator-c-of-i-times-i-psi-equals-minus-c-of-psi-establishing-that-the-twist-squares-to-minus-one"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature.twisted_kernel_real_phase where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature.cliffordMulBar_sub_cliffordMul",
  supported_by @ "lean:KroneckerDelta.sum_mul",
  formalizes @ "claim:the-twisted-fluctuated-dirac-operator-annihilates-the-real-phase-exponential-chern-simons-dressed-fock-vacuum-giving-the-twisted-operator-a-real-rather-than-complex-kodama-like-chern-simons-kernel-phase"

zil attach Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature.untwisted_kernel_unitary_transport where
  formalizes @ "claim:the-untwisted-inner-fluctuation-is-plain-conjugation-u-d-u-inverse-so-its-kernel-is-the-unitary-transport-of-the-kernel-of-d-the-complex-phase-kodama-like-dressing-the-foil-to-the-twisted-real-phase-case"

zil_file_contract physlib.configurationSpaceTwistSignature where
  promises "The twist signature and its distinction from a real-structure conjugation (Aastrup-Grimstrup arXiv:2410.07290). Applying the spinor twist twice negates the Clifford generator, so the twist squares to -1 (cliffordMul_twist_sq); consequently no square-(plus or minus one) element implements the twist c(psi) -> c(i psi) by conjugation -- the twist has order 4, not 2, so it is genuinely distinct from a Chamseddine-Connes real-structure conjugation (twist_not_conjugation). The twisted fluctuated Dirac operator annihilates the real-phase e^{+CS}-dressed Fock vacuum (twisted_kernel_real_phase), whereas the untwisted inner fluctuation is plain conjugation whose kernel is the unitary transport, the complex Kodama-like dressing (untwisted_kernel_unitary_transport)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation.cliffordMul",
    "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceDiracFluctuation.cliffordMulBar"]
  forbids_substitutes ["the classification of real structures by the KO-dimension and the physical identification of the Kodama state, which are the cited noncommutative-geometry and quantum-gravity infrastructure",
    "any claim that the twisted spectral triple is fully axiomatized; only the order-4 no-go, the twist-squares-to-minus-one, and the kernel-phase identities are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature.twist_not_conjugation,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature.cliffordMul_twist_sq,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature.twisted_kernel_real_phase,
    Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.ConfigurationSpaceTwistSignature.untwisted_kernel_unitary_transport]

/- ZIL-END -/
