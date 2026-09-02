/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic
meta import Zil

/-!
# The Coulomb-gauge Yang–Mills variational vacuum: transverse projector, gluon propagator, ghost Dyson

Formalizes the geometric core of the **variational solution of the Yang–Mills Schrödinger equation in
Coulomb gauge** (Feuchter–Reinhardt, arXiv:hep-th/0408236, Phys. Rev. D 70, 105021). In the Weyl gauge
`A₀ = 0` the Yang–Mills Hamiltonian `H = ½∫(Πₖ² + Bₖ²)` (their Eq. 3) is quantized canonically; the
physical degrees of freedom are the **transverse** gauge fields `Aᵢ^⊥ = tᵢⱼ Aⱼ` (Coulomb gauge
`∂ᵢAᵢ = 0`), and the vacuum is obtained from the variational principle `⟨Ψ|H|Ψ⟩/⟨Ψ|Ψ⟩ → min` (their Eq. 24
— the Rayleigh–Ritz principle of the variational calculus, Lovelock–Rund) over a Gaussian ansatz
`Ψ[A] = N exp(−½∫∫ A ω A)` (their Eq. 34).

Three exact structures underlie that construction, formalized here in momentum space (a fixed spatial
momentum `k ∈ ℝ^d`, physical `d = 3`):

* **§A — the transverse (Coulomb-gauge) projector** `tᵢⱼ(k) = δᵢⱼ − kᵢkⱼ/k²` (their Eq. 11): a symmetric
  idempotent projector that annihilates the longitudinal direction `k` and has trace `d − 1` — the
  `d − 1 = 2` physical gluon polarizations.
* **§B — the variational gluon propagator** `Dᵢⱼ(k) = tᵢⱼ(k)/(2ω)` (their Eq. 37/45): the Gaussian
  two-point function, transverse and equal to the inverse of the kernel `2ω t` on the physical subspace,
  provided the gluon energy `ω` is strictly positive (their normalizability condition below Eq. 45).
* **§C — the ghost Dyson–Schwinger equation** `G = G₀ + G₀ Σ G ⟹ G⁻¹ = G₀⁻¹ − Σ` (their Eq. 49): the
  ghost propagator's inverse is the free inverse minus the ghost self-energy.

**Honest layering.** The projector algebra, the propagator identity and the Dyson resummation are exact.
The variational determination of the gluon energy `ω(k)` (the coupled gap/Schwinger–Dyson equations, the
infrared-divergent ghost and the confining Coulomb potential of the paper) is *not* solved here; it is the
non-perturbative input the paper computes numerically. `ω > 0` is assumed, not derived.

## References

* C. Feuchter, H. Reinhardt, *Variational solution of the Yang–Mills Schrödinger equation in Coulomb
  gauge*, arXiv:hep-th/0408236 (Eqs. 3, 11, 24, 34, 37, 45, 49).
* D. Lovelock, H. Rund, *Tensors, differential forms, and variational principles* (the Rayleigh–Ritz /
  stationary-action principle behind `⟨H⟩ → min`).
-/

set_option autoImplicit false

open scoped Matrix

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum

variable {d : ℕ}

/-! ### §A — the transverse (Coulomb-gauge) projector -/

/-- **The transverse projector** `tᵢⱼ(k) = δᵢⱼ − kᵢkⱼ/k²` (Feuchter–Reinhardt Eq. 11) — projects a spatial
vector onto the subspace orthogonal to the momentum `k`, i.e. onto the physical transverse gauge-field
polarizations of Coulomb gauge. -/
noncomputable def transverseProjector (k : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  1 - (k ⬝ᵥ k)⁻¹ • Matrix.vecMulVec k k

/-- **[The transverse projector is symmetric] `tᵀ = t`.** -/
lemma transverseProjector_isSymm (k : Fin d → ℝ) :
    (transverseProjector k)ᵀ = transverseProjector k := by
  unfold transverseProjector
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul]
  congr 1
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.transpose_apply, mul_comm]

/-- **[The projector annihilates the longitudinal direction] `t(k) · k = 0`.** The Coulomb-gauge projector
removes the longitudinal (unphysical, gauge) part along `k` — the transverse gauge field satisfies
`∂ᵢAᵢ = 0`. -/
lemma transverseProjector_mulVec_self (k : Fin d → ℝ) (hk : k ⬝ᵥ k ≠ 0) :
    transverseProjector k *ᵥ k = 0 := by
  have hmv : Matrix.vecMulVec k k *ᵥ k = (k ⬝ᵥ k) • k := by
    rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  unfold transverseProjector
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hmv, smul_smul,
    inv_mul_cancel₀ hk, one_smul, sub_self]

/-- **[The transverse projector is idempotent] `t · t = t`.** With the longitudinal part removed once, a
second projection does nothing — `t` is a genuine projector onto the transverse polarizations. -/
lemma transverseProjector_mul_self (k : Fin d → ℝ) (hk : k ⬝ᵥ k ≠ 0) :
    transverseProjector k * transverseProjector k = transverseProjector k := by
  have hVV : Matrix.vecMulVec k k * Matrix.vecMulVec k k = (k ⬝ᵥ k) • Matrix.vecMulVec k k := by
    rw [Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hcVcV : ((k ⬝ᵥ k)⁻¹ • Matrix.vecMulVec k k) * ((k ⬝ᵥ k)⁻¹ • Matrix.vecMulVec k k)
      = (k ⬝ᵥ k)⁻¹ • Matrix.vecMulVec k k := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hVV, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ hk, mul_one]
  unfold transverseProjector
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, hcVcV]
  abel

/-- **[The projector counts the transverse polarizations] `tr t(k) = d − 1`.** The trace of the Coulomb-gauge
projector is the number of transverse (physical) gluon polarizations — `d − 1 = 2` in `d = 3` space. -/
lemma transverseProjector_trace (k : Fin d → ℝ) (hk : k ⬝ᵥ k ≠ 0) :
    (transverseProjector k).trace = (d : ℝ) - 1 := by
  unfold transverseProjector
  rw [Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin, Matrix.trace_smul,
    Matrix.trace_vecMulVec, smul_eq_mul, inv_mul_cancel₀ hk]

/-! ### §B — the variational gluon propagator -/

/-- **The variational gluon propagator** `Dᵢⱼ(k) = tᵢⱼ(k)/(2ω)` (Feuchter–Reinhardt Eq. 37/45) — the
Gaussian-vacuum two-point function `⟨AᵢAⱼ⟩ = tᵢⱼ/(2ω)`, with `ω = ω(k)` the gluon energy. -/
noncomputable def gluonPropagator (k : Fin d → ℝ) (ω : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (2 * ω)⁻¹ • transverseProjector k

/-- **[The gluon propagator is transverse] `D(k) · k = 0`.** The propagator has no longitudinal part: only
the physical transverse gluon propagates. -/
lemma gluonPropagator_mulVec_self (k : Fin d → ℝ) (ω : ℝ) (hk : k ⬝ᵥ k ≠ 0) :
    gluonPropagator k ω *ᵥ k = 0 := by
  unfold gluonPropagator
  rw [Matrix.smul_mulVec, transverseProjector_mulVec_self k hk, smul_zero]

/-- **[The propagator inverts the kernel on the physical subspace] `(2ω t) · D = t`.** The Gaussian kernel
`2ω t` times the propagator `D = t/(2ω)` returns the transverse identity `t`: `D` is the inverse of the
variational kernel restricted to the physical (transverse) subspace, provided the gluon energy `ω ≠ 0` — the
normalizability of the trial vacuum requires `ω(k)` strictly positive. -/
lemma gluonPropagator_kernel_mul (k : Fin d → ℝ) (ω : ℝ) (hω : ω ≠ 0) (hk : k ⬝ᵥ k ≠ 0) :
    (2 * ω) • transverseProjector k * gluonPropagator k ω = transverseProjector k := by
  unfold gluonPropagator
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ (mul_ne_zero (two_ne_zero) hω), one_smul, transverseProjector_mul_self k hk]

/-! ### §C — the ghost Dyson–Schwinger equation -/

/-- **[The ghost Dyson–Schwinger equation] `G = G₀ + G₀ Σ G ⟹ G₀⁻¹ − Σ` is the inverse ghost propagator.**
From the Dyson equation (Feuchter–Reinhardt Eq. 49) for the ghost propagator `G`, with `G₀` the free ghost
propagator and `Σ` the ghost self-energy, the operator `G₀⁻¹ − Σ` is a left inverse of `G`: the inverse
ghost propagator is the free inverse minus the self-energy. Stated in an abstract operator ring `R` (the
ghost propagator is an operator in color/coordinate space). -/
theorem ghost_dyson_inverse {R : Type*} [Ring R] (G G₀ G₀inv selfEnergy : R)
    (hG₀ : G₀inv * G₀ = 1) (hDyson : G = G₀ + G₀ * selfEnergy * G) :
    (G₀inv - selfEnergy) * G = 1 := by
  have h1 : G₀inv * G = 1 + selfEnergy * G := by
    conv_lhs => rw [hDyson]
    rw [mul_add, hG₀, ← mul_assoc, ← mul_assoc, hG₀, one_mul]
  rw [sub_mul, h1, add_sub_cancel_right]

end Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum

end

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector_mul_self where
  formalizes @ "claim:the-coulomb-gauge-transverse-projector-delta-minus-k-k-over-k-squared-is-an-idempotent-projector-onto-the-physical-transverse-gluon-polarizations",
  supported_by @ "paper:feuchter-reinhardt-2004-variational-yang-mills-coulomb-gauge"

zil attach Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector_trace where
  supported_by @ "lean:HermitianMat.trace_one",
  supported_by @ "lean:HermitianMat.trace_smul",
  formalizes @ "claim:the-trace-of-the-coulomb-gauge-transverse-projector-is-d-minus-one-the-number-of-physical-transverse-gluon-polarizations",
  requires @ "claim:the-coulomb-gauge-transverse-projector-delta-minus-k-k-over-k-squared-is-an-idempotent-projector-onto-the-physical-transverse-gluon-polarizations"

zil attach Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.gluonPropagator_kernel_mul where
  formalizes @ "claim:the-variational-gluon-propagator-t-over-two-omega-inverts-the-gaussian-vacuum-kernel-two-omega-t-on-the-physical-transverse-subspace",
  requires @ "claim:the-coulomb-gauge-transverse-projector-delta-minus-k-k-over-k-squared-is-an-idempotent-projector-onto-the-physical-transverse-gluon-polarizations",
  supported_by @ "paper:feuchter-reinhardt-2004-variational-yang-mills-coulomb-gauge",
  caveat @ "claim:the-variational-gluon-energy-omega-of-k-is-assumed-positive-not-solved-from-the-gap-equation"

zil attach Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.ghost_dyson_inverse where
  formalizes @ "claim:the-ghost-dyson-schwinger-equation-gives-the-inverse-ghost-propagator-as-the-free-inverse-minus-the-ghost-self-energy",
  supported_by @ "paper:feuchter-reinhardt-2004-variational-yang-mills-coulomb-gauge"

zil_file_contract physlib.yangMillsCoulombGaugeVacuum where
  promises "The geometric core of the Coulomb-gauge Yang-Mills variational vacuum: the transverse projector delta minus k-k over k-squared is symmetric, annihilates the longitudinal momentum direction, is idempotent, and has trace d minus one (the d minus one physical transverse gluon polarizations); the variational gluon propagator t over two omega is transverse and inverts the Gaussian kernel two-omega-t on the physical subspace when the gluon energy is nonzero; and the ghost Dyson-Schwinger equation gives the inverse ghost propagator as the free inverse minus the self-energy."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector",
    "lean:Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.gluonPropagator"]
  forbids_substitutes ["a variational solution of the gluon energy from the coupled gap and Schwinger-Dyson equations, which the paper computes numerically",
    "a derivation of the confining Coulomb potential or the infrared ghost dominance, only the exact projector, propagator and Dyson-resummation algebra are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector_isSymm,
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector_mulVec_self,
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector_mul_self,
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.transverseProjector_trace,
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.gluonPropagator_mulVec_self,
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.gluonPropagator_kernel_mul,
    Physlib.QuantumMechanics.ComplexAction.YangMillsCoulombGaugeVacuum.ghost_dyson_inverse]

/- ZIL-END -/
