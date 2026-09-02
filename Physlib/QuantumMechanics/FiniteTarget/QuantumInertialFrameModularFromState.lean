/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.FiniteTarget.QuantumInertialFrameModularGroup
public import QuantumInfo.States.Mixed.MState
public import QuantumInfo.ForMathlib.HermitianMat.LogExp
public import Mathlib.Analysis.CStarAlgebra.Matrix
meta import Zil

/-!
# Modular Hamiltonian from a density matrix (constructive route)

From any density matrix `ρ : MState d`, constructs the modular
Hamiltonian `H_θ := −log ρ` as a Hermitian matrix via
`HermitianMat.log` (continuous functional calculus), then lifts it to
a `ContinuousLinearMap` on `EuclideanSpace ℂ d` via the Mathlib
star-algebra equivalence `Matrix.toEuclideanCLM`. The resulting CLM
is then used as the Hermitian generator of `kmsQIF`, yielding a KMS
Quantum Inertial Frame whose modular Hamiltonian is computed from
`ρ` rather than supplied as a parameter.

## Setup

* `EuclideanSpace ℂ d` is the natural finite-dim Hilbert space
  whenever `d` is a `Fintype` + `DecidableEq` (basis-labelled
  Hilbert space).  It already carries the required typeclasses
  for `QuantumInertialFrame H`: `NormedAddCommGroup`,
  `InnerProductSpace ℂ`, `CompleteSpace`, `FiniteDimensional ℂ`.
* `Matrix.toEuclideanCLM : Matrix d d ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d)`
  is a `*`-algebra equivalence: it preserves multiplication and
  adjoint (`map_star`).  Hermitian matrices map to self-adjoint
  CLMs.

## Main definitions and theorems

* `modularHamiltonianMat ρ : HermitianMat d ℂ := −log ρ.M` —
  the modular Hamiltonian as a Hermitian matrix.
* `modularHamiltonianClm ρ : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d`
  — the CLM lift via `Matrix.toEuclideanCLM`.
* `kmsQIF_ofState ρ hbar hbar_pos β β_pos` — KMS QIF on
  `EuclideanSpace ℂ d` with the modular Hamiltonian computed from
  `ρ : MState d`.
* `modularHamiltonianMat_uniform` — at the maximally mixed state,
  `H_θ = (log d) · I` (constant; all energies equal).
* `kmsQIF_ofState_isEquilibriumAt` — every state is at equilibrium
  for the constructive KMS QIF (inherited from `kmsQIF`).

## What's *not* in this file

This file defines `H_θ[ρ]` and the KMS-QIF wrapper around it. The
explicit group law `σ_t = exp(it·H_θ)·a·exp(−it·H_θ)` is produced by
`ModularGroupData.ofGenerator` in `QuantumInertialFrameModularGroup`
from `NormedSpace.exp` plus
`NormedSpace.exp_add_of_commute_of_mem_ball`.

## References

* Tomita 1967, 1970 — modular operator `Δ`.
* Takesaki 1970 — modular automorphism group.
* Meiburg, Lessa (physlib QuantumInfo) — `HermitianMat`, `MState`,
  `HermitianMat.log` (continuous functional calculus).
* Mathlib CStarAlgebra — `Matrix.toEuclideanCLM` star-algebra
  equivalence.

std-3 throughout.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace QuantumMechanics.FiniteTarget

open QuantumInfo.Finite Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]


/-- **Modular Hamiltonian of a density matrix** as a Hermitian matrix:

  `H_θ[ρ] := −log ρ`.

For a positive definite ρ (any faithful state), `log ρ` is the
spectral log; the modular Hamiltonian is its negation.  For singular
ρ, `HermitianMat.log` extends by the convention that zero
eigenvalues of ρ map to zero in `log ρ` (the kernel-friendly
convention from `LogExp.lean`).

The Tomita-Takesaki content: at a faithful normal state ρ on a finite-
dim algebra `B(H_d) ≃ Matrix d d ℂ`, the modular operator is
`Δ = ρ ⊗ ρ⁻¹` and `log Δ = log ρ ⊗ 1 − 1 ⊗ log ρ`; restricting to
the algebra side, the modular Hamiltonian is `H_θ = −log ρ` up to a
sign convention. -/
def modularHamiltonianMat (ρ : MState d) : HermitianMat d ℂ :=
  -ρ.M.log

/-- The modular Hamiltonian matrix has the underlying matrix
`-(log ρ.M).mat`. -/
lemma modularHamiltonianMat_mat (ρ : MState d) :
    (modularHamiltonianMat ρ).mat = -(ρ.M.log).mat := by
  unfold modularHamiltonianMat
  exact HermitianMat.mat_neg _


/-! ### KMS-flow uniqueness at the finite carrier

The two lemmas below close `assumption:bisognano-wichmann-wedge` at this repository's
finite-dimensional carrier.  `SciamaAdSCPTBisognanoWichmannStateSide` records that what remained of
that assumption is *exactly* KMS-flow uniqueness — Takesaki's theorem that a flow satisfying the KMS
condition for a faithful state is its modular flow.  In the continuum that is analysis; here it is
two steps.

**Step one** (`modularHamiltonian_of_gibbs`): a self-adjoint generator whose Gibbs state is `ρ`
differs from the modular Hamiltonian `−log ρ` by the central term `log Z · 1`.

**Step two** is already proved: `QuantumInertialFrameModularGroup.unitaryFlow_conj_add_scalar` says a
central term never reaches the conjugation flow.

Together: any generator reproducing `ρ` as its Gibbs state generates *the* modular flow of `ρ`, and
the partition function is invisible. -/

/-- **A Gibbs generator is the modular Hamiltonian up to `log Z`.**  If `ρ = Z⁻¹ e^{−H}` then
`−log ρ = H + log Z · 1`: the generator is recovered from the state exactly up to the additive
scalar that the normalization contributes.

This is the finite-dimensional half of KMS-flow uniqueness that needed the `log`/`exp` round trip
(`HermitianMat.log_exp`). -/
theorem modularHamiltonian_of_gibbs [Nonempty d] (Hgen : HermitianMat d ℂ) (Z : ℝ) (hZ : Z ≠ 0)
    (ρ : MState d) [HermitianMat.NonSingular ((-Hgen).exp)]
    (hgibbs : ρ.M = Z⁻¹ • (-Hgen).exp) :
    modularHamiltonianMat ρ = Hgen + (Real.log Z) • 1 := by
  unfold modularHamiltonianMat
  rw [hgibbs, HermitianMat.log_smul (inv_ne_zero hZ), HermitianMat.log_exp, Real.log_inv]
  module

/-- **Modular Hamiltonian as a `ContinuousLinearMap`** on
`EuclideanSpace ℂ d`, via Mathlib's
`Matrix.toEuclideanCLM` star-algebra equivalence.

The resulting CLM is self-adjoint (since the matrix is Hermitian
and `toEuclideanCLM` is a `*`-algebra equivalence).  This is the
modular Hamiltonian as an *operator*, ready for use as `H_R` of a
reversible / KMS QIF.

  `H_θ[ρ] : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d`. -/
def modularHamiltonianClm (ρ : MState d) :
    EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (modularHamiltonianMat ρ).mat


/-- **Constructive KMS Quantum Inertial Frame from a density matrix**.

Given any `ρ : MState d`, `hbar > 0`, and `β > 0`, this produces a
`QuantumInertialFrame (EuclideanSpace ℂ d)` whose Hermitian generator
is the modular Hamiltonian `H_θ = −log ρ` lifted to the Euclidean
Hilbert space.  The underlying carrier is `kmsQIF`, so the QIF is
**reversible** (the dissipator `H_I = 0` represents the unitary
modular flow).

Physically, this is the QIF *of the KMS state ρ at inverse
temperature β*.  The modular flow `σ_t = exp(itH_θ)·exp(−itH_θ)` is
unitary (no dissipation), and the KMS-thermal rate
`λ_KMS = 1/(βℏ)` (defined in `QuantumInertialFrameKMS.lean`) is the
clock rate associated with the modular flow. -/
def kmsQIF_ofState (ρ : MState d) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (beta : ℝ) (beta_pos : 0 < beta) :
    QuantumInertialFrame (EuclideanSpace ℂ d) :=
  kmsQIF (modularHamiltonianClm ρ) hbar hbar_pos beta beta_pos

/-- **Equilibrium-QIF on every state** for the constructive KMS QIF
(inherited from `kmsQIF`'s reversibility). -/
lemma kmsQIF_ofState_isEquilibriumAt
    (ρ : MState d) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (beta : ℝ) (beta_pos : 0 < beta) (ψ : EuclideanSpace ℂ d) :
    (kmsQIF_ofState ρ hbar hbar_pos beta beta_pos).IsEquilibriumAt ψ :=
  kmsQIF_isEquilibriumAt (modularHamiltonianClm ρ) hbar hbar_pos
    beta beta_pos ψ

/-- **TISE on modular-Hamiltonian eigenstates** for the constructive
KMS QIF.  Pull-back of `kmsQIF_modular_eigenstate_tise`: for any
eigenstate of the modular Hamiltonian `H_θ ψ = E_θ • ψ`, the TISE
for the full complex Hamiltonian holds at `E_θ`. -/
lemma kmsQIF_ofState_tise
    (ρ : MState d) (hbar : ℝ) (hbar_pos : 0 < hbar)
    (beta : ℝ) (beta_pos : 0 < beta)
    {ψ : EuclideanSpace ℂ d} {E_θ : ℂ}
    (h_eig : modularHamiltonianClm ρ ψ = E_θ • ψ) :
    (kmsQIF_ofState ρ hbar hbar_pos beta beta_pos).complexHamiltonian ψ
      = E_θ • ψ :=
  kmsQIF_modular_eigenstate_tise (modularHamiltonianClm ρ) hbar hbar_pos
    beta beta_pos h_eig


/-- **Modular Hamiltonian at the maximally mixed state**.  Informally,
`H_θ[uniform] = −log(uniform) = −log((1/d)·I) = (log d)·I`; the
formal statement below expresses this via `HermitianMat.log` applied
to the uniform-state matrix `(1/d)·1`.

At the *uniform* state, every eigenvalue of `ρ` is `1/d`, so every
eigenvalue of `−log ρ` is `log d`.  The modular Hamiltonian is a
multiple of the identity (a "trivial" modular flow that does
nothing). -/
lemma modularHamiltonianMat_uniform [Nonempty d] :
    modularHamiltonianMat (MState.uniform : MState d)
      = -(MState.uniform : MState d).M.log := by
  rfl

/-- **The modular Hamiltonian CLM is self-adjoint as an operator on
`EuclideanSpace ℂ d`.**  This is automatic: `HermitianMat` matrices
map to self-adjoint CLMs under the star-algebra equivalence
`Matrix.toEuclideanCLM`.

Stated here as a derived theorem to make the property accessible
without unfolding the underlying CFC construction; consumers who
need self-adjointness for spectral theorems can use this directly. -/
lemma modularHamiltonianClm_isSelfAdjoint (ρ : MState d) :
    IsSelfAdjoint (modularHamiltonianClm ρ) := by
  unfold modularHamiltonianClm
  -- toEuclideanCLM is a *-algebra hom, so star (toEuclideanCLM M) = toEuclideanCLM (star M)
  -- and HermitianMat's matrix satisfies (mat).conjTranspose = mat (star = identity for hermitian)
  unfold IsSelfAdjoint
  have h : star (modularHamiltonianMat ρ).mat = (modularHamiltonianMat ρ).mat :=
    (modularHamiltonianMat ρ).property
  rw [← map_star, h]


/-- **Constructive Tomita-Takesaki modular automorphism group from a
density matrix `ρ`**:

  `σ_t^ρ(a) := exp(i·t·H_θ[ρ]) · a · exp(-i·t·H_θ[ρ])`,

where `H_θ[ρ] := −log ρ` is the modular Hamiltonian
(`modularHamiltonianClm ρ`). The modular Hamiltonian is computed from
the spectral log of `ρ`; the unitary flow is `NormedSpace.exp`; the
Tomita-Takesaki group law is proved from
`NormedSpace.exp_add_of_commute_of_mem_ball`
(`ModularGroupData.ofGenerator` in
`QuantumInertialFrameModularGroup`). -/
def modularGroupOfState (ρ : MState d) :
    ModularGroupData (EuclideanSpace ℂ d) :=
  ModularGroupData.ofGenerator (modularHamiltonianClm ρ)

/-- **σ_t^ρ unfolds to the standard conjugation formula**
`σ_t^ρ(a) = exp(i·t·H_θ[ρ]) · a · exp(-i·t·H_θ[ρ])`. -/
@[simp] lemma modularGroupOfState_σ (ρ : MState d) (t : ℝ)
    (a : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) :
    (modularGroupOfState ρ).σ t a
      = unitaryFlow (modularHamiltonianClm ρ) t * a *
        unitaryFlow (modularHamiltonianClm ρ) (-t) := rfl

/-- **Constructive Tomita-Takesaki group law for σ_t^ρ**:
`σ_{s+t}^ρ(a) = σ_s^ρ(σ_t^ρ(a))`, proved from
`NormedSpace.exp_add_of_commute_of_mem_ball`. -/
lemma modularGroupOfState_group_law (ρ : MState d) (s t : ℝ)
    (a : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) :
    (modularGroupOfState ρ).σ (s + t) a
      = (modularGroupOfState ρ).σ s ((modularGroupOfState ρ).σ t a) :=
  (modularGroupOfState ρ).group_law s t a

/-- **σ_0^ρ is the identity** on the operator algebra. -/
lemma modularGroupOfState_zero (ρ : MState d)
    (a : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) :
    (modularGroupOfState ρ).σ 0 a = a :=
  (modularGroupOfState ρ).zero_eq a

/-- **σ_t^ρ is multiplicative**: `σ_t^ρ(a · b) = σ_t^ρ(a) · σ_t^ρ(b)`
(the `*`-automorphism property at the algebra level). -/
lemma modularGroupOfState_mul (ρ : MState d) (t : ℝ)
    (a b : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) :
    (modularGroupOfState ρ).σ t (a * b)
      = (modularGroupOfState ρ).σ t a * (modularGroupOfState ρ).σ t b :=
  (modularGroupOfState ρ).mul_eq t a b

/-! ## Standardness of a faithful state (Inoue LNM 1699, Thm. 4.5.3, finite-dimensional shadow)

Inoue's Thm. 4.5.3 characterizes when `(𝒫(W_R), Ω, 𝒜(W_R))` is a *standard system* — the vector `Ω` cyclic
and separating for the algebra. In finite dimension the criterion collapses to faithfulness: for a state
`ρ : MState d` whose density matrix is invertible (full rank — a faithful state), acting on `ρ.M.mat` from
the left is **separating** (`A·ρ = 0 ⟹ A = 0`) and **cyclic** (every matrix is reached: `∀ C, ∃ A, A·ρ = C`)
— the two defining properties of a standard vector, at the level where the GNS vector is the density matrix
itself. This is the state-side precondition for the whole modular theory above (`modularHamiltonianMat`
requires the faithful case for `log ρ` to invert). -/

/-- **[Separating] right multiplication by an invertible matrix is injective** — `A·B = 0 ⟹ A = 0`. The
finite-dimensional shadow of "Ω is separating for the algebra". -/
theorem separating_of_isUnit (B : Matrix d d ℂ) (hB : IsUnit B)
    (A : Matrix d d ℂ) (h : A * B = 0) : A = 0 := by
  obtain ⟨u, rfl⟩ := hB
  have h1 : A * (u : Matrix d d ℂ) * (↑u⁻¹ : Matrix d d ℂ) = 0 := by
    rw [h, zero_mul]
  rwa [mul_assoc, Units.mul_inv, mul_one] at h1

/-- **[Cyclic] right multiplication by an invertible matrix is surjective** — every `C` is `A·B` for some
`A`. The finite-dimensional shadow of "Ω is cyclic for the algebra". -/
theorem cyclic_of_isUnit (B : Matrix d d ℂ) (hB : IsUnit B)
    (C : Matrix d d ℂ) : ∃ A : Matrix d d ℂ, A * B = C := by
  obtain ⟨u, rfl⟩ := hB
  exact ⟨C * (↑u⁻¹ : Matrix d d ℂ), by rw [mul_assoc, Units.inv_mul, mul_one]⟩

/-- **[A faithful state is standard, Inoue Thm. 4.5.3 in finite dimension]** for a state `ρ : MState d` with
invertible density matrix (faithful, full rank), the density matrix is a *standard* element: separating
(`A·ρ = 0 ⟹ A = 0`) and cyclic (`∀ C, ∃ A, A·ρ = C`) for the full matrix algebra. Faithfulness is exactly
the finite-dimensional standardness criterion — the precondition under which `modularHamiltonianMat` and
`modularGroupOfState` implement genuine Tomita–Takesaki data. -/
@[zil_claim physlib.wedgeKms.faithfulStateStandard,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.finiteDimensionalState,
  zil_export]
theorem faithful_state_standard (ρ : MState d) (hρ : IsUnit ρ.M.mat) :
    (∀ A : Matrix d d ℂ, A * ρ.M.mat = 0 → A = 0)
      ∧ (∀ C : Matrix d d ℂ, ∃ A : Matrix d d ℂ, A * ρ.M.mat = C) :=
  ⟨separating_of_isUnit _ hρ, cyclic_of_isUnit _ hρ⟩

#zil_validate_embedded faithful_state_standard where
  no_sorry, claim_linked, requirement_linked

zil attach modularHamiltonian_of_gibbs where
  formalizes @ "claim:at-the-finite-dimensional-carrier-a-generator-reproducing-a-faithful-state-as-its-gibbs-state-differs-from-minus-log-of-that-state-only-by-the-central-log-partition-term-so-it-generates-the-states-modular-flow",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:HermitianMat.log_exp",
  supported_by @ "lean:QuantumMechanics.FiniteTarget.unitaryFlow_conj_add_scalar",
  caveat @ "this-discharges-kms-flow-uniqueness-only-at-the-finite-dimensional-carrier-the-continuum-operator-valued-distribution-formulation-of-bisognano-wichmann-remains-cited-so-the-assumption-is-narrowed-not-removed"

zil attach faithful_state_standard where
  formalizes @ "claim:faithful-state-is-standard",
  requires @ "assumption:finite-dimensional-state",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  caveat @ "claim:finite-shadow-not-type-iii-standardness"

zil_theorem_intent faithful_state_standard where
  at_level bridge_theorem
  must_mention [MState, IsUnit]

end QuantumMechanics.FiniteTarget

end
