/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QuantumMechanics.Liouville.Schrodinger
public import Physlib.QuantumMechanics.Lindblad.FullLindbladODE
public import Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HilbertSchmidtOperatorIdeal
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Second quantization of open systems in Liouville space

Finite-dimensional algebraic layer for Sukharnikov--Chuchurka--Benediktovitch--
Rohringer, *Second quantization of open quantum systems in Liouville space*
(arXiv:2207.14234v2).

The paper's core construction is that a one-particle matrix unit
`|i⟩⟨j|` becomes a Liouville basis ket `|ij⟩⟩`.  For an `M`-level
particle, the bosonic Liouville Fock modes are therefore indexed by
pairs `(i,j)`, so there are `M^2` modes.  The fixed-`N` sector is the
occupation register whose total occupation is `N`.

This file formalizes the part that is already supported by the repo:

* Hilbert multi-indices, permutation-invariant coefficients, and the
  pure/reduced density-matrix coefficient formulas.
* Liouville modes `(i,j)`, multi-indices, and their `M^2` / `M^(2N)` counts.
* Fixed-particle occupation registers and the number-operator identity.
* The paper's binomial dimension formula as the closed-form sector size.
* Occupation transpose and diagonal trace-support predicates.
* Bosonic CCR deltas, raise/lower occupation maps, amplitudes, vacuum, and
  trace amplitudes.
* The left/right/sandwich Liouville multiplication decomposition, including
  the finite matrix-unit form of the `Γ` algebra, used by GKLS/Lindblad
  open-system dynamics.
* Section III occupation-number representation: density/observable
  coefficients, trace-one normalization, expectation values, generating
  functions, finite master equations, and two-time correlations.
* A bridge to the existing finite-matrix Hilbert-Schmidt inner product and
  `FullLindbladODE` trace-preservation theorems.

No continuum measure, unbounded operator, or path-integral claim is introduced
here; this is the finite Liouville-space second-quantized algebraic core.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.Liouville.SecondQuantization

open Matrix Complex
open QuantumMechanics.FiniteTarget (commutator anticommutator)
open Physlib.QuantumMechanics.Lindblad
open Physlib.QuantumMechanics.Liouville.Schrodinger
open Physlib.QuantumMechanics.ComplexAction.OperatorAlgebra.HilbertSchmidtOperatorIdeal

/-! ## Section II A-B: Hilbert labels and Liouville superkets -/

/-- A Hilbert-space multi-index `i = (i₁, ..., i_N)` for `N` identical
`M`-level particles. -/
abbrev HilbertMultiIndex (M N : ℕ) : Type := Fin N → Fin M

/-- The unsymmetrized Hilbert label space in Eq. (1) has `M^N` basis labels. -/
theorem hilbertMultiIndex_card (M N : ℕ) :
    Fintype.card (HilbertMultiIndex M N) = M ^ N := by
  simp [HilbertMultiIndex]

/-- The symmetric Hilbert sector of `N` identical particles over `M` one-particle
levels, represented as the `N`th symmetric power of `Fin M`. -/
abbrev SymmetricHilbertSector (M N : ℕ) : Type := Sym (Fin M) N

/-- Stars-and-bars count for the symmetric Hilbert sector:
`dim Sym^N(ℂ^M) = binomial(M + N - 1, N)`. -/
theorem symmetricHilbertSector_card (M N : ℕ) :
    Fintype.card (SymmetricHilbertSector M N) =
      Nat.choose (M + N - 1) N := by
  classical
  simpa [SymmetricHilbertSector] using
    (Sym.card_sym_eq_choose (α := Fin M) N)

/-- One-particle finite matrix operators on the `M`-level Hilbert space. -/
abbrev OneParticleOperator (M : ℕ) : Type := Matrix (Fin M) (Fin M) ℂ

/-- The paper's one-particle transition operator
`σ_{ij} = |i⟩⟨j|`, represented as a finite matrix unit. -/
def oneParticleMatrixUnit {M : ℕ} (i j : Fin M) : OneParticleOperator M :=
  Matrix.single i j 1

/-- Matrix-entry form of `σ_{ij} = |i⟩⟨j|`. -/
theorem oneParticleMatrixUnit_apply
    {M : ℕ} (i j p q : Fin M) :
    oneParticleMatrixUnit i j p q =
      if i = p ∧ j = q then 1 else 0 := by
  rfl

/-- Matrix units multiply as `σ_{ij} σ_{pq} = δ_{jp} σ_{iq}`. -/
theorem oneParticleMatrixUnit_mul
    {M : ℕ} (i j p q : Fin M) :
    oneParticleMatrixUnit i j * oneParticleMatrixUnit p q =
      if j = p then oneParticleMatrixUnit i q else 0 := by
  by_cases h : j = p
  · subst p
    simp [oneParticleMatrixUnit]
  · simp [oneParticleMatrixUnit, Matrix.single_mul_single_of_ne, h]

/-- Relabel particles by a permutation of the particle index set. -/
def permuteHilbertMultiIndex {M N : ℕ} (π : Equiv.Perm (Fin N))
    (i : HilbertMultiIndex M N) : HilbertMultiIndex M N :=
  fun μ => i (π μ)

/-- Coefficients of a state vector are permutation invariant when relabelling
the identical particles leaves them unchanged. -/
def PermutationInvariantHilbertCoefficients {M N : ℕ}
    (C : HilbertMultiIndex M N → ℂ) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) (i : HilbertMultiIndex M N),
    C (permuteHilbertMultiIndex π i) = C i

/-- Pure-state density-matrix coefficients `Cᵢ Cⱼ*`. -/
def pureDensityCoefficient {M N : ℕ}
    (C : HilbertMultiIndex M N → ℂ)
    (i j : HilbertMultiIndex M N) : ℂ :=
  C i * star (C j)

/-- If state-vector coefficients are permutation invariant, then the pure
density-matrix coefficients are invariant under simultaneous particle
permutation. -/
theorem pureDensityCoefficient_permutationInvariant
    {M N : ℕ} {C : HilbertMultiIndex M N → ℂ}
    (hC : PermutationInvariantHilbertCoefficients C)
    (π : Equiv.Perm (Fin N)) (i j : HilbertMultiIndex M N) :
    pureDensityCoefficient C (permuteHilbertMultiIndex π i)
        (permuteHilbertMultiIndex π j)
      = pureDensityCoefficient C i j := by
  simp [pureDensityCoefficient, hC π i, hC π j]

/-- Reduced density-matrix coefficient after tracing a finite environment:
`Cᵢⱼ = ∑_env Cᵢ,env Cⱼ,env*`. -/
def reducedDensityCoefficient {M N Env : ℕ}
    (C : HilbertMultiIndex M N → Fin Env → ℂ)
    (i j : HilbertMultiIndex M N) : ℂ :=
  ∑ env : Fin Env, C i env * star (C j env)

/-- With a singleton environment, the reduced coefficient is the pure
coefficient. -/
theorem reducedDensityCoefficient_one_eq_pure
    {M N : ℕ} (C : HilbertMultiIndex M N → ℂ)
    (i j : HilbertMultiIndex M N) :
    reducedDensityCoefficient (Env := 1) (fun k _ => C k) i j =
      pureDensityCoefficient C i j := by
  simp [reducedDensityCoefficient, pureDensityCoefficient]

/-- Environment-indexed state coefficients are permutation invariant when each
environment component is invariant under relabelling identical particles. -/
def PermutationInvariantEnvironmentCoefficients {M N Env : ℕ}
    (C : HilbertMultiIndex M N → Fin Env → ℂ) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) (i : HilbertMultiIndex M N) (env : Fin Env),
    C (permuteHilbertMultiIndex π i) env = C i env

/-- Tracing out a finite environment preserves permutation invariance of the
reduced density-matrix coefficients. -/
theorem reducedDensityCoefficient_permutationInvariant
    {M N Env : ℕ} {C : HilbertMultiIndex M N → Fin Env → ℂ}
    (hC : PermutationInvariantEnvironmentCoefficients C)
    (π : Equiv.Perm (Fin N)) (i j : HilbertMultiIndex M N) :
    reducedDensityCoefficient C (permuteHilbertMultiIndex π i)
        (permuteHilbertMultiIndex π j)
      = reducedDensityCoefficient C i j := by
  simp [reducedDensityCoefficient, hC π i, hC π j]

/-! ## Section II B: Liouville pair labels -/

/-! ## Liouville occupation registers -/

/-- A Liouville-space mode for an `M`-level particle is a pair `(i,j)`,
corresponding to the matrix unit `|i⟩⟨j|` and the superket `|ij⟩⟩`. -/
abbrev LiouvilleMode (M : ℕ) : Type := Fin M × Fin M

/-- The number of Liouville modes is `M^2`. -/
theorem liouvilleMode_card (M : ℕ) :
    Fintype.card (LiouvilleMode M) = M * M := by
  simp [LiouvilleMode]

/-- A Liouville multi-index is a choice of one superket label `|iμ jμ⟩⟩`
for each particle. -/
abbrev LiouvilleMultiIndex (M N : ℕ) : Type := Fin N → LiouvilleMode M

/-- The ket-bra pair of Hilbert multi-indices gives the corresponding
Liouville multi-index. -/
def ketBraLiouvilleMultiIndex {M N : ℕ}
    (i j : HilbertMultiIndex M N) : LiouvilleMultiIndex M N :=
  fun μ => (i μ, j μ)

/-- Recover the Hilbert ket and bra multi-indices from a Liouville multi-index. -/
def liouvilleMultiIndexToKetBra {M N : ℕ}
    (a : LiouvilleMultiIndex M N) :
    HilbertMultiIndex M N × HilbertMultiIndex M N :=
  (fun μ => (a μ).1, fun μ => (a μ).2)

/-- Eq. (4)--(5) as an equivalence of finite labels:
a Liouville-Hilbert superket label is exactly a ket/bra pair of Hilbert
multi-indices. -/
def hilbertPairLiouvilleEquiv (M N : ℕ) :
    (HilbertMultiIndex M N × HilbertMultiIndex M N) ≃
      LiouvilleMultiIndex M N where
  toFun x := ketBraLiouvilleMultiIndex x.1 x.2
  invFun a := liouvilleMultiIndexToKetBra a
  left_inv := by
    rintro ⟨i, j⟩
    rfl
  right_inv := by
    intro a
    funext μ
    exact Prod.ext rfl rfl

/-- The first component of the Liouville multi-index is the ket index. -/
theorem ketBraLiouvilleMultiIndex_fst
    {M N : ℕ} (i j : HilbertMultiIndex M N) (μ : Fin N) :
    (ketBraLiouvilleMultiIndex i j μ).1 = i μ :=
  rfl

/-- The second component of the Liouville multi-index is the bra index. -/
theorem ketBraLiouvilleMultiIndex_snd
    {M N : ℕ} (i j : HilbertMultiIndex M N) (μ : Fin N) :
    (ketBraLiouvilleMultiIndex i j μ).2 = j μ :=
  rfl

/-- Vectorizing and then projecting back to ket/bra labels is the identity. -/
theorem liouvilleMultiIndexToKetBra_ketBra
    {M N : ℕ} (i j : HilbertMultiIndex M N) :
    liouvilleMultiIndexToKetBra (ketBraLiouvilleMultiIndex i j) = (i, j) :=
  rfl

/-- The ket/bra reconstruction of a Liouville multi-index vectorizes back to
the original Liouville multi-index. -/
theorem ketBra_liouvilleMultiIndexToKetBra
    {M N : ℕ} (a : LiouvilleMultiIndex M N) :
    ketBraLiouvilleMultiIndex (liouvilleMultiIndexToKetBra a).1
        (liouvilleMultiIndexToKetBra a).2 = a := by
  funext μ
  exact Prod.ext rfl rfl

/-- The unsymmetrized Liouville space has `M^(2N)` labels, expressed as
`(M*M)^N` in the pair-mode representation. -/
theorem liouvilleMultiIndex_card (M N : ℕ) :
    Fintype.card (LiouvilleMultiIndex M N) = (M * M) ^ N := by
  simp [LiouvilleMultiIndex, LiouvilleMode]

/-- The Liouville label count is the count of ket/bra Hilbert-label pairs. -/
theorem liouvilleMultiIndex_card_eq_hilbert_pair_card (M N : ℕ) :
    Fintype.card (LiouvilleMultiIndex M N) =
      Fintype.card (HilbertMultiIndex M N × HilbertMultiIndex M N) := by
  exact Fintype.card_congr (hilbertPairLiouvilleEquiv M N).symm

/-- The Liouville exponential wall is the square of the Hilbert label count:
`M^N · M^N`. -/
theorem liouvilleMultiIndex_card_eq_hilbert_square (M N : ℕ) :
    Fintype.card (LiouvilleMultiIndex M N) = M ^ N * M ^ N := by
  rw [liouvilleMultiIndex_card, Nat.mul_pow]

/-- The same count in the paper's notation: `M^(2N)`. -/
theorem liouvilleMultiIndex_card_eq_pow_two_mul (M N : ℕ) :
    Fintype.card (LiouvilleMultiIndex M N) = M ^ (2 * N) := by
  rw [liouvilleMultiIndex_card_eq_hilbert_square, ← pow_add, two_mul]

/-- Transport density-matrix coefficients `Cᵢⱼ` to Liouville superket
coefficients using the Eq. (4)--(5) ket/bra equivalence. -/
def liouvilleCoefficientFromDensity {M N : ℕ}
    (C : HilbertMultiIndex M N → HilbertMultiIndex M N → ℂ)
    (a : LiouvilleMultiIndex M N) : ℂ :=
  C (liouvilleMultiIndexToKetBra a).1 (liouvilleMultiIndexToKetBra a).2

/-- On labels of the form `|i₁j₁⟩⟩ ... |i_Nj_N⟩⟩`, the transported
Liouville coefficient is exactly `Cᵢⱼ`. -/
theorem liouvilleCoefficientFromDensity_ketBra
    {M N : ℕ}
    (C : HilbertMultiIndex M N → HilbertMultiIndex M N → ℂ)
    (i j : HilbertMultiIndex M N) :
    liouvilleCoefficientFromDensity C (ketBraLiouvilleMultiIndex i j) =
      C i j :=
  rfl

/-- Pure-state Liouville coefficient corresponding to Eq. (3) with
`Cᵢⱼ = Cᵢ Cⱼ*`. -/
def pureLiouvilleCoefficient {M N : ℕ}
    (C : HilbertMultiIndex M N → ℂ)
    (a : LiouvilleMultiIndex M N) : ℂ :=
  liouvilleCoefficientFromDensity (pureDensityCoefficient C) a

/-- Reduced Liouville coefficient after tracing a finite environment:
`Cᵢⱼ = ∑_env Cᵢ,env Cⱼ,env*`. -/
def reducedLiouvilleCoefficient {M N Env : ℕ}
    (C : HilbertMultiIndex M N → Fin Env → ℂ)
    (a : LiouvilleMultiIndex M N) : ℂ :=
  liouvilleCoefficientFromDensity (reducedDensityCoefficient C) a

/-- Pure-state vectorization gives the paper's coefficient
`Cᵢ Cⱼ*` on the superket labelled by `(i,j)`. -/
theorem pureLiouvilleCoefficient_ketBra
    {M N : ℕ} (C : HilbertMultiIndex M N → ℂ)
    (i j : HilbertMultiIndex M N) :
    pureLiouvilleCoefficient C (ketBraLiouvilleMultiIndex i j) =
      C i * star (C j) :=
  rfl

/-- Reduced vectorization gives the paper's coefficient
`∑_env Cᵢ,env Cⱼ,env*` on the superket labelled by `(i,j)`. -/
theorem reducedLiouvilleCoefficient_ketBra
    {M N Env : ℕ} (C : HilbertMultiIndex M N → Fin Env → ℂ)
    (i j : HilbertMultiIndex M N) :
    reducedLiouvilleCoefficient C (ketBraLiouvilleMultiIndex i j) =
      ∑ env : Fin Env, C i env * star (C j env) :=
  rfl

/-- Symmetric density matrices in Liouville-Hilbert space are multisets of
`N` Liouville modes, i.e. `Sym^N(Fin M × Fin M)`. -/
abbrev SymmetricLiouvilleSector (M N : ℕ) : Type := Sym (LiouvilleMode M) N

/-- Eq. (6): the symmetric Liouville-Hilbert sector has
`binomial(N + M^2 - 1, N)` labels. -/
theorem symmetricLiouvilleSector_card (M N : ℕ) :
    Fintype.card (SymmetricLiouvilleSector M N) =
      Nat.choose (N + M * M - 1) N := by
  classical
  have h :=
    (Sym.card_sym_eq_choose (α := LiouvilleMode M) N)
  simpa [SymmetricLiouvilleSector, LiouvilleMode, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

/-- Kronecker delta on one-particle levels. -/
def finDelta {M : ℕ} (i j : Fin M) : ℂ :=
  if i = j then 1 else 0

/-- Kronecker delta on Liouville modes. -/
def liouvilleModeDelta {M : ℕ} (a b : LiouvilleMode M) : ℂ :=
  if a = b then 1 else 0

/-- The Liouville-mode delta factors into the two ordinary deltas
`δᵢₚ δⱼq`. -/
theorem liouvilleModeDelta_pair
    {M : ℕ} (i j p q : Fin M) :
    liouvilleModeDelta (i, j) (p, q) = finDelta i p * finDelta j q := by
  by_cases hi : i = p
  · subst p
    by_cases hj : j = q
    · subst q
      simp [liouvilleModeDelta, finDelta]
    · simp [liouvilleModeDelta, finDelta, hj]
  · simp [liouvilleModeDelta, finDelta, hi]

/-- Scalar form of the bosonic CCR index factor:
`[bᵢⱼ, b†ₛₜ] = δᵢₛ δⱼₜ`. -/
def bosonicCCRDelta {M : ℕ} (i j s t : Fin M) : ℂ :=
  liouvilleModeDelta (i, j) (s, t)

/-- The CCR scalar is exactly the product of the two Kronecker deltas. -/
theorem bosonicCCRDelta_eq
    {M : ℕ} (i j s t : Fin M) :
    bosonicCCRDelta i j s t = finDelta i s * finDelta j t :=
  liouvilleModeDelta_pair i j s t

/-! ## Section II C: Liouville-Hilbert inner product and bosonization -/

/-- Eq. (7): the Liouville-Hilbert inner product is the finite
Hilbert-Schmidt product `⟪A|B⟫ = Tr(A†B)`. -/
noncomputable def liouvilleHilbertInner {M : ℕ}
    (A B : OneParticleOperator M) : ℂ :=
  matrixHSInner A B

/-- Superket basis element `|ij⟩⟩`, represented by the matrix unit
`|i⟩⟨j|`. -/
def liouvilleSuperketMatrix {M : ℕ} (a : LiouvilleMode M) :
    OneParticleOperator M :=
  oneParticleMatrixUnit a.1 a.2

/-- Eq. (7) on basis superkets:
`⟪ij|pq⟫ = δᵢₚ δⱼq`. -/
theorem liouvilleHilbertInner_superket
    {M : ℕ} (i j p q : Fin M) :
    liouvilleHilbertInner (liouvilleSuperketMatrix (i, j))
        (liouvilleSuperketMatrix (p, q)) =
      finDelta i p * finDelta j q := by
  by_cases hip : i = p
  · subst p
    by_cases hjq : j = q
    · subst q
      simp [liouvilleHilbertInner, liouvilleSuperketMatrix,
        oneParticleMatrixUnit, matrixHSInner, finDelta]
    · simp [liouvilleHilbertInner, liouvilleSuperketMatrix,
        oneParticleMatrixUnit, matrixHSInner, finDelta, hjq]
  · simp [liouvilleHilbertInner, liouvilleSuperketMatrix,
      oneParticleMatrixUnit, matrixHSInner, finDelta, hip]

/-- Eq. (7) in Liouville-mode notation. -/
theorem liouvilleHilbertInner_superket_eq_delta
    {M : ℕ} (a b : LiouvilleMode M) :
    liouvilleHilbertInner (liouvilleSuperketMatrix a)
        (liouvilleSuperketMatrix b) =
      liouvilleModeDelta a b := by
  rcases a with ⟨i, j⟩
  rcases b with ⟨p, q⟩
  rw [liouvilleHilbertInner_superket, liouvilleModeDelta_pair]

/-- The left action of `σ_{pq}` on a one-particle Liouville mode:
`σ_{pq}|ij⟩⟩` is nonzero only when `i = q`, in which case it becomes
`|pj⟩⟩`. -/
def leftActionMode {M : ℕ} (p q : Fin M) (a : LiouvilleMode M) :
    Option (LiouvilleMode M) :=
  if a.1 = q then some (p, a.2) else none

/-- The right action of `σ_{kℓ}` on a one-particle Liouville mode:
`|ij⟩⟩ σ_{kℓ}` is nonzero only when `j = k`, in which case it becomes
`|iℓ⟩⟩`. -/
def rightActionMode {M : ℕ} (k ℓ : Fin M) (a : LiouvilleMode M) :
    Option (LiouvilleMode M) :=
  if a.2 = k then some (a.1, ℓ) else none

@[simp] theorem leftActionMode_matching
    {M : ℕ} (p q t : Fin M) :
    leftActionMode p q (q, t) = some (p, t) := by
  simp [leftActionMode]

@[simp] theorem rightActionMode_matching
    {M : ℕ} (s k ℓ : Fin M) :
    rightActionMode k ℓ (s, k) = some (s, ℓ) := by
  simp [rightActionMode]

/-- Independent-reservoir sandwich action on one Liouville mode:
left `σ_{pq}` and right `σ_{kℓ}` send `|qk⟩⟩` to `|pℓ⟩⟩`. -/
def sandwichActionMode {M : ℕ} (p q k ℓ : Fin M)
    (a : LiouvilleMode M) : Option (LiouvilleMode M) :=
  if a = (q, k) then some (p, ℓ) else none

@[simp] theorem sandwichActionMode_matching
    {M : ℕ} (p q k ℓ : Fin M) :
    sandwichActionMode p q k ℓ (q, k) = some (p, ℓ) := by
  simp [sandwichActionMode]

/-- Occupation numbers of the `M^2` Liouville modes. -/
abbrev LiouvilleOccupation (M : ℕ) : Type := LiouvilleMode M → ℕ

/-- Total occupation, the eigenvalue of the Liouville-space number operator
`∑_{p,q} b†_{pq} b_{pq}` on an occupation basis vector. -/
def totalOccupation {M : ℕ} (n : LiouvilleOccupation M) : ℕ :=
  ∑ a : LiouvilleMode M, n a

/-- Fixed-`N` Liouville sector: occupation registers with total occupation
exactly `N`. -/
def FixedParticleLiouvilleOccupation (M N : ℕ) : Type :=
  {n : LiouvilleOccupation M // totalOccupation n = N}

/-- The fixed-particle subtype records exactly the number-operator equation
`∑_{p,q} n_{pq} = N`. -/
theorem fixedParticle_totalOccupation
    {M N : ℕ} (n : FixedParticleLiouvilleOccupation M N) :
    totalOccupation n.1 = N :=
  n.2

/-- The paper's symmetric Liouville-sector dimension:
`binomial(N + M^2 - 1, N)`.  This is the stars-and-bars closed form for
placing `N` identical Liouville-space bosons into `M^2` modes. -/
def symmetricLiouvilleDimension (M N : ℕ) : ℕ :=
  Nat.choose (N + M * M - 1) N

/-- The symbolic dimension formula is the closed form used in the paper. -/
theorem symmetricLiouvilleDimension_eq_choose (M N : ℕ) :
    symmetricLiouvilleDimension M N = Nat.choose (N + M * M - 1) N :=
  rfl

/-- The existing closed-form dimension is the cardinality of the symmetric
Liouville sector `Sym^N(Fin M × Fin M)`. -/
theorem symmetricLiouvilleSector_card_eq_dimension (M N : ℕ) :
    Fintype.card (SymmetricLiouvilleSector M N) =
      symmetricLiouvilleDimension M N := by
  rw [symmetricLiouvilleSector_card, symmetricLiouvilleDimension]

/-- The Liouville number operator is the total occupation sum on a basis
register. -/
theorem liouvilleNumberOperator_eigenvalue
    {M : ℕ} (n : LiouvilleOccupation M) :
    (∑ a : LiouvilleMode M, n a) = totalOccupation n :=
  rfl

/-- The number operator written with the paper's double index notation. -/
def liouvilleNumberOperatorPairSum {M : ℕ} (n : LiouvilleOccupation M) : ℕ :=
  ∑ p : Fin M, ∑ q : Fin M, n (p, q)

/-- The double-index number operator is the same finite sum as
`totalOccupation`. -/
theorem liouvilleNumberOperatorPairSum_eq_total
    {M : ℕ} (n : LiouvilleOccupation M) :
    liouvilleNumberOperatorPairSum n = totalOccupation n := by
  simp [liouvilleNumberOperatorPairSum, totalOccupation, LiouvilleMode,
    Fintype.sum_prod_type]

/-- Eq. (13) on a fixed-`N` sector:
`∑_{p,q} n_{pq} = N`. -/
theorem fixedParticle_numberOperator_pair_sum
    {M N : ℕ} (n : FixedParticleLiouvilleOccupation M N) :
    liouvilleNumberOperatorPairSum n.1 = N := by
  rw [liouvilleNumberOperatorPairSum_eq_total]
  exact n.2

/-- Abstract occupation-basis inner product.  This is the finite Fock-basis
delta corresponding to the statement that `|{n_ij}⟩⟩` is orthonormal with
respect to Eq. (7). -/
def occupationBasisInner {M : ℕ}
    (n m : LiouvilleOccupation M) : ℂ :=
  if n = m then 1 else 0

@[simp] theorem occupationBasisInner_self
    {M : ℕ} (n : LiouvilleOccupation M) :
    occupationBasisInner n n = 1 := by
  simp [occupationBasisInner]

theorem occupationBasisInner_eq_zero_of_ne
    {M : ℕ} {n m : LiouvilleOccupation M} (h : n ≠ m) :
    occupationBasisInner n m = 0 := by
  simp [occupationBasisInner, h]

/-! ## Section II D: occupation-basis creation and annihilation -/

/-- The vacuum occupation register. -/
def vacuumOccupation (M : ℕ) : LiouvilleOccupation M :=
  fun _ => 0

/-- The vacuum has zero total occupation. -/
theorem totalOccupation_vacuum (M : ℕ) :
    totalOccupation (vacuumOccupation M) = 0 := by
  simp [totalOccupation, vacuumOccupation]

/-- The vacuum as the fixed-`0` particle sector. -/
def vacuumFixedParticleOccupation (M : ℕ) :
    FixedParticleLiouvilleOccupation M 0 :=
  ⟨vacuumOccupation M, totalOccupation_vacuum M⟩

/-- Occupation obtained after creating one quantum in mode `a`. -/
def raiseOccupation {M : ℕ} (a : LiouvilleMode M)
    (n : LiouvilleOccupation M) : LiouvilleOccupation M :=
  Function.update n a (n a + 1)

/-- Occupation obtained after annihilating one quantum in mode `a`
using natural-number subtraction. -/
def lowerOccupation {M : ℕ} (a : LiouvilleMode M)
    (n : LiouvilleOccupation M) : LiouvilleOccupation M :=
  Function.update n a (n a - 1)

@[simp] theorem raiseOccupation_self
    {M : ℕ} (a : LiouvilleMode M) (n : LiouvilleOccupation M) :
    raiseOccupation a n a = n a + 1 := by
  simp [raiseOccupation]

@[simp] theorem raiseOccupation_of_ne
    {M : ℕ} {a b : LiouvilleMode M} (h : b ≠ a)
    (n : LiouvilleOccupation M) :
    raiseOccupation a n b = n b := by
  simp [raiseOccupation, Function.update_of_ne h]

@[simp] theorem lowerOccupation_self
    {M : ℕ} (a : LiouvilleMode M) (n : LiouvilleOccupation M) :
    lowerOccupation a n a = n a - 1 := by
  simp [lowerOccupation]

@[simp] theorem lowerOccupation_of_ne
    {M : ℕ} {a b : LiouvilleMode M} (h : b ≠ a)
    (n : LiouvilleOccupation M) :
    lowerOccupation a n b = n b := by
  simp [lowerOccupation, Function.update_of_ne h]

/-- Creation raises the total occupation by one. -/
theorem totalOccupation_raise
    {M : ℕ} (a : LiouvilleMode M) (n : LiouvilleOccupation M) :
    totalOccupation (raiseOccupation a n) = totalOccupation n + 1 := by
  unfold totalOccupation raiseOccupation
  rw [Finset.sum_update_of_mem (s := Finset.univ) (i := a)
      (Finset.mem_univ a)]
  have hsame :
      (∑ x : LiouvilleMode M, n x)
        = n a + ∑ x ∈ Finset.univ \ {a}, n x := by
    rw [← Finset.sum_update_of_mem (s := Finset.univ) (i := a)
      (Finset.mem_univ a) n (n a)]
    simp [Function.update_eq_self]
  rw [hsame]
  omega

/-- Annihilation lowers the total occupation by one, when the selected mode is
occupied.  This is stated in additive form to avoid ambiguity from truncated
natural subtraction. -/
theorem totalOccupation_lower_add_one
    {M : ℕ} (a : LiouvilleMode M) (n : LiouvilleOccupation M)
    (hpos : 0 < n a) :
    totalOccupation (lowerOccupation a n) + 1 = totalOccupation n := by
  unfold totalOccupation lowerOccupation
  rw [Finset.sum_update_of_mem (s := Finset.univ) (i := a)
      (Finset.mem_univ a)]
  have hsame :
      (∑ x : LiouvilleMode M, n x)
        = n a + ∑ x ∈ Finset.univ \ {a}, n x := by
    rw [← Finset.sum_update_of_mem (s := Finset.univ) (i := a)
      (Finset.mem_univ a) n (n a)]
    simp [Function.update_eq_self]
  rw [hsame]
  omega

/-- Move one Liouville quantum from `annihilator` to `creator`, the occupation
register version of a bilinear `b†_creator b_annihilator`. -/
def transferOccupation {M : ℕ} (creator annihilator : LiouvilleMode M)
    (n : LiouvilleOccupation M) : LiouvilleOccupation M :=
  raiseOccupation creator (lowerOccupation annihilator n)

/-- A bilinear `b† b` conserves the total particle number whenever the
annihilated mode is occupied. -/
theorem totalOccupation_transfer
    {M : ℕ} (creator annihilator : LiouvilleMode M)
    (n : LiouvilleOccupation M) (hpos : 0 < n annihilator) :
    totalOccupation (transferOccupation creator annihilator n) =
      totalOccupation n := by
  unfold transferOccupation
  rw [totalOccupation_raise]
  exact totalOccupation_lower_add_one annihilator n hpos

/-- The annihilation amplitude in the occupation basis: `√n_a`. -/
noncomputable def annihilationAmplitude {M : ℕ}
    (n : LiouvilleOccupation M) (a : LiouvilleMode M) : ℝ :=
  Real.sqrt ((n a : ℕ) : ℝ)

/-- The creation amplitude in the occupation basis: `√(n_a + 1)`. -/
noncomputable def creationAmplitude {M : ℕ}
    (n : LiouvilleOccupation M) (a : LiouvilleMode M) : ℝ :=
  Real.sqrt (((n a + 1 : ℕ) : ℝ))

/-- Squaring the annihilation amplitude gives the occupation number. -/
theorem annihilationAmplitude_sq
    {M : ℕ} (n : LiouvilleOccupation M) (a : LiouvilleMode M) :
    annihilationAmplitude n a ^ 2 = ((n a : ℕ) : ℝ) := by
  rw [annihilationAmplitude, Real.sq_sqrt]
  exact_mod_cast Nat.zero_le (n a)

/-- Squaring the creation amplitude gives `n_a + 1`. -/
theorem creationAmplitude_sq
    {M : ℕ} (n : LiouvilleOccupation M) (a : LiouvilleMode M) :
    creationAmplitude n a ^ 2 = (((n a + 1 : ℕ) : ℝ)) := by
  rw [creationAmplitude, Real.sq_sqrt]
  exact_mod_cast Nat.zero_le (n a + 1)

/-! ## Transpose, Hermiticity, and trace support -/

/-- Transpose of a Liouville mode: `|ij⟩⟩ ↦ |ji⟩⟩`. -/
def transposeMode {M : ℕ} (a : LiouvilleMode M) : LiouvilleMode M :=
  (a.2, a.1)

/-- Mode transposition is involutive. -/
theorem transposeMode_involutive {M : ℕ} :
    Function.Involutive (@transposeMode M) := by
  intro a
  cases a
  rfl

/-- Transpose an occupation register by swapping all Liouville mode indices. -/
def transposeOccupation {M : ℕ} (n : LiouvilleOccupation M) :
    LiouvilleOccupation M :=
  fun a => n (transposeMode a)

/-- Occupation transposition is involutive. -/
theorem transposeOccupation_involutive {M : ℕ}
    (n : LiouvilleOccupation M) :
    transposeOccupation (transposeOccupation n) = n := by
  funext a
  cases a
  rfl

/-- Occupation-level Hermiticity condition for Liouville coefficients:
`ρ({n_ij}) = conj (ρ({n_ji}))`, equivalently `ρ(transpose n) = star (ρ n)`.
-/
def HermitianOccupationCoefficients {M : ℕ}
    (ρ : LiouvilleOccupation M → ℂ) : Prop :=
  ∀ n, ρ (transposeOccupation n) = star (ρ n)

/-- Hermiticity plus involutivity gives the reverse conjugation identity. -/
theorem hermitianOccupationCoefficients_star_transpose
    {M : ℕ} {ρ : LiouvilleOccupation M → ℂ}
    (hρ : HermitianOccupationCoefficients ρ)
    (n : LiouvilleOccupation M) :
    star (ρ (transposeOccupation n)) = ρ n := by
  have h := hρ (transposeOccupation n)
  simpa [transposeOccupation_involutive n] using h.symm

/-- A register has support only on diagonal Liouville modes `|ii⟩⟩`.  In the
paper's trace formula, only these diagonal modes contribute to the trace. -/
def HasOnlyDiagonalOccupation {M : ℕ} (n : LiouvilleOccupation M) : Prop :=
  ∀ a : LiouvilleMode M, a.1 ≠ a.2 → n a = 0

/-- Diagonal trace-support is invariant under occupation transposition. -/
theorem hasOnlyDiagonalOccupation_transpose_iff
    {M : ℕ} (n : LiouvilleOccupation M) :
    HasOnlyDiagonalOccupation (transposeOccupation n) ↔
      HasOnlyDiagonalOccupation n := by
  constructor
  · intro h a hne
    rcases a with ⟨i, j⟩
    have hne' : j ≠ i := by
      intro hji
      exact hne hji.symm
    simpa [HasOnlyDiagonalOccupation, transposeOccupation, transposeMode]
      using h (j, i) hne'
  · intro h a hne
    rcases a with ⟨i, j⟩
    have hne' : j ≠ i := by
      intro hji
      exact hne hji.symm
    simpa [HasOnlyDiagonalOccupation, transposeOccupation, transposeMode]
      using h (j, i) hne'

/-- Product of diagonal occupation factorials in Eq. (12). -/
def diagonalOccupationFactorialProduct {M : ℕ}
    (n : LiouvilleOccupation M) : ℕ :=
  ∏ q : Fin M, (n (q, q)).factorial

/-- Diagonal trace weight in Eq. (12):
`sqrt(N! / ∏_q n_qq!)`. -/
noncomputable def diagonalTraceWeight {M : ℕ} (N : ℕ)
    (n : LiouvilleOccupation M) : ℝ :=
  Real.sqrt (((N.factorial : ℕ) : ℝ) /
    ((diagonalOccupationFactorialProduct n : ℕ) : ℝ))

/-- The Liouville-Hilbert trace amplitude for an occupation basis vector:
zero off the diagonal-support sector, and Eq. (12) on it. -/
noncomputable def occupationTraceAmplitude {M : ℕ} (N : ℕ)
    (n : LiouvilleOccupation M) : ℝ :=
  by
    classical
    exact if HasOnlyDiagonalOccupation n then diagonalTraceWeight N n else 0

/-- Off-diagonal Liouville occupations have zero trace. -/
theorem occupationTraceAmplitude_zero_of_not_diagonal
    {M : ℕ} {N : ℕ} {n : LiouvilleOccupation M}
    (h : ¬ HasOnlyDiagonalOccupation n) :
    occupationTraceAmplitude N n = 0 := by
  unfold occupationTraceAmplitude
  classical
  simp [h]

/-- On diagonal-support occupations, the trace amplitude is Eq. (12). -/
theorem occupationTraceAmplitude_eq_diagonalTraceWeight
    {M : ℕ} {N : ℕ} {n : LiouvilleOccupation M}
    (h : HasOnlyDiagonalOccupation n) :
    occupationTraceAmplitude N n = diagonalTraceWeight N n := by
  unfold occupationTraceAmplitude
  classical
  simp [h]

/-- The diagonal trace weight is nonnegative. -/
theorem diagonalTraceWeight_nonneg
    {M : ℕ} (N : ℕ) (n : LiouvilleOccupation M) :
    0 ≤ diagonalTraceWeight N n :=
  Real.sqrt_nonneg _

/-! ## Paper equations (8)--(10): left, right, and sandwich modes -/

/-- Mode pair appearing in the collective left action
`∑_μ σ_{μ,pq} ρ = ∑_t b†_{pt} b_{qt} |ρ⟩⟩`.  The first component is the
created mode and the second component is the annihilated mode. -/
def leftCollectiveBosonizationModes {M : ℕ} (p q t : Fin M) :
    LiouvilleMode M × LiouvilleMode M :=
  ((p, t), (q, t))

/-- The Eq. (8) summand is exactly the nonzero left action
`|qt⟩⟩ ↦ |pt⟩⟩`. -/
theorem leftActionMode_eq_collectiveLeftBosonizationModes
    {M : ℕ} (p q t : Fin M) :
    leftActionMode p q (leftCollectiveBosonizationModes p q t).2 =
      some (leftCollectiveBosonizationModes p q t).1 := by
  simp [leftCollectiveBosonizationModes]

/-- Mode pair appearing in the collective right action
`∑_μ σᵀ_{μ,kℓ} ρ = ∑_s b†_{sℓ} b_{sk} |ρ⟩⟩`. -/
def rightCollectiveBosonizationModes {M : ℕ} (k ℓ s : Fin M) :
    LiouvilleMode M × LiouvilleMode M :=
  ((s, ℓ), (s, k))

/-- The Eq. (9) summand is exactly the nonzero right action
`|sk⟩⟩ ↦ |sℓ⟩⟩`. -/
theorem rightActionMode_eq_collectiveRightBosonizationModes
    {M : ℕ} (k ℓ s : Fin M) :
    rightActionMode k ℓ (rightCollectiveBosonizationModes k ℓ s).2 =
      some (rightCollectiveBosonizationModes k ℓ s).1 := by
  simp [rightCollectiveBosonizationModes]

/-- Mode pair for the independent-reservoir one-particle left/right term
`Γ^{pq}_{kℓ} = ∑_μ σ_{μ,pq} σᵀ_{μ,kℓ} = b†_{pℓ} b_{qk}`. -/
def independentReservoirBosonizationModes {M : ℕ}
    (p q k ℓ : Fin M) : LiouvilleMode M × LiouvilleMode M :=
  ((p, ℓ), (q, k))

/-- The Eq. (10) summand is exactly the nonzero sandwich action
`|qk⟩⟩ ↦ |pℓ⟩⟩`. -/
theorem sandwichActionMode_eq_independentReservoirBosonizationModes
    {M : ℕ} (p q k ℓ : Fin M) :
    sandwichActionMode p q k ℓ
        (independentReservoirBosonizationModes p q k ℓ).2 =
      some (independentReservoirBosonizationModes p q k ℓ).1 := by
  simp [independentReservoirBosonizationModes]

/-- The independent-reservoir term is exactly the `b†_{pℓ} b_{qk}` mode pair. -/
theorem independentReservoirBosonizationModes_eq
    {M : ℕ} (p q k ℓ : Fin M) :
    independentReservoirBosonizationModes p q k ℓ = ((p, ℓ), (q, k)) :=
  rfl

/-- Four-mode monomial appearing in the two-particle bosonized operator
Eq. (11): two created Liouville modes followed by two annihilated modes. -/
structure TwoParticleBosonMonomial (M : ℕ) where
  /-- First created Liouville mode. -/
  creator₁ : LiouvilleMode M
  /-- Second created Liouville mode. -/
  creator₂ : LiouvilleMode M
  /-- First annihilated Liouville mode. -/
  annihilator₁ : LiouvilleMode M
  /-- Second annihilated Liouville mode. -/
  annihilator₂ : LiouvilleMode M
deriving DecidableEq

/-- Mode pattern of the two-particle invariant operator in Eq. (11). -/
def twoParticleBosonizationMonomial {M : ℕ}
    (s₁ t₁ s₂ t₂ i₁ j₁ i₂ j₂ : Fin M) :
    TwoParticleBosonMonomial M where
  creator₁ := (s₁, t₁)
  creator₂ := (s₂, t₂)
  annihilator₁ := (i₂, j₂)
  annihilator₂ := (i₁, j₁)

/-- Eq. (11) creates `(s₁,t₁),(s₂,t₂)` and annihilates
`(i₂,j₂),(i₁,j₁)` in that order. -/
theorem twoParticleBosonizationMonomial_components
    {M : ℕ} (s₁ t₁ s₂ t₂ i₁ j₁ i₂ j₂ : Fin M) :
    let mono :=
      twoParticleBosonizationMonomial s₁ t₁ s₂ t₂ i₁ j₁ i₂ j₂
    mono.creator₁ = (s₁, t₁)
      ∧ mono.creator₂ = (s₂, t₂)
      ∧ mono.annihilator₁ = (i₂, j₂)
      ∧ mono.annihilator₂ = (i₁, j₁) := by
  simp [twoParticleBosonizationMonomial]

/-- Occupation-register action of the Eq. (11) monomial
`b†_{s₁t₁} b†_{s₂t₂} b_{i₂j₂} b_{i₁j₁}`.  Operators act from right to
left, so `annihilator₂` is applied before `annihilator₁`. -/
def twoParticleTransferOccupation {M : ℕ}
    (mono : TwoParticleBosonMonomial M)
    (n : LiouvilleOccupation M) : LiouvilleOccupation M :=
  raiseOccupation mono.creator₁
    (raiseOccupation mono.creator₂
      (lowerOccupation mono.annihilator₁
        (lowerOccupation mono.annihilator₂ n)))

/-- Eq. (11) preserves particle number: two occupied modes are annihilated and
two modes are created.  The second positivity hypothesis is stated after the
first annihilation, which correctly covers the case where both annihilators are
the same mode. -/
theorem totalOccupation_twoParticleTransfer
    {M : ℕ} (mono : TwoParticleBosonMonomial M)
    (n : LiouvilleOccupation M)
    (h₂ : 0 < n mono.annihilator₂)
    (h₁ : 0 < (lowerOccupation mono.annihilator₂ n) mono.annihilator₁) :
    totalOccupation (twoParticleTransferOccupation mono n) =
      totalOccupation n := by
  unfold twoParticleTransferOccupation
  rw [totalOccupation_raise, totalOccupation_raise]
  have hlow₁ :=
    totalOccupation_lower_add_one mono.annihilator₁
      (lowerOccupation mono.annihilator₂ n) h₁
  have hlow₂ :=
    totalOccupation_lower_add_one mono.annihilator₂ n h₂
  omega

/-! ## Section II D: Jordan-Schwinger `Γ` algebra -/

/-- Finite matrix model of a bosonic bilinear `b†_a b_b` on the mode-index
space. This gives a concrete representative for the Section II `Γ` commutator
algebra. -/
abbrev ModeMatrix (M : ℕ) : Type :=
  Matrix (LiouvilleMode M) (LiouvilleMode M) ℂ

/-- Matrix unit `E_ab`, representing the bilinear `b†_a b_b` on modes. -/
def modeMatrixUnit {M : ℕ} (a b : LiouvilleMode M) : ModeMatrix M :=
  Matrix.single a b 1

/-- Eq. (8): collective left action
`∑_μ σ_{μ,pq}` as the bosonized mode matrix
`∑_t b†_{pt} b_{qt}`. -/
def collectiveLeftBosonizationMatrix {M : ℕ} (p q : Fin M) :
    ModeMatrix M :=
  ∑ t : Fin M, modeMatrixUnit (p, t) (q, t)

/-- Eq. (9): collective right action
`∑_μ σᵀ_{μ,kℓ}` as the bosonized mode matrix
`∑_s b†_{sℓ} b_{sk}`. -/
def collectiveRightBosonizationMatrix {M : ℕ} (k ℓ : Fin M) :
    ModeMatrix M :=
  ∑ s : Fin M, modeMatrixUnit (s, ℓ) (s, k)

/-- Eq. (10): independent-reservoir left/right term
`Γ^{pq}_{kℓ} = b†_{pℓ} b_{qk}` as a mode matrix. -/
def independentReservoirBosonizationMatrix {M : ℕ}
    (p q k ℓ : Fin M) : ModeMatrix M :=
  modeMatrixUnit (p, ℓ) (q, k)

/-- The Eq. (8) mode pair is exactly the matrix unit summand in the collective
left bosonization matrix. -/
theorem collectiveLeftBosonizationMatrix_eq_sum
    {M : ℕ} (p q : Fin M) :
    collectiveLeftBosonizationMatrix p q =
      ∑ t : Fin M,
        modeMatrixUnit (leftCollectiveBosonizationModes p q t).1
          (leftCollectiveBosonizationModes p q t).2 :=
  rfl

/-- The Eq. (9) mode pair is exactly the matrix unit summand in the collective
right bosonization matrix. -/
theorem collectiveRightBosonizationMatrix_eq_sum
    {M : ℕ} (k ℓ : Fin M) :
    collectiveRightBosonizationMatrix k ℓ =
      ∑ s : Fin M,
        modeMatrixUnit (rightCollectiveBosonizationModes k ℓ s).1
          (rightCollectiveBosonizationModes k ℓ s).2 :=
  rfl

/-- The Eq. (10) independent-reservoir mode pair is exactly the `Γ` matrix unit. -/
theorem independentReservoirBosonizationMatrix_eq_modes
    {M : ℕ} (p q k ℓ : Fin M) :
    independentReservoirBosonizationMatrix p q k ℓ =
      modeMatrixUnit
        (independentReservoirBosonizationModes p q k ℓ).1
        (independentReservoirBosonizationModes p q k ℓ).2 :=
  rfl

/-- Multiplication rule for matrix units:
`E_ab E_cd = δ_bc E_ad`. -/
theorem modeMatrixUnit_mul
    {M : ℕ} (a b c d : LiouvilleMode M) :
    modeMatrixUnit a b * modeMatrixUnit c d =
      if b = c then modeMatrixUnit a d else 0 := by
  ext x y
  by_cases hbc : b = c
  · subst c
    by_cases hxa : x = a
    · subst x
      by_cases hyd : y = d
      · subst y
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single b]
        · simp [modeMatrixUnit]
        · intro z _ hz
          simp_all [modeMatrixUnit, Matrix.single_apply]
          try aesop
        · intro hbmem
          simp at hbmem
      · rw [Matrix.mul_apply]
        rw [Finset.sum_eq_zero]
        · simp_all [modeMatrixUnit, Matrix.single_apply]
          try aesop
        · intro z hz
          simp_all [modeMatrixUnit, Matrix.single_apply]
          try aesop
    · rw [Matrix.mul_apply]
      rw [Finset.sum_eq_zero]
      · simp_all [modeMatrixUnit, Matrix.single_apply]
        try aesop
      · intro z hz
        simp_all [modeMatrixUnit, Matrix.single_apply]
        try aesop
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_zero]
    · simp_all
    · intro z hz
      simp_all [modeMatrixUnit, Matrix.single_apply]
      try aesop

/-- Matrix commutator on the concrete mode matrix structure. -/
def modeMatrixCommutator {M : ℕ} (A B : ModeMatrix M) : ModeMatrix M :=
  A * B - B * A

/-- Jordan-Schwinger matrix-unit algebra:
`[E_ab,E_cd] = δ_bc E_ad - δ_da E_cb`. -/
theorem modeMatrixUnit_commutator
    {M : ℕ} (a b c d : LiouvilleMode M) :
    modeMatrixCommutator (modeMatrixUnit a b) (modeMatrixUnit c d)
      =
        (if b = c then modeMatrixUnit a d else 0)
          - (if d = a then modeMatrixUnit c b else 0) := by
  simp [modeMatrixCommutator, modeMatrixUnit_mul]

/-- Concrete matrix-unit representative of the paper's
`Γ^{pq}_{kℓ} = b†_{pℓ} b_{qk}`. -/
def gammaMatrix {M : ℕ} (p q k ℓ : Fin M) : ModeMatrix M :=
  modeMatrixUnit (p, ℓ) (q, k)

/-- The independent-reservoir mode pair and the concrete `Γ` matrix use the
same created/annihilated Liouville modes. -/
theorem gammaMatrix_eq_independentReservoir_modes
    {M : ℕ} (p q k ℓ : Fin M) :
    gammaMatrix p q k ℓ =
      modeMatrixUnit
        (independentReservoirBosonizationModes p q k ℓ).1
        (independentReservoirBosonizationModes p q k ℓ).2 :=
  rfl

/-- The concrete `Γ` matrix is the Eq. (10) independent-reservoir
bosonization matrix. -/
theorem gammaMatrix_eq_independentReservoirBosonizationMatrix
    {M : ℕ} (p q k ℓ : Fin M) :
    gammaMatrix p q k ℓ =
      independentReservoirBosonizationMatrix p q k ℓ :=
  rfl

/-- Concrete form of the Section II `Γ` commutator algebra, as the standard
matrix-unit/Jordan-Schwinger identity. -/
theorem gammaMatrix_commutator
    {M : ℕ} (p q k ℓ r s u v : Fin M) :
    modeMatrixCommutator (gammaMatrix p q k ℓ) (gammaMatrix r s u v)
      =
        (if (q, k) = (r, v) then modeMatrixUnit (p, ℓ) (s, u) else 0)
          - (if (s, u) = (p, ℓ) then modeMatrixUnit (r, v) (q, k) else 0) := by
  simpa [gammaMatrix] using
    (modeMatrixUnit_commutator (a := (p, ℓ)) (b := (q, k))
      (c := (r, v)) (d := (s, u)))

/-! ## Section III: second-quantization representation -/

/-! ### Section III A: density matrices in the occupation-number basis -/

/-- Finite bounded occupation registers for the fixed-`N` sector.  Because
every occupied mode in a fixed-`N` register has occupation at most `N`, this
finite structure gives the summation domain used in Section III. -/
abbrev BoundedLiouvilleOccupation (M N : ℕ) : Type :=
  LiouvilleMode M → Fin (N + 1)

/-- Total occupation for bounded registers. -/
def boundedTotalOccupation {M N : ℕ}
    (n : BoundedLiouvilleOccupation M N) : ℕ :=
  ∑ a : LiouvilleMode M, (n a).val

/-- Forget the bound and view a bounded register as a natural-valued
Liouville occupation. -/
def boundedToOccupation {M N : ℕ}
    (n : BoundedLiouvilleOccupation M N) : LiouvilleOccupation M :=
  fun a => (n a).val

/-- The fixed-`N` finite occupation representative for Section III sums. -/
def FixedBoundedLiouvilleOccupation (M N : ℕ) : Type :=
  {n : BoundedLiouvilleOccupation M N // boundedTotalOccupation n = N}

/-- The fixed bounded occupation structure is finite. -/
noncomputable instance fixedBoundedLiouvilleOccupationFintype (M N : ℕ) :
    Fintype (FixedBoundedLiouvilleOccupation M N) := by
  classical
  unfold FixedBoundedLiouvilleOccupation BoundedLiouvilleOccupation
  infer_instance

/-- Equality on the fixed bounded occupation structure is decidable. -/
noncomputable instance fixedBoundedLiouvilleOccupationDecidableEq (M N : ℕ) :
    DecidableEq (FixedBoundedLiouvilleOccupation M N) := by
  classical
  infer_instance

/-- Forgetting bounds preserves the total occupation equation. -/
def fixedBoundedToFixedParticle {M N : ℕ}
    (n : FixedBoundedLiouvilleOccupation M N) :
    FixedParticleLiouvilleOccupation M N :=
  ⟨boundedToOccupation n.1, by
    simpa [boundedToOccupation, boundedTotalOccupation, totalOccupation] using n.2⟩

/-- Product of all occupation factorials in Eq. (14). -/
def occupationFactorialProduct {M : ℕ}
    (n : LiouvilleOccupation M) : ℕ :=
  ∏ a : LiouvilleMode M, (n a).factorial

/-- Density-vector normalization weight in Eq. (14):
`sqrt(∏ n_pq! / N!)`. -/
noncomputable def densityExpansionWeight {M : ℕ} (N : ℕ)
    (n : LiouvilleOccupation M) : ℝ :=
  Real.sqrt (((occupationFactorialProduct n : ℕ) : ℝ) /
    ((N.factorial : ℕ) : ℝ))

/-- Observable-vector normalization weight, inverse to the density convention
used in Section III B: `sqrt(N! / ∏ n_pq!)`. -/
noncomputable def observableExpansionWeight {M : ℕ} (N : ℕ)
    (n : LiouvilleOccupation M) : ℝ :=
  Real.sqrt (((N.factorial : ℕ) : ℝ) /
    ((occupationFactorialProduct n : ℕ) : ℝ))

/-- The coefficient appearing in the density expansion Eq. (14), including the
paper's multinomial square-root factor. -/
noncomputable def densityExpansionCoefficient {M : ℕ} (N : ℕ)
    (ρ : LiouvilleOccupation M → ℂ) (n : LiouvilleOccupation M) : ℂ :=
  (densityExpansionWeight N n : ℂ) * ρ n

/-- Density coefficients are supported on the fixed-`N` sector. -/
def SupportedOnFixedParticleNumber {M : ℕ} (N : ℕ)
    (ρ : LiouvilleOccupation M → ℂ) : Prop :=
  ∀ n : LiouvilleOccupation M, totalOccupation n ≠ N → ρ n = 0

/-- If a density coefficient is outside the fixed-particle sector, its
Eq. (14) expansion coefficient is zero. -/
theorem densityExpansionCoefficient_zero_of_not_fixed
    {M N : ℕ} {ρ : LiouvilleOccupation M → ℂ}
    (hρ : SupportedOnFixedParticleNumber N ρ)
    {n : LiouvilleOccupation M} (hn : totalOccupation n ≠ N) :
    densityExpansionCoefficient N ρ n = 0 := by
  simp [densityExpansionCoefficient, hρ n hn]

/-- Finite trace sum over the diagonal fixed-`N` occupation sector.  This is
the Section III A trace formula after the Eq. (14) normalization cancels the
Eq. (12) trace weight. -/
noncomputable def traceDiagonalCoefficientSum (M N : ℕ)
    (ρ : LiouvilleOccupation M → ℂ) : ℂ :=
  by
    classical
    exact
      ∑ n : FixedBoundedLiouvilleOccupation M N,
        if HasOnlyDiagonalOccupation (boundedToOccupation n.1) then
          ρ (boundedToOccupation n.1)
        else
          0

/-- Trace-one predicate for Section III density coefficients:
`∑_{n_i≠j=0} ρ({n_ij}) = 1`. -/
def TraceOneDensityCoefficients (M N : ℕ)
    (ρ : LiouvilleOccupation M → ℂ) : Prop :=
  traceDiagonalCoefficientSum M N ρ = 1

/-- Single summand in the diagonal trace sum. -/
noncomputable def traceDiagonalContribution
    {M N : ℕ} (ρ : LiouvilleOccupation M → ℂ)
    (n : FixedBoundedLiouvilleOccupation M N) : ℂ :=
  by
    classical
    exact
      if HasOnlyDiagonalOccupation (boundedToOccupation n.1) then
        ρ (boundedToOccupation n.1)
      else
        0

/-- If a fixed bounded register is diagonal, its trace contribution is its
density coefficient. -/
theorem traceDiagonalContribution_eq_coeff
    {M N : ℕ} (ρ : LiouvilleOccupation M → ℂ)
    (n : FixedBoundedLiouvilleOccupation M N)
    (hn : HasOnlyDiagonalOccupation (boundedToOccupation n.1)) :
    traceDiagonalContribution ρ n = ρ (boundedToOccupation n.1) := by
  unfold traceDiagonalContribution
  classical
  simp [hn]

/-- If a fixed bounded register has an off-diagonal occupation, its trace
contribution is zero. -/
theorem traceDiagonalContribution_eq_zero
    {M N : ℕ} (ρ : LiouvilleOccupation M → ℂ)
    (n : FixedBoundedLiouvilleOccupation M N)
    (hn : ¬ HasOnlyDiagonalOccupation (boundedToOccupation n.1)) :
    traceDiagonalContribution ρ n = 0 := by
  unfold traceDiagonalContribution
  classical
  simp [hn]

/-! ### Section III B: observables and expectation values -/

/-- Occupation-basis observable coefficients. -/
abbrev ObservableCoefficients (M : ℕ) : Type :=
  LiouvilleOccupation M → ℂ

/-- The coefficient appearing in the observable supervector expansion in
Section III B, including the inverse multinomial square-root factor. -/
noncomputable def observableExpansionCoefficient {M : ℕ} (N : ℕ)
    (O : ObservableCoefficients M) (n : LiouvilleOccupation M) : ℂ :=
  (observableExpansionWeight N n : ℂ) * O n

/-- Section III expectation-value formula, Eq. (15):
`⟨O⟩ = ∑_n ρ({n_ji}) O({n_ij})`. -/
noncomputable def occupationExpectation (M N : ℕ)
    (ρ : LiouvilleOccupation M → ℂ) (O : ObservableCoefficients M) : ℂ :=
  ∑ n : FixedBoundedLiouvilleOccupation M N,
    ρ (transposeOccupation (boundedToOccupation n.1)) *
      O (boundedToOccupation n.1)

/-- Eq. (15) is exactly the finite fixed-`N` occupation sum. -/
theorem occupationExpectation_eq_paper_formula
    {M N : ℕ} (ρ : LiouvilleOccupation M → ℂ)
    (O : ObservableCoefficients M) :
    occupationExpectation M N ρ O =
      ∑ n : FixedBoundedLiouvilleOccupation M N,
        ρ (transposeOccupation (boundedToOccupation n.1)) *
          O (boundedToOccupation n.1) :=
  rfl

/-- For Hermitian density coefficients, the transposed coefficient in
Eq. (15) is the Hilbert-Schmidt conjugate coefficient. -/
theorem occupationExpectation_eq_conjugate_coefficients
    {M N : ℕ} {ρ : LiouvilleOccupation M → ℂ}
    (hρ : HermitianOccupationCoefficients ρ)
    (O : ObservableCoefficients M) :
    occupationExpectation M N ρ O =
      ∑ n : FixedBoundedLiouvilleOccupation M N,
        star (ρ (boundedToOccupation n.1)) * O (boundedToOccupation n.1) := by
  unfold occupationExpectation
  apply Finset.sum_congr rfl
  intro n _
  rw [hρ]

/-- Section III generating function, Eq. (17):
`F_n(λ) = ∏_{p,q} λ_pq^{n_pq}`. -/
noncomputable def occupationGeneratingFunction {M : ℕ}
    (n : LiouvilleOccupation M) (lam : LiouvilleMode M → ℂ) : ℂ :=
  ∏ a : LiouvilleMode M, lam a ^ n a

/-- The diagonal evaluation point `λ_pq = δ_pq`. -/
def diagonalGeneratingPoint {M : ℕ} (a : LiouvilleMode M) : ℂ :=
  finDelta a.1 a.2

/-- If only diagonal modes are occupied, the generating function evaluated at
`λ_pq = δ_pq` is one. -/
theorem occupationGeneratingFunction_at_diagonal_of_diagonal_support
    {M : ℕ} {n : LiouvilleOccupation M}
    (hn : HasOnlyDiagonalOccupation n) :
    occupationGeneratingFunction n diagonalGeneratingPoint = 1 := by
  unfold occupationGeneratingFunction
  apply Finset.prod_eq_one
  intro a _
  by_cases hdiag : a.1 = a.2
  · simp [diagonalGeneratingPoint, finDelta, hdiag]
  · have hzero : n a = 0 := hn a hdiag
    simp [diagonalGeneratingPoint, finDelta, hdiag, hzero]

/-- If an off-diagonal mode is occupied, the generating function vanishes at
the diagonal evaluation point. -/
theorem occupationGeneratingFunction_at_diagonal_zero_of_offdiag
    {M : ℕ} {n : LiouvilleOccupation M} {a : LiouvilleMode M}
  (hoff : a.1 ≠ a.2) (hpos : 0 < n a) :
    occupationGeneratingFunction n diagonalGeneratingPoint = 0 := by
  unfold occupationGeneratingFunction
  apply Finset.prod_eq_zero (i := a)
  · simp
  · simp [diagonalGeneratingPoint, finDelta, hoff, Nat.pos_iff_ne_zero.mp hpos]

/-- Falling factorial `n(n-1)...(n-k+1)`, the coefficient produced by `k`
ordinary derivatives of `x^n`. -/
def fallingFactorial : ℕ → ℕ → ℕ
  | _, 0 => 1
  | n, k + 1 => n * fallingFactorial (n - 1) k

@[simp] theorem fallingFactorial_zero (n : ℕ) :
    fallingFactorial n 0 = 1 :=
  rfl

/-- Multiplicity of a mode among the `K` differentiated variables in Eq. (18). -/
def modeMultiplicity {M K : ℕ} (α : Fin K → LiouvilleMode M)
    (a : LiouvilleMode M) : ℕ :=
  ∑ k : Fin K, if α k = a then 1 else 0

/-- Formal value of
`∂^K F / ∂λ_{α₁}...∂λ_{αK}` at `λ_pq = δ_pq`, computed from the monomial
generating function. -/
noncomputable def formalGeneratingDerivativeAtDiagonal
    {M K : ℕ} (n : LiouvilleOccupation M)
    (α : Fin K → LiouvilleMode M) : ℂ :=
  ∏ a : LiouvilleMode M,
    ((fallingFactorial (n a) (modeMultiplicity α a) : ℕ) : ℂ) *
      diagonalGeneratingPoint a ^ (n a - modeMultiplicity α a)

/-- Matrix elements of a `K`-particle permutation-invariant operator after
writing each `(i_r,j_r)` as a Liouville mode. -/
abbrev KParticleOperatorMatrixElements (M K : ℕ) : Type :=
  (Fin K → LiouvilleMode M) → ℂ

/-- Section III Eq. (18): components of a `K`-particle operator are obtained
by summing matrix elements against the formal derivatives of the generating
function. -/
noncomputable def kParticleOperatorComponent {M K : ℕ}
    (O : KParticleOperatorMatrixElements M K)
    (n : LiouvilleOccupation M) : ℂ :=
  ∑ α : Fin K → LiouvilleMode M,
    O α * formalGeneratingDerivativeAtDiagonal n α

/-- Eq. (18) in finite Liouville-mode notation. -/
theorem kParticleOperatorComponent_eq_derivative_sum
    {M K : ℕ} (O : KParticleOperatorMatrixElements M K)
    (n : LiouvilleOccupation M) :
    kParticleOperatorComponent O n =
      ∑ α : Fin K → LiouvilleMode M,
        O α * formalGeneratingDerivativeAtDiagonal n α :=
  rfl

/-! ### Section III C: Liouville master equation -/

/-- Finite fixed-`N` occupation index used for coefficient-space dynamics. -/
abbrev FixedOccupationIndex (M N : ℕ) : Type :=
  FixedBoundedLiouvilleOccupation M N

/-- A finite vector of occupation coefficients. -/
abbrev OccupationVector (M N : ℕ) : Type :=
  FixedOccupationIndex M N → ℂ

/-- A finite matrix acting on occupation coefficients. -/
abbrev OccupationMatrix (M N : ℕ) : Type :=
  Matrix (FixedOccupationIndex M N) (FixedOccupationIndex M N) ℂ

/-- Matrix-vector action on occupation coefficients. -/
def occupationMatrixVecMul {M N : ℕ}
    (L : OccupationMatrix M N) (ρ : OccupationVector M N) :
    OccupationVector M N :=
  fun n => ∑ m : FixedOccupationIndex M N, L n m * ρ m

/-- Finite coefficient form of `dρ/dt = Lρ`. -/
def IsOccupationMasterEquation {M N : ℕ}
    (L : ℝ → OccupationMatrix M N)
    (ρ ρdot : ℝ → OccupationVector M N) : Prop :=
  ∀ t : ℝ, ρdot t = occupationMatrixVecMul (L t) (ρ t)

/-- The zero coefficient trajectory solves any homogeneous finite master
equation. -/
theorem zero_isOccupationMasterEquation
    {M N : ℕ} (L : ℝ → OccupationMatrix M N) :
    IsOccupationMasterEquation L (fun _ => 0) (fun _ => 0) := by
  intro t
  funext n
  simp [occupationMatrixVecMul]

/-- Section III Eq. (19): `L = (i/ℏ)(Hᵀ - H) + D`, represented on the finite
occupation coefficient space. -/
def occupationLiouvillianFromHamiltonianDissipator {M N : ℕ}
    (H Hright D : OccupationMatrix M N) (ℏ : ℝ) : OccupationMatrix M N :=
  (Complex.I / (ℏ : ℂ)) • (Hright - H) + D

/-- Eq. (19) as a definitional equality. -/
theorem occupationLiouvillianFromHamiltonianDissipator_eq
    {M N : ℕ} (H Hright D : OccupationMatrix M N) (ℏ : ℝ) :
    occupationLiouvillianFromHamiltonianDissipator H Hright D ℏ =
      (Complex.I / (ℏ : ℂ)) • (Hright - H) + D :=
  rfl

/-- The Section III generic Lindblad dissipator written in the bosonized
mode-matrix notation:
`Σ Γ_ijpq (b†_ip b_jq - δ_ip/2 Σ_t (b†_qt b_jt + b†_tj b_tq))`. -/
def sectionIIIDissipatorModeMatrix {M : ℕ}
    (Γ : Fin M → Fin M → Fin M → Fin M → ℂ) : ModeMatrix M :=
  ∑ i : Fin M, ∑ j : Fin M, ∑ p : Fin M, ∑ q : Fin M,
    Γ i j p q •
      (modeMatrixUnit (i, p) (j, q)
        - ((finDelta i p / (2 : ℂ)) •
            ∑ t : Fin M,
              (modeMatrixUnit (q, t) (j, t)
                + modeMatrixUnit (t, j) (t, q))))

/-- The bosonized dissipator is exactly the Section III finite mode-matrix
sum. -/
theorem sectionIIIDissipatorModeMatrix_eq_sum
    {M : ℕ} (Γ : Fin M → Fin M → Fin M → Fin M → ℂ) :
    sectionIIIDissipatorModeMatrix Γ =
      ∑ i : Fin M, ∑ j : Fin M, ∑ p : Fin M, ∑ q : Fin M,
        Γ i j p q •
          (modeMatrixUnit (i, p) (j, q)
            - ((finDelta i p / (2 : ℂ)) •
                ∑ t : Fin M,
                  (modeMatrixUnit (q, t) (j, t)
                    + modeMatrixUnit (t, j) (t, q)))) :=
  rfl

/-! ### Section III D: two-time correlation functions -/

/-- Bilinear pairing of a Liouville-space bra coefficient vector with a ket
coefficient vector. -/
noncomputable def occupationPairing {M N : ℕ}
    (bra ket : OccupationVector M N) : ℂ :=
  ∑ n : FixedOccupationIndex M N, bra n * ket n

/-- Finite occupation-space version of
`X(t,τ) = ⟪A(τ)| B |ρ(t)⟫`. -/
noncomputable def twoTimeCorrelation {M N : ℕ}
    (Aτ : OccupationVector M N) (B : OccupationMatrix M N)
    (ρt : OccupationVector M N) : ℂ :=
  occupationPairing Aτ (occupationMatrixVecMul B ρt)

/-- The two-time correlation is the pairing of the evolved bra with the
operator-applied density vector. -/
theorem twoTimeCorrelation_eq_pairing
    {M N : ℕ} (Aτ : OccupationVector M N) (B : OccupationMatrix M N)
    (ρt : OccupationVector M N) :
    twoTimeCorrelation Aτ B ρt =
      occupationPairing Aτ (occupationMatrixVecMul B ρt) :=
  rfl

/-- Finite evolution-operator equation `dU/dt = L U`, `U(0)=1`. -/
def IsOccupationEvolutionOperator {M N : ℕ}
    (L : ℝ → OccupationMatrix M N)
    (U Udot : ℝ → OccupationMatrix M N) : Prop :=
  (∀ t : ℝ, Udot t = L t * U t) ∧ U 0 = 1

/-- Finite adjoint master equation for the time-dependent observable bra in
Eq. (21). -/
def IsAdjointOccupationMasterEquation {M N : ℕ}
    (Ldag : ℝ → OccupationMatrix M N)
    (A Adot : ℝ → OccupationVector M N) : Prop :=
  ∀ τ : ℝ, Adot τ = occupationMatrixVecMul (Ldag τ) (A τ)

/-- The zero observable bra solves the homogeneous adjoint master equation. -/
theorem zero_isAdjointOccupationMasterEquation
    {M N : ℕ} (Ldag : ℝ → OccupationMatrix M N) :
    IsAdjointOccupationMasterEquation Ldag (fun _ => 0) (fun _ => 0) := by
  intro τ
  funext n
  simp [occupationMatrixVecMul]

/-! ## Liouville matrix superoperators and GKLS linkage -/

variable {d ι : Type*} [Fintype d] [Fintype ι]

section HilbertSchmidt

variable [DecidableEq d]

/-- Paper Eq. (7), reusing the repo's finite-matrix Hilbert-Schmidt inner
product `Tr(AᴴB)`. -/
abbrev liouvilleInnerProduct (A B : Matrix d d ℂ) : ℂ :=
  matrixHSInner A B

/-- The Liouville inner product is the Hilbert-Schmidt trace `Tr(AᴴB)`. -/
theorem liouvilleInnerProduct_eq_trace_conjTranspose_mul
    (A B : Matrix d d ℂ) :
    liouvilleInnerProduct A B = (Aᴴ * B).trace :=
  rfl

end HilbertSchmidt

/-- Left multiplication superoperator `ρ ↦ Aρ`. -/
def leftMultiplication (A : Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    Matrix d d ℂ :=
  A * ρ

/-- Right multiplication superoperator `ρ ↦ ρA`. -/
def rightMultiplication (A : Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    Matrix d d ℂ :=
  ρ * A

/-- Sandwich multiplication `ρ ↦ LρR`, the matrix version of the paper's
one-particle left/right Liouville action. -/
def sandwichMultiplication (L R : Matrix d d ℂ) (ρ : Matrix d d ℂ) :
    Matrix d d ℂ :=
  L * ρ * R

/-- The commutator is left multiplication minus right multiplication. -/
theorem commutator_eq_left_sub_right
    (A ρ : Matrix d d ℂ) :
    commutator A ρ = leftMultiplication A ρ - rightMultiplication A ρ :=
  rfl

/-- The anticommutator is left multiplication plus right multiplication. -/
theorem anticommutator_eq_left_add_right
    (A ρ : Matrix d d ℂ) :
    anticommutator A ρ = leftMultiplication A ρ + rightMultiplication A ρ :=
  rfl

/-- Single-jump Lindblad dissipator decomposed into Liouville sandwich,
left-multiplication, and right-multiplication superoperators. -/
theorem lindbladSingleJumpDissipator_eq_left_right
    (L ρ : Matrix d d ℂ) :
    lindbladSingleJumpDissipator L ρ =
      sandwichMultiplication L Lᴴ ρ
        - ((1 / 2 : ℂ) •
            (leftMultiplication (Lᴴ * L) ρ
              + rightMultiplication (Lᴴ * L) ρ)) := by
  rfl

/-- Full finite GKLS generator written as a Liouville-space left/right
superoperator decomposition. -/
theorem gklsGenerator_eq_left_right
    (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ)
    (ρ : Matrix d d ℂ) :
    gklsGenerator H L_fn ℏ ρ =
      -(Complex.I / (ℏ : ℂ)) •
          (leftMultiplication H ρ - rightMultiplication H ρ)
        + ∑ j : ι,
            (sandwichMultiplication (L_fn j) (L_fn j)ᴴ ρ
              - ((1 / 2 : ℂ) •
                  (leftMultiplication ((L_fn j)ᴴ * L_fn j) ρ
                    + rightMultiplication ((L_fn j)ᴴ * L_fn j) ρ))) := by
  rfl

section DirectMatrixGKLS

variable [DecidableEq d]

/-- The second-quantized finite Liouville GKLS generator, as a direct matrix
Liouville superoperator. -/
def liouvilleSecondQuantizedGKLS
    (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ) :
    MatrixLiouvilleKet d → MatrixLiouvilleKet d :=
  fun ρ => gklsGenerator H L_fn ℏ ρ

/-- The finite Liouville second-quantized GKLS generator preserves trace at
the rate level, by the existing `FullLindbladODE` theorem. -/
theorem liouvilleSecondQuantizedGKLS_trace_preserving
    (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ)
    (ρ : MatrixLiouvilleKet d) :
    (liouvilleSecondQuantizedGKLS H L_fn ℏ ρ).trace = 0 :=
  trace_gklsGenerator_eq_zero H L_fn ℏ ρ

/-- The zero matrix is a steady state of the finite Liouville GKLS generator. -/
theorem liouvilleSecondQuantizedGKLS_zero
    (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ) :
    liouvilleSecondQuantizedGKLS H L_fn ℏ 0 = 0 :=
  zero_isGKLSSteady H L_fn ℏ

/-- Direct matrix Liouville trajectory existence for the finite
second-quantized GKLS generator, using the existing zero-trajectory theorem for
generators that vanish at zero. -/
theorem exists_liouvilleSecondQuantizedGKLS_trajectory
    (H : Matrix d d ℂ) (L_fn : ι → Matrix d d ℂ) (ℏ : ℝ) :
    ∃ traj : MatrixLiouvilleTrajectory d,
      matrixLiouvilleSchrodinger
        (fun _ => liouvilleSecondQuantizedGKLS H L_fn ℏ) traj :=
  exists_matrix_liouville_trajectory
    (fun _ => liouvilleSecondQuantizedGKLS H L_fn ℏ)
    (fun _ => liouvilleSecondQuantizedGKLS_zero H L_fn ℏ)

/-- Any Lindblad solution written in the finite Liouville second-quantized
generator has zero trace rate. -/
theorem liouvilleSecondQuantizedGKLS_solution_trace_rate_zero
    {H : Matrix d d ℂ} {L_fn : ι → Matrix d d ℂ} {ℏ : ℝ}
    {ρ_fn ρ_dot_fn : ℝ → MatrixLiouvilleKet d}
    (h_sol : IsLindbladSolution H L_fn ℏ ρ_fn ρ_dot_fn) (t : ℝ) :
    (ρ_dot_fn t).trace = 0 :=
  isLindbladSolution_trace_rate_zero h_sol t

end DirectMatrixGKLS

end Physlib.QuantumMechanics.Liouville.SecondQuantization

end
