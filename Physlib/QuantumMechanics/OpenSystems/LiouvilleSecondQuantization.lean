/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Sym.Card
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Prod
public import Physlib.Mathematics.Distribution.Basic
public import Physlib.QuantumMechanics.DDimensions.Operators.Multiplication

/-!
# Second quantization of open quantum systems in Liouville space

This file formalizes the algebraic core of Sukharnikov, Chuchurka,
Benediktovitch and Rohringer, *Second quantization of open quantum systems in
Liouville space*, arXiv:2207.14234v2.

The finite part proves the matrix-unit and occupation-basis statements behind
Eqs. (4)--(10) and (13). The infinite and continuum parts reuse infrastructure
already present in Mathlib and Physlib:

* `Matrix.single` for discrete matrix units on arbitrary index types;
* `MeasureTheory.Lp` and `MemLp` for square-integrable continuum kernels;
* `SpaceDHilbertSpace` for the doubled-configuration-space Hilbert carrier;
* `SpaceDHilbertSpace.mulOperator` for pointwise multiplication with maximal
  domain;
* `Physlib.Distribution.diracDelta` for continuum-labelled matrix units.

A Kronecker matrix unit on a discrete index type and a Dirac matrix unit on a
continuum are intentionally distinct. ZIL annotation blocks record claim,
source, and dependency links, but Lean's kernel remains the proof authority.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics
namespace LiouvilleSecondQuantization

open MeasureTheory

/-! ## Finite-dimensional Liouville modes -/

/-- One of the `M` internal levels of an identical emitter. -/
abbrev Level (M : ℕ) := Fin M

/-- A Liouville-space mode, corresponding to the superket `|ij⟩⟩`. -/
abbrev Mode (M : ℕ) := Level M × Level M

/-- A finite-dimensional density-matrix carrier for an `M`-level emitter. -/
abbrev DensityMatrix (M : ℕ) := Matrix (Level M) (Level M) ℂ

/-- The number of Liouville modes of an `M`-level emitter is `M²`. -/
@[simp]
theorem card_mode (M : ℕ) : Fintype.card (Mode M) = M ^ 2 := by
  simp [Mode, Level, pow_two]

/-- The matrix unit `Eᵢⱼ = |i⟩⟨j|`. -/
def matrixUnit {M : ℕ} (i j : Level M) : DensityMatrix M :=
  Matrix.single i j 1

/-- Matrix units compose when their adjacent indices agree. -/
@[simp]
theorem matrixUnit_mul_same {M : ℕ} (i j k : Level M) :
    matrixUnit i j * matrixUnit j k = matrixUnit i k := by
  simp [matrixUnit]

/-- Matrix units compose to zero when their adjacent indices disagree. -/
@[simp]
theorem matrixUnit_mul_of_ne {M : ℕ} (i j k l : Level M) (h : j ≠ k) :
    matrixUnit i j * matrixUnit k l = 0 := by
  simp [matrixUnit, h]

/-- Unified matrix-unit multiplication rule `Eᵢⱼ Eₖₗ = δⱼₖ Eᵢₗ`. -/
theorem matrixUnit_mul_matrixUnit {M : ℕ} (i j k l : Level M) :
    matrixUnit i j * matrixUnit k l =
      if j = k then matrixUnit i l else 0 := by
  by_cases h : j = k
  · subst k
    simp
  · simp [h]

/-- Left action of a matrix unit on a density matrix. -/
def leftAction {M : ℕ} (p q : Level M) (ρ : DensityMatrix M) : DensityMatrix M :=
  matrixUnit p q * ρ

/-- Right action of a matrix unit on a density matrix. -/
def rightAction {M : ℕ} (k l : Level M) (ρ : DensityMatrix M) : DensityMatrix M :=
  ρ * matrixUnit k l

/-- Equation (8) at the one-emitter matrix-unit level: `Eₚq E_qj = Eₚj`. -/
@[simp]
theorem leftAction_matrixUnit_same {M : ℕ} (p q j : Level M) :
    leftAction p q (matrixUnit q j) = matrixUnit p j := by
  simp [leftAction]

/-- Equation (8) vanishes when the contracted indices disagree. -/
@[simp]
theorem leftAction_matrixUnit_of_ne {M : ℕ} (p q i j : Level M) (h : q ≠ i) :
    leftAction p q (matrixUnit i j) = 0 := by
  simp [leftAction, h]

/-- Equation (9) maps `Eᵢk` to `Eᵢl` under right multiplication. -/
@[simp]
theorem rightAction_matrixUnit_same {M : ℕ} (i k l : Level M) :
    rightAction k l (matrixUnit i k) = matrixUnit i l := by
  simp [rightAction]

/-- Equation (9) vanishes when the contracted indices disagree. -/
@[simp]
theorem rightAction_matrixUnit_of_ne {M : ℕ} (i j k l : Level M) (h : j ≠ k) :
    rightAction k l (matrixUnit i j) = 0 := by
  simp [rightAction, h]

/-- The left-right matrix-unit sandwich occurring in independent-reservoir terms. -/
def independentReservoirTerm {M : ℕ} (p q k l : Level M)
    (ρ : DensityMatrix M) : DensityMatrix M :=
  matrixUnit p q * ρ * matrixUnit k l

/-- The reservoir sandwich selects one density-matrix coefficient. -/
@[simp]
theorem independentReservoirTerm_eq {M : ℕ} (p q k l : Level M)
    (ρ : DensityMatrix M) :
    independentReservoirTerm p q k l ρ = Matrix.single p l (ρ q k) := by
  simp [independentReservoirTerm, matrixUnit]

/-- The unsymmetrized Liouville basis for `N` distinguishable emitters. -/
abbrev FullLiouvilleBasis (M N : ℕ) := Fin N → Mode M

/-- The full Liouville-space dimension is `M^(2N)`. -/
theorem card_fullLiouvilleBasis (M N : ℕ) :
    Fintype.card (FullLiouvilleBasis M N) = M ^ (2 * N) := by
  calc
    Fintype.card (FullLiouvilleBasis M N) = (M ^ 2) ^ N := by
      simp [FullLiouvilleBasis, pow_two]
    _ = M ^ (2 * N) := (pow_mul M 2 N).symm

/-- Fixed-particle-number occupation states over the `M²` Liouville modes. -/
abbrev OccupationBasis (M N : ℕ) := Sym (Mode M) N

/-- Equation (6): cardinality of the permutation-symmetric fixed-`N` basis. -/
theorem card_occupationBasis (M N : ℕ) :
    Fintype.card (OccupationBasis M N) = (M ^ 2 + N - 1).choose N := by
  simpa [OccupationBasis, pow_two] using
    (Sym.card_sym_eq_choose (α := Mode M) N)

/-- Occupation number of a particular Liouville mode. -/
def occupationNumber {M N : ℕ} (state : OccupationBasis M N) (mode : Mode M) : ℕ :=
  (state : Multiset (Mode M)).count mode

/-- Equation (13): each fixed sector contains exactly `N` excitations. -/
@[simp]
theorem occupationBasis_particleNumber {M N : ℕ} (state : OccupationBasis M N) :
    (state : Multiset (Mode M)).card = N :=
  state.property

/-- No mode occupation exceeds the fixed total particle number. -/
theorem occupationNumber_le_particleNumber {M N : ℕ}
    (state : OccupationBasis M N) (mode : Mode M) :
    occupationNumber state mode ≤ N := by
  calc
    occupationNumber state mode ≤ (state : Multiset (Mode M)).card :=
      Multiset.count_le_card mode _
    _ = N := state.property

/-! ## Discrete arbitrary-index kernels -/

/-
@zil target=self
self#formalizes@claim:discrete_arbitrary_index_liouville_mode.
self#generalizes@claim:finite_liouville_mode.
self#supported_by@source:arxiv_2207_14234_eq4_eq5.
@endzil
-/
/-- A Liouville mode over an arbitrary discrete level-index type. -/
abbrev KernelMode (ι : Type*) := ι × ι

/-- A complex density kernel over an arbitrary index type. -/
abbrev DensityKernel (ι : Type*) := Matrix ι ι ℂ

/-- The arbitrary-index Kronecker matrix unit, reusing `Matrix.single`. -/
def kernelMatrixUnit {ι : Type*} [DecidableEq ι] (i j : ι) : DensityKernel ι :=
  Matrix.single i j 1

@[simp]
theorem kernelMatrixUnit_apply_same {ι : Type*} [DecidableEq ι] (i j : ι) :
    kernelMatrixUnit i j i j = 1 := by
  simp [kernelMatrixUnit]

/-
@zil target=self
self#formalizes@claim:discrete_arbitrary_index_left_action.
self#supported_by@source:arxiv_2207_14234_eq8.
self#leverages@api:Mathlib.Matrix.single.
@endzil
-/
/-- Pointwise left action `(Eₚq ρ)ᵢⱼ = δᵢₚ ρ_qj`. -/
def leftKernelAction {ι : Type*} [DecidableEq ι] (p q : ι)
    (ρ : DensityKernel ι) : DensityKernel ι :=
  fun i j => if i = p then ρ q j else 0

/-
@zil target=self
self#formalizes@claim:discrete_arbitrary_index_right_action.
self#supported_by@source:arxiv_2207_14234_eq9.
self#leverages@api:Mathlib.Matrix.single.
@endzil
-/
/-- Pointwise right action `(ρ Eₖl)ᵢⱼ = δⱼl ρᵢk`. -/
def rightKernelAction {ι : Type*} [DecidableEq ι] (k l : ι)
    (ρ : DensityKernel ι) : DensityKernel ι :=
  fun i j => if j = l then ρ i k else 0

@[simp]
theorem leftKernelAction_apply_same {ι : Type*} [DecidableEq ι]
    (p q j : ι) (ρ : DensityKernel ι) :
    leftKernelAction p q ρ p j = ρ q j := by
  simp [leftKernelAction]

@[simp]
theorem leftKernelAction_apply_of_ne {ι : Type*} [DecidableEq ι]
    (p q i j : ι) (ρ : DensityKernel ι) (h : i ≠ p) :
    leftKernelAction p q ρ i j = 0 := by
  simp [leftKernelAction, h]

@[simp]
theorem rightKernelAction_apply_same {ι : Type*} [DecidableEq ι]
    (k l i : ι) (ρ : DensityKernel ι) :
    rightKernelAction k l ρ i l = ρ i k := by
  simp [rightKernelAction]

@[simp]
theorem rightKernelAction_apply_of_ne {ι : Type*} [DecidableEq ι]
    (k l i j : ι) (ρ : DensityKernel ι) (h : j ≠ l) :
    rightKernelAction k l ρ i j = 0 := by
  simp [rightKernelAction, h]

@[simp]
theorem leftKernelAction_matrixUnit_same {ι : Type*} [DecidableEq ι]
    (p q j : ι) :
    leftKernelAction p q (kernelMatrixUnit q j) = kernelMatrixUnit p j := by
  ext i k
  by_cases hi : i = p <;> by_cases hk : k = j <;>
    simp_all [leftKernelAction, kernelMatrixUnit, Matrix.single_apply] <;> aesop

@[simp]
theorem rightKernelAction_matrixUnit_same {ι : Type*} [DecidableEq ι]
    (i k l : ι) :
    rightKernelAction k l (kernelMatrixUnit i k) = kernelMatrixUnit i l := by
  ext p q
  by_cases hp : p = i <;> by_cases hq : q = l <;>
    simp_all [rightKernelAction, kernelMatrixUnit, Matrix.single_apply] <;> aesop

/-- The arbitrary discrete-index left-right sandwich `Eₚq ρ Eₖl`. -/
def independentReservoirKernel {ι : Type*} [DecidableEq ι]
    (p q k l : ι) (ρ : DensityKernel ι) : DensityKernel ι :=
  leftKernelAction p q (rightKernelAction k l ρ)

/-- The arbitrary discrete reservoir sandwich selects one coefficient. -/
@[simp]
theorem independentReservoirKernel_eq_single {ι : Type*} [DecidableEq ι]
    (p q k l : ι) (ρ : DensityKernel ι) :
    independentReservoirKernel p q k l ρ = Matrix.single p l (ρ q k) := by
  ext i j
  by_cases hi : i = p <;> by_cases hj : j = l <;>
    simp_all [independentReservoirKernel, leftKernelAction, rightKernelAction,
      Matrix.single_apply] <;> aesop

/-- The arbitrary-index carrier reduces definitionally to the finite carrier. -/
theorem densityKernel_fin_eq_densityMatrix (M : ℕ) :
    DensityKernel (Level M) = DensityMatrix M := rfl

/-! ## Infinite mode sets and finite-particle sectors -/

/-- Every level embeds diagonally into the Liouville-mode type. -/
def diagonalModeEmbedding (ι : Type*) : ι ↪ KernelMode ι where
  toFun i := (i, i)
  inj' := by
    intro i j h
    exact congrArg Prod.fst h

/-- An infinite level-index type induces an infinite Liouville-mode type. -/
theorem kernelMode_infinite (ι : Type*) [Infinite ι] : Infinite (KernelMode ι) := by
  infer_instance

/-- The fixed-`N` occupation basis over arbitrary, possibly infinite, modes. -/
abbrev KernelOccupationBasis (ι : Type*) (N : ℕ) := Sym (KernelMode ι) N

/-- Every state in an arbitrary-mode fixed sector has exactly `N` excitations. -/
@[simp]
theorem kernelOccupationBasis_particleNumber {ι : Type*} {N : ℕ}
    (state : KernelOccupationBasis ι N) :
    (state : Multiset (KernelMode ι)).card = N :=
  state.property

/-- Occupation number of one arbitrary Liouville mode. -/
def kernelOccupationNumber {ι : Type*} [DecidableEq ι] {N : ℕ}
    (state : KernelOccupationBasis ι N) (mode : KernelMode ι) : ℕ :=
  (state : Multiset (KernelMode ι)).count mode

/-- A mode occupation cannot exceed the fixed total particle number. -/
theorem kernelOccupationNumber_le_particleNumber {ι : Type*} [DecidableEq ι]
    {N : ℕ} (state : KernelOccupationBasis ι N) (mode : KernelMode ι) :
    kernelOccupationNumber state mode ≤ N := by
  calc
    kernelOccupationNumber state mode ≤ (state : Multiset (KernelMode ι)).card :=
      Multiset.count_le_card mode _
    _ = N := state.property

/-- Basis labels for the algebraic sum of all finite-particle sectors. -/
abbrev AlgebraicLiouvilleFockBasis (ι : Type*) :=
  Σ N : ℕ, KernelOccupationBasis ι N

/-- Particle number carried by an algebraic Fock-basis label. -/
def fockParticleNumber {ι : Type*} (state : AlgebraicLiouvilleFockBasis ι) : ℕ :=
  state.1

/-- Include a fixed-particle state into the algebraic Fock basis. -/
def ofOccupationSector {ι : Type*} {N : ℕ}
    (state : KernelOccupationBasis ι N) : AlgebraicLiouvilleFockBasis ι :=
  ⟨N, state⟩

@[simp]
theorem fockParticleNumber_ofOccupationSector {ι : Type*} {N : ℕ}
    (state : KernelOccupationBasis ι N) :
    fockParticleNumber (ofOccupationSector state) = N := rfl

/-- The zero-particle basis label. -/
def vacuumBasis (ι : Type*) : AlgebraicLiouvilleFockBasis ι :=
  ⟨0, ⟨0, rfl⟩⟩

@[simp]
theorem fockParticleNumber_vacuum (ι : Type*) :
    fockParticleNumber (vacuumBasis ι) = 0 := rfl

/-! ## Continuum kernels from existing `L²` infrastructure -/

/-
@zil target=self
self#formalizes@claim:continuum_liouville_kernel_l2_carrier.
self#leverages@api:Mathlib.MeasureTheory.Lp.
self#leverages@api:Mathlib.MeasureTheory.MemLp.
self#ensures@guarantee:measurability_and_square_integrability_by_type.
@endzil
-/
/-- The continuum Liouville-kernel Hilbert space `L²(X × X, μ × μ; ℂ)`. -/
abbrev ContinuumKernelSpace (X : Type*) [MeasurableSpace X] (μ : Measure X) :=
  MeasureTheory.Lp ℂ 2 (μ.prod μ)

/-- The existing `MemLp` predicate specialized to continuum Liouville kernels. -/
def MemContinuumKernel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : X × X → ℂ) : Prop :=
  MemLp K 2 (μ.prod μ)

/-- Membership already contains almost-everywhere strong measurability. -/
lemma memContinuumKernel_aestronglyMeasurable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {K : X × X → ℂ} (hK : MemContinuumKernel μ K) :
    AEStronglyMeasurable K (μ.prod μ) :=
  hK.1

/-- Membership already contains finiteness of the `L²` norm. -/
lemma memContinuumKernel_eLpNorm_lt_top {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {K : X × X → ℂ} (hK : MemContinuumKernel μ K) :
    eLpNorm K 2 (μ.prod μ) < ⊤ :=
  hK.2

/-- The standard `AEEqFun` constructor belongs to the existing `Lp` carrier
exactly when its representative satisfies `MemContinuumKernel`. -/
lemma aeEqFun_mk_mem_continuumKernelSpace_iff
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (K : X × X → ℂ) (hK : AEStronglyMeasurable K (μ.prod μ)) :
    AEEqFun.mk K hK ∈ ContinuumKernelSpace X μ ↔ MemContinuumKernel μ K := by
  rw [Lp.mem_Lp_iff_memLp]
  exact memLp_congr_ae (AEEqFun.coeFn_mk K hK)

/-- Construct a continuum Liouville kernel directly in the existing `Lp` space. -/
def mkContinuumKernel {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {K : X × X → ℂ} (hK : MemContinuumKernel μ K) : ContinuumKernelSpace X μ :=
  ⟨AEEqFun.mk K hK.1, (aeEqFun_mk_mem_continuumKernelSpace_iff K hK.1).mpr hK⟩

/-- The constructed `Lp` element agrees almost everywhere with its representative. -/
lemma coe_mkContinuumKernel_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {K : X × X → ℂ} (hK : MemContinuumKernel μ K) :
    (mkContinuumKernel hK : X × X → ℂ) =ᵐ[μ.prod μ] K :=
  AEEqFun.coeFn_mk K hK.1

/-- The squared continuum-kernel norm uses the existing Hilbert-space norm. -/
def continuumKernelNormSq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (K : ContinuumKernelSpace X μ) : ℝ :=
  ‖K‖ ^ 2

@[simp]
theorem continuumKernelNormSq_nonneg {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (K : ContinuumKernelSpace X μ) :
    0 ≤ continuumKernelNormSq K := by
  exact sq_nonneg ‖K‖

/-! ## Pointwise kernel operations -/

/-- Left multiplication of a regular kernel representative by a function on
its first variable. -/
def leftPointwiseKernelAction {X : Type*} (a : X → ℂ)
    (K : X × X → ℂ) : X × X → ℂ :=
  fun z => a z.1 * K z

/-- Right multiplication of a regular kernel representative by a function on
its second variable. -/
def rightPointwiseKernelAction {X : Type*} (b : X → ℂ)
    (K : X × X → ℂ) : X × X → ℂ :=
  fun z => K z * b z.2

@[simp]
theorem leftPointwiseKernelAction_apply {X : Type*} (a : X → ℂ)
    (K : X × X → ℂ) (z : X × X) :
    leftPointwiseKernelAction a K z = a z.1 * K z := rfl

@[simp]
theorem rightPointwiseKernelAction_apply {X : Type*} (b : X → ℂ)
    (K : X × X → ℂ) (z : X × X) :
    rightPointwiseKernelAction b K z = K z * b z.2 := rfl

/-- Left and right pointwise multipliers commute. -/
theorem leftPointwise_rightPointwise_commute {X : Type*}
    (a b : X → ℂ) (K : X × X → ℂ) :
    leftPointwiseKernelAction a (rightPointwiseKernelAction b K) =
      rightPointwiseKernelAction b (leftPointwiseKernelAction a K) := by
  funext z
  simp [leftPointwiseKernelAction, rightPointwiseKernelAction, mul_assoc]

/-
@zil target=self
self#formalizes@claim:doubled_space_pointwise_operator.
self#leverages@api:QuantumMechanics.SpaceDHilbertSpace.
self#leverages@api:QuantumMechanics.SpaceDHilbertSpace.mulOperator.
self#ensures@guarantee:maximal_domain_pointwise_action.
@endzil
-/
/-- The existing spatial `L²` carrier on doubled configuration space. -/
abbrev SpaceLiouvilleHilbertSpace (d : ℕ) :=
  SpaceDHilbertSpace (d + d)

/-- Pointwise multiplication on the doubled-space Liouville Hilbert space,
using the existing maximal-domain multiplication operator. -/
def spacePointwiseKernelOperator {d : ℕ} (f : Space (d + d) → ℂ) :
    SpaceLiouvilleHilbertSpace d →ₗ.[ℂ] SpaceLiouvilleHilbertSpace d :=
  SpaceDHilbertSpace.mulOperator volume f

/-- An almost-everywhere strongly measurable multiplier has dense domain. -/
theorem spacePointwiseKernelOperator_hasDenseDomain {d : ℕ}
    {f : Space (d + d) → ℂ} (hf : AEStronglyMeasurable f) :
    (spacePointwiseKernelOperator f).HasDenseDomain := by
  simpa [spacePointwiseKernelOperator] using
    (SpaceDHilbertSpace.mulOperator_hasDenseDomain hf)

/-- The existing multiplication operator acts pointwise almost everywhere. -/
lemma spacePointwiseKernelOperator_apply_ae {d : ℕ}
    {f : Space (d + d) → ℂ}
    (ψ : (spacePointwiseKernelOperator f).domain) :
    spacePointwiseKernelOperator f ψ =ᵐ[volume] f • ψ := by
  simpa [spacePointwiseKernelOperator] using
    (SpaceDHilbertSpace.mulOperator_apply_ae (f := f) ψ)

/-! ## Continuum matrix units as distributions -/

/-
@zil target=self
self#formalizes@claim:continuum_dirac_matrix_unit.
self#leverages@api:Physlib.Distribution.diracDelta.
self#supported_by@source:arxiv_2207_14234_eq4_eq5.
self#excludes@claim:continuum_matrix_unit_as_kronecker_function.
@endzil
-/
/-- A continuum matrix unit is a Dirac distribution on the doubled level
space, not a Kronecker-valued ordinary function. -/
abbrev ContinuumMatrixUnitDistribution (d : ℕ) :=
  Physlib.Distribution ℂ (Space d × Space d) ℂ

/-- Dirac matrix unit centered at the ordered pair `(p,q)`. -/
def continuumMatrixUnit {d : ℕ} (p q : Space d) :
    ContinuumMatrixUnitDistribution d :=
  Physlib.Distribution.diracDelta ℂ (p, q)

/-- The continuum matrix unit evaluates a Schwartz test kernel at `(p,q)`. -/
@[simp]
theorem continuumMatrixUnit_apply {d : ℕ} (p q : Space d)
    (η : SchwartzMap (Space d × Space d) ℂ) :
    continuumMatrixUnit p q η = η (p, q) :=
  rfl

end LiouvilleSecondQuantization
end QuantumMechanics
