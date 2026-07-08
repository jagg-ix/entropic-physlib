/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree

/-!
# Sorkin-Johnston vacuum in the two-dimensional causal diamond

This file formalizes the repo-facing core of Mathur--Surya,
*Sorkin-Johnston vacuum for a massive scalar field in the 2D causal diamond*,
arXiv:1906.07952v3.

The general SJ algebra is already available in `SorkinJohnstonRegionState`: a
real Pauli-Jordan kernel `Delta` is antisymmetric, a Wightman two-point function
has antisymmetric part `i Delta`, and the SJ prescription keeps the positive
spectral part of the self-adjoint operator `i Delta`. This file adds the
paper-specific causal-diamond layer:

* null-coordinate diamond points `(u,v)`;
* the massive two-dimensional Pauli-Jordan kernel of Eq. (22), parameterized by
  the ordinary Bessel function `J_0`;
* the exact equation saying that `i Delta` is the complex kernel written in the
  paper;
* the massless limit when `J_0(0)=1`;
* the crossover scale `m_c = 2 Lambda`, including the quoted value
  `Lambda = 0.462`, `m_c = 0.924`;
* a bridge back to the existing SJ-state and Verch quasifree infrastructure.

No new axioms.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SorkinJohnstonCausalDiamond

open Physlib.QuantumMechanics.ComplexAction.SorkinJohnstonRegionState
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Construction
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SchmidtVerchQuasifree

/-! ## A. Null-coordinate causal-diamond kernel -/

/-- A point in the two-dimensional causal diamond, written in null coordinates. -/
structure DiamondPoint where
  u : ℝ
  v : ℝ

/-- `Delta u = u-u'`. -/
def deltaU (x y : DiamondPoint) : ℝ := x.u - y.u

/-- `Delta v = v-v'`. -/
def deltaV (x y : DiamondPoint) : ℝ := x.v - y.v

/-- The Heaviside step function used in the paper's Eq. (22). -/
def heaviside (t : ℝ) : ℝ := if 0 ≤ t then 1 else 0

/-- The causal support/sign factor `theta(Delta u)+theta(Delta v)-1`. -/
def diamondCausalFactor (x y : DiamondPoint) : ℝ :=
  heaviside (deltaU x y) + heaviside (deltaV x y) - 1

/-- The real Pauli-Jordan kernel `Delta` underlying Mathur-Surya Eq. (22).

The paper writes `i Delta = - i/2 J_0(m sqrt(2 Delta u Delta v))
(theta(Delta u)+theta(Delta v)-1)`. This is the real `Delta` whose
multiplication by `i` gives that displayed complex kernel. -/
def massivePauliJordanDelta2D (J0 : ℝ → ℝ) (m : ℝ) (x y : DiamondPoint) : ℝ :=
  -(1 / 2) * J0 (m * Real.sqrt (2 * deltaU x y * deltaV x y)) * diamondCausalFactor x y

/-- The complex kernel `i Delta` in the notation of Eq. (22). -/
def massiveIPauliJordan2D (J0 : ℝ → ℝ) (m : ℝ) (x y : DiamondPoint) : ℂ :=
  Complex.I * ((massivePauliJordanDelta2D J0 m x y : ℝ) : ℂ)

/-- Eq. (22), written as an equality between the repo's real `Delta` convention
and the paper's complex `i Delta` convention. -/
theorem massiveIPauliJordan2D_eq_paper_kernel (J0 : ℝ → ℝ) (m : ℝ) (x y : DiamondPoint) :
    massiveIPauliJordan2D J0 m x y =
      -(Complex.I / 2) *
        ((J0 (m * Real.sqrt (2 * deltaU x y * deltaV x y)) : ℝ) : ℂ) *
        ((diamondCausalFactor x y : ℝ) : ℂ) := by
  unfold massiveIPauliJordan2D massivePauliJordanDelta2D
  push_cast
  ring

/-- At `m = 0`, Eq. (22) reduces to the massless causal-support kernel whenever
`J_0(0)=1`. -/
theorem massiveIPauliJordan2D_zero_mass (J0 : ℝ → ℝ) (hJ0 : J0 0 = 1) :
    massiveIPauliJordan2D J0 0 =
      fun x y : DiamondPoint => -(Complex.I / 2) * ((diamondCausalFactor x y : ℝ) : ℂ) := by
  funext x y
  rw [massiveIPauliJordan2D_eq_paper_kernel]
  simp [hJ0]

/-! ## B. SJ state and spectral selection, reusing the existing region-state API -/

/-- The SJ Wightman function on the diamond, using the existing region-state convention
`W = A + i Delta/2`. -/
def diamondWightmanTwoPoint (A Delta : DiamondPoint → DiamondPoint → ℝ)
    (x y : DiamondPoint) : ℂ :=
  wightmanTwoPoint A Delta x y

/-- The diamond Wightman function recovers the field commutator by the existing
Sorkin-Johnston region-state theorem. -/
theorem diamondWightman_commutator (A Delta : DiamondPoint → DiamondPoint → ℝ)
    (hA : IsSymmetricKernel A) (hDelta : IsPauliJordan Delta) (x y : DiamondPoint) :
    diamondWightmanTwoPoint A Delta x y - diamondWightmanTwoPoint A Delta y x =
      Complex.I * ((Delta x y : ℝ) : ℂ) :=
  wightman_commutator A Delta hA hDelta x y

/-- A positive symmetric part gives an SJ state on the two-dimensional diamond. -/
theorem diamondWightman_isSJState (A Delta : DiamondPoint → DiamondPoint → ℝ)
    (hA : IsSymmetricKernel A) (hDelta : IsPauliJordan Delta) (hApos : ∀ x, 0 ≤ A x x) :
    IsSJState (diamondWightmanTwoPoint A Delta) Delta :=
  wightman_isSJState A Delta hA hDelta hApos

/-- The SJ positive spectral choice is non-negative. -/
theorem diamond_sjSpectrum_nonneg (lam : ℝ) : 0 ≤ sjSpectrum lam :=
  sjSpectrum_nonneg lam

/-- The positive-minus-negative SJ spectral choice recovers the original
Pauli-Jordan eigenvalue. -/
theorem diamond_sjSpectrum_sub (lam : ℝ) : sjSpectrum lam - sjSpectrum (-lam) = lam :=
  sjSpectrum_sub lam

/-! ## C. The central eigenvalue problem and small-mass spectrum -/

/-- Pointwise complex conjugation of a mode. -/
def pointwiseConj {X : Type*} (f : X → ℂ) : X → ℂ := fun x => starRingEnd ℂ (f x)

/-- A kernel/integral operator eigenfunction equation `T f = lam f`. -/
def KernelEigenfunction {X : Type*} (T : (X → ℂ) → X → ℂ) (lam : ℝ) (f : X → ℂ) : Prop :=
  T f = fun x => ((lam : ℝ) : ℂ) * f x

/-- The Pauli-Jordan `i Delta` operator anticommutes with pointwise conjugation in the
spectral pairing statement of Eq. (8). -/
def AntiCommutesWithConj {X : Type*} (T : (X → ℂ) → X → ℂ) : Prop :=
  ∀ f, T (pointwiseConj f) = fun x => -pointwiseConj (T f) x

/-- Eq. (8): if `u` is an eigenfunction with real eigenvalue `lambda`, then the
complex-conjugate mode has eigenvalue `-lambda`, provided the operator has the
Pauli-Jordan conjugation anticommutation property. -/
theorem conjugate_mode_eigenvalue_neg {X : Type*} (T : (X → ℂ) → X → ℂ)
    (lam : ℝ) (u : X → ℂ) (hT : AntiCommutesWithConj T)
    (hu : KernelEigenfunction T lam u) :
    KernelEigenfunction T (-lam) (pointwiseConj u) := by
  unfold KernelEigenfunction at hu ⊢
  rw [hT u, hu]
  funext x
  simp [pointwiseConj]

/-- Swap the null coordinates `u` and `v`. -/
def uvSwapPoint (x : DiamondPoint) : DiamondPoint := { u := x.v, v := x.u }

/-- Pointwise pullback by the null-coordinate swap. -/
def uvSwapMode (f : DiamondPoint → ℂ) : DiamondPoint → ℂ := fun x => f (uvSwapPoint x)

/-- Symmetric part of a mode under `u ↔ v`. -/
def symmetricMode (f : DiamondPoint → ℂ) : DiamondPoint → ℂ := fun x => f x + uvSwapMode f x

/-- Antisymmetric part of a mode under `u ↔ v`. -/
def antisymmetricMode (f : DiamondPoint → ℂ) : DiamondPoint → ℂ := fun x => f x - uvSwapMode f x

/-- Linearity of an abstract kernel/integral operator. -/
def KernelLinear {X : Type*} (T : (X → ℂ) → X → ℂ) : Prop :=
  ∀ (f g : X → ℂ) (a b : ℂ),
    T (fun x => a * f x + b * g x) = fun x => a * T f x + b * T g x

/-- Commutation with `u ↔ v`, the symmetry used in Claim 1. -/
def CommutesWithUVSwap (T : (DiamondPoint → ℂ) → DiamondPoint → ℂ) : Prop :=
  ∀ f, T (uvSwapMode f) = uvSwapMode (T f)

/-- A linear combination of two modes with the same eigenvalue is again an eigenmode. -/
theorem linear_combination_eigenfunction {X : Type*} (T : (X → ℂ) → X → ℂ)
    (lam : ℝ) (f g : X → ℂ) (a b : ℂ) (hlin : KernelLinear T)
    (hf : KernelEigenfunction T lam f) (hg : KernelEigenfunction T lam g) :
    KernelEigenfunction T lam (fun x => a * f x + b * g x) := by
  unfold KernelEigenfunction at hf hg ⊢
  rw [hlin f g a b, hf, hg]
  funext x
  ring

/-- Claim 1, first half: the symmetric part of an eigenmode is again an eigenmode when
the operator is linear and commutes with the null-coordinate swap. -/
theorem symmetricMode_eigenfunction {T : (DiamondPoint → ℂ) → DiamondPoint → ℂ}
    (lam : ℝ) (f : DiamondPoint → ℂ) (hlin : KernelLinear T)
    (hswap : CommutesWithUVSwap T) (hf : KernelEigenfunction T lam f) :
    KernelEigenfunction T lam (symmetricMode f) := by
  have hswapEig : KernelEigenfunction T lam (uvSwapMode f) := by
    unfold KernelEigenfunction at hf ⊢
    rw [hswap f, hf]
    funext x
    rfl
  have h1 : (fun x => (1:ℂ) * f x + 1 * uvSwapMode f x) = symmetricMode f := by
    funext x; unfold symmetricMode; ring
  rw [← h1]
  exact linear_combination_eigenfunction T lam f (uvSwapMode f) 1 1 hlin hf hswapEig

/-- Claim 1, second half: the antisymmetric part of an eigenmode is again an eigenmode
under the same hypotheses. -/
theorem antisymmetricMode_eigenfunction {T : (DiamondPoint → ℂ) → DiamondPoint → ℂ}
    (lam : ℝ) (f : DiamondPoint → ℂ) (hlin : KernelLinear T)
    (hswap : CommutesWithUVSwap T) (hf : KernelEigenfunction T lam f) :
    KernelEigenfunction T lam (antisymmetricMode f) := by
  have hswapEig : KernelEigenfunction T lam (uvSwapMode f) := by
    unfold KernelEigenfunction at hf ⊢
    rw [hswap f, hf]
    funext x
    rfl
  have h1 : (fun x => (1:ℂ) * f x + (-1) * uvSwapMode f x) = antisymmetricMode f := by
    funext x; unfold antisymmetricMode; ring
  rw [← h1]
  exact linear_combination_eigenfunction T lam f (uvSwapMode f) 1 (-1) hlin hf hswapEig

/-- Section 3, Eq. (30): the antisymmetric-family small-mass quantization right-hand side
through order `m^4`, with the `O(m^6)` remainder separated out. -/
def antisymmetricQuantizationRHS (m k : ℝ) : ℝ :=
  (m ^ 2 / k + (m ^ 4 / (12 * k)) * (1 - 3 / k ^ 2)) * Real.cos k

/-- The residual form of Eq. (30). Setting this residual to zero is the displayed
quantization condition without the suppressed `O(m^6)` term. -/
def antisymmetricQuantizationResidual (m k : ℝ) : ℝ :=
  Real.sin k - antisymmetricQuantizationRHS m k

theorem antisymmetricQuantization_residual_zero_iff (m k : ℝ) :
    antisymmetricQuantizationResidual m k = 0 ↔
      Real.sin k = antisymmetricQuantizationRHS m k := by
  unfold antisymmetricQuantizationResidual
  constructor <;> intro h <;> linarith

/-- At zero mass, the antisymmetric quantization condition reduces to `sin k = 0`. -/
theorem antisymmetricQuantizationRHS_zero_mass (k : ℝ) :
    antisymmetricQuantizationRHS 0 k = 0 := by
  simp [antisymmetricQuantizationRHS]

/-- Section 3, Eq. (31): the displayed small-mass root approximation for the
antisymmetric family, treating `n` as the real mode label. -/
def antisymmetricRootApprox (m n : ℝ) : ℝ :=
  n * Real.pi + m ^ 2 / (n * Real.pi) +
    m ^ 4 * (1 / (12 * n * Real.pi) - 5 / (4 * n ^ 3 * Real.pi ^ 3))

theorem antisymmetricRootApprox_zero_mass (n : ℝ) :
    antisymmetricRootApprox 0 n = n * Real.pi := by
  simp [antisymmetricRootApprox]

/-- Section 3, Eq. (33): the symmetric-family small-mass quantization right-hand side
through order `m^4`, with the `O(m^6)` remainder separated out. -/
def symmetricQuantizationRHS (m k : ℝ) : ℝ :=
  (2 * k - (m ^ 2 / k) * (1 - 2 * k ^ 2) +
      (m ^ 4 / (12 * k ^ 3)) * (3 - 29 * k ^ 2 + 28 * k ^ 4)) * Real.cos k

def symmetricQuantizationResidual (m k : ℝ) : ℝ :=
  Real.sin k - symmetricQuantizationRHS m k

theorem symmetricQuantization_residual_zero_iff (m k : ℝ) :
    symmetricQuantizationResidual m k = 0 ↔ Real.sin k = symmetricQuantizationRHS m k := by
  unfold symmetricQuantizationResidual
  constructor <;> intro h <;> linarith

/-- At zero mass, Eq. (33) reduces to Sorkin's massless condition `sin k = 2 k cos k`. -/
theorem symmetricQuantizationRHS_zero_mass (k : ℝ) :
    symmetricQuantizationRHS 0 k = 2 * k * Real.cos k := by
  simp [symmetricQuantizationRHS]

/-- Section 3, Eq. (34): the displayed small-mass root approximation for the symmetric family. -/
def symmetricRootApprox (m k0 : ℝ) : ℝ :=
  k0 + m ^ 2 * ((1 - 2 * k0 ^ 2) / (k0 * (1 - 4 * k0 ^ 2))) +
    m ^ 4 *
      (((3 - 4 * k0 ^ 2) * (-5 + 35 * k0 ^ 2 - 40 * k0 ^ 4 + 16 * k0 ^ 6)) /
        (12 * k0 ^ 3 * (1 - 4 * k0 ^ 2) ^ 3))

theorem symmetricRootApprox_zero_mass (k0 : ℝ) : symmetricRootApprox 0 k0 = k0 := by
  simp [symmetricRootApprox]

/-- The first omitted order after retaining terms through `m^4` is `m^6`. -/
theorem smallMass_fourth_order_next_power : 4 + 2 = (6 : ℕ) := by
  norm_num

/-! ## D. Mode sums and finite truncations -/

/-- One normalized positive SJ mode contribution in the formal mode sum of Eq. (83). -/
def normalizedModeContribution (L k normSq : ℝ) (u : DiamondPoint → ℂ)
    (x y : DiamondPoint) : ℂ :=
  -(((L ^ 2 / (k * normSq) : ℝ) : ℂ)) * u x * pointwiseConj u y

/-- A finite version of the SJ mode sum, used both for exact finite structures and for the
paper's numerical truncations. -/
def finiteSJModeSum {ι : Type*} [Fintype ι]
    (L : ℝ) (k normSq : ι → ℝ) (u : ι → DiamondPoint → ℂ) :
    DiamondPoint → DiamondPoint → ℂ :=
  fun x y => ∑ i, normalizedModeContribution L (k i) (normSq i) (u i) x y

/-- The small-mass Wightman sum decomposes into antisymmetric and symmetric contributions,
matching Eq. (88). -/
def finiteSmallMassWightman {ιA ιS : Type*} [Fintype ιA] [Fintype ιS]
    (L : ℝ) (kA normA : ιA → ℝ) (uA : ιA → DiamondPoint → ℂ)
    (kS normS : ιS → ℝ) (uS : ιS → DiamondPoint → ℂ) :
    DiamondPoint → DiamondPoint → ℂ :=
  fun x y => finiteSJModeSum L kA normA uA x y + finiteSJModeSum L kS normS uS x y

theorem finiteSmallMassWightman_decompose {ιA ιS : Type*} [Fintype ιA] [Fintype ιS]
    (L : ℝ) (kA normA : ιA → ℝ) (uA : ιA → DiamondPoint → ℂ)
    (kS normS : ιS → ℝ) (uS : ιS → DiamondPoint → ℂ) :
    finiteSmallMassWightman L kA normA uA kS normS uS =
      fun x y => finiteSJModeSum L kA normA uA x y + finiteSJModeSum L kS normS uS x y := rfl

/-- Truncating a sequence of kernels at `N` terms. -/
def truncatedKernelSum (N : ℕ) (K : ℕ → DiamondPoint → DiamondPoint → ℂ) :
    DiamondPoint → DiamondPoint → ℂ :=
  fun x y => (Finset.range N).sum (fun n => K n x y)

theorem truncatedKernelSum_succ (N : ℕ) (K : ℕ → DiamondPoint → DiamondPoint → ℂ) :
    truncatedKernelSum (N + 1) K = fun x y => truncatedKernelSum N K x y + K N x y := by
  funext x y
  simp [truncatedKernelSum, Finset.sum_range_succ]

/-! ## E. Causal-diamond and quasifree bridges -/

/-- The existing complex-action causal diamond supplies the geometric region used by
the SJ diamond construction: for `R>0`, the center belongs to the closed diamond. -/
theorem sj_center_mem_complexAction_diamond {R : ℝ} (hR : 0 < R) :
    (0 : ℂ) ∈ causalDiamond (-(R : ℂ)) (R : ℂ) :=
  center_mem_diamond hR

/-- In the separable limit, the same vacuum structure is the pure Verch quasifree
Hadamard state already used by the repo. -/
theorem sj_separable_verch_quasifree_vacuum (phi : Fin 2 → ℝ) :
    OperatorAlgebra.WeylCCRSpacetime.quasifreeWeight (fun _ _ => (0 : ℝ)) phi = 1 ∧
      SymplecticAdjointHadamard.sympForm * SymplecticAdjointHadamard.sympForm = -1 :=
  ⟨pure_quasifree_separable phi, pure_state_complex_structure⟩

/-! ## F. Center/corner comparison and crossover scale -/

/-- A two-point kernel differs from a reference vacuum by a constant on a region.
This is the logical form of the center/corner asymptotic comparisons in the paper. -/
def DiffersByConstantOnRegion {X : Type*} (Region : X → Prop)
    (W Reference : X → X → ℂ) (constant : ℂ) : Prop :=
  ∀ x y, Region x → Region y → W x y - Reference x y = constant

/-- If `W = Reference + constant` on a region, then it differs by that constant there. -/
theorem differsByConstantOnRegion_of_eq {X : Type*} (Region : X → Prop)
    (W Reference : X → X → ℂ) (constant : ℂ)
    (h : ∀ x y, Region x → Region y → W x y = Reference x y + constant) :
    DiffersByConstantOnRegion Region W Reference constant := by
  intro x y hx hy
  rw [h x y hx hy]
  ring

/-- Constant shifts compose additively when comparing vacuum kernels on the same region. -/
theorem differsByConstantOnRegion_trans {X : Type*} (Region : X → Prop)
    (W1 W2 W3 : X → X → ℂ) (c12 c23 : ℂ)
    (h12 : DiffersByConstantOnRegion Region W1 W2 c12)
    (h23 : DiffersByConstantOnRegion Region W2 W3 c23) :
    DiffersByConstantOnRegion Region W1 W3 (c12 + c23) := by
  intro x y hx hy
  calc
    W1 x y - W3 x y = (W1 x y - W2 x y) + (W2 x y - W3 x y) := by ring
    _ = c12 + c23 := by rw [h12 x y hx hy, h23 x y hx hy]

/-- Eq. (119): the constant by which the center SJ approximation differs from the
massless Minkowski reference. `eulerGamma` is kept as an explicit real parameter. -/
def centerSJDifferenceConstant (Lambda eulerGamma epsCenter : ℝ) : ℂ :=
  -(((Real.log (Real.pi / 4) / (2 * Real.pi) : ℝ) : ℂ)) +
    ((epsCenter : ℝ) : ℂ) +
      (((Real.log (2 * Lambda ^ 2 * Real.exp (2 * eulerGamma)) / (4 * Real.pi) : ℝ) : ℂ))

/-- The center approximation packaged as the massless reference plus the paper's
constant offset. -/
def centerSJApprox (W0mink : DiamondPoint → DiamondPoint → ℂ)
    (Lambda eulerGamma epsCenter : ℝ) : DiamondPoint → DiamondPoint → ℂ :=
  fun x y => W0mink x y + centerSJDifferenceConstant Lambda eulerGamma epsCenter

theorem centerSJApprox_sub_masslessMinkowski (W0mink : DiamondPoint → DiamondPoint → ℂ)
    (Lambda eulerGamma epsCenter : ℝ) (x y : DiamondPoint) :
    centerSJApprox W0mink Lambda eulerGamma epsCenter x y - W0mink x y =
      centerSJDifferenceConstant Lambda eulerGamma epsCenter := by
  simp [centerSJApprox]

theorem centerSJApprox_differsByConstant (W0mink : DiamondPoint → DiamondPoint → ℂ)
    (Lambda eulerGamma epsCenter : ℝ) (Region : DiamondPoint → Prop) :
    DiffersByConstantOnRegion Region (centerSJApprox W0mink Lambda eulerGamma epsCenter)
      W0mink (centerSJDifferenceConstant Lambda eulerGamma epsCenter) := by
  intro x y _ _
  exact centerSJApprox_sub_masslessMinkowski W0mink Lambda eulerGamma epsCenter x y

/-- The exact coefficient in Eq. (126), before the numerical approximation `≈ 0.034`. -/
def cornerFourthOrderCoefficient (zeta3 : ℝ) : ℝ := 7 * zeta3 / (8 * Real.pi ^ 3)

/-- Eq. (129): the constant by which the corner SJ approximation differs from the
massive mirror reference. -/
def cornerSJDifferenceConstant (zeta3 m epsCorner : ℝ) : ℂ :=
  (((cornerFourthOrderCoefficient zeta3 * m ^ 4 + epsCorner : ℝ) : ℂ))

def cornerSJApprox (Wmirror : DiamondPoint → DiamondPoint → ℂ)
    (zeta3 m epsCorner : ℝ) : DiamondPoint → DiamondPoint → ℂ :=
  fun x y => Wmirror x y + cornerSJDifferenceConstant zeta3 m epsCorner

theorem cornerSJApprox_sub_mirror (Wmirror : DiamondPoint → DiamondPoint → ℂ)
    (zeta3 m epsCorner : ℝ) (x y : DiamondPoint) :
    cornerSJApprox Wmirror zeta3 m epsCorner x y - Wmirror x y =
      cornerSJDifferenceConstant zeta3 m epsCorner := by
  simp [cornerSJApprox]

theorem cornerSJApprox_differsByConstant (Wmirror : DiamondPoint → DiamondPoint → ℂ)
    (zeta3 m epsCorner : ℝ) (Region : DiamondPoint → Prop) :
    DiffersByConstantOnRegion Region (cornerSJApprox Wmirror zeta3 m epsCorner)
      Wmirror (cornerSJDifferenceConstant zeta3 m epsCorner) := by
  intro x y _ _
  exact cornerSJApprox_sub_mirror Wmirror zeta3 m epsCorner x y

/-- The paper's crossover relation: `m_c = 2 Lambda`. -/
def sjCriticalMass (Lambda : ℝ) : ℝ := 2 * Lambda

/-- For the value quoted in the paper, `Lambda = 0.462`, the crossover mass is `0.924`. -/
theorem sjCriticalMass_numeric : sjCriticalMass 0.462 = 0.924 := by
  norm_num [sjCriticalMass]

/-- The three center regimes described in Section 5. -/
inductive CenterVacuumRegime where
  | masslessMinkowski
  | crossover
  | massiveMinkowski
  deriving DecidableEq

/-- Section 5 center behavior: below `m_c` the causal-set SJ data tracks the massless
Minkowski curve, at `m_c` the curves cross, and above it tracks the massive curve. -/
def centerVacuumRegime (Lambda m : ℝ) : CenterVacuumRegime :=
  if m < sjCriticalMass Lambda then CenterVacuumRegime.masslessMinkowski
  else if m = sjCriticalMass Lambda then CenterVacuumRegime.crossover
  else CenterVacuumRegime.massiveMinkowski

theorem centerVacuumRegime_small {Lambda m : ℝ} (hm : m < sjCriticalMass Lambda) :
    centerVacuumRegime Lambda m = CenterVacuumRegime.masslessMinkowski := by
  simp [centerVacuumRegime, hm]

theorem centerVacuumRegime_at_crossover {Lambda m : ℝ} (hm : m = sjCriticalMass Lambda) :
    centerVacuumRegime Lambda m = CenterVacuumRegime.crossover := by
  have hnotlt : ¬ m < sjCriticalMass Lambda := by rw [hm]; exact lt_irrefl _
  simp [centerVacuumRegime, hm]

theorem centerVacuumRegime_large {Lambda m : ℝ} (hm : sjCriticalMass Lambda < m) :
    centerVacuumRegime Lambda m = CenterVacuumRegime.massiveMinkowski := by
  have hnotlt : ¬ m < sjCriticalMass Lambda := not_lt_of_ge (le_of_lt hm)
  have hneq : ¬ m = sjCriticalMass Lambda := ne_of_gt hm
  simp [centerVacuumRegime, hnotlt, hneq]

/-- An algebraic representative for a family with a well-defined massless value. This is the
part of the paper's massless-limit statement that can be checked without analytic
topology: the `m=0` specialization is a specified kernel. -/
def HasMasslessValue {X : Type*} (W : ℝ → X → X → ℂ) (W0 : X → X → ℂ) : Prop := W 0 = W0

theorem hasMasslessValue_apply {X : Type*} (W : ℝ → X → X → ℂ) (W0 : X → X → ℂ)
    (hW : HasMasslessValue W W0) (x y : X) : W 0 x y = W0 x y := by
  rw [hW]

/-! ## G. Causal-set discretization and the finite Green function -/

/-- A finite causal set approximating the diamond, represented only by its causal order. -/
structure FiniteCausalSet (N : ℕ) where
  precedes : Fin N → Fin N → Prop

/-- A finite kernel on a causal set. -/
abbrev FiniteKernel (N : ℕ) := Fin N → Fin N → ℂ

/-- The identity kernel. -/
def kernelId (N : ℕ) : FiniteKernel N := fun i j => if i = j then 1 else 0

/-- Finite kernel composition. -/
def kernelComp {N : ℕ} (A B : FiniteKernel N) : FiniteKernel N :=
  fun i j => ∑ k, A i k * B k j

theorem kernelId_comp {N : ℕ} (B : FiniteKernel N) : kernelComp (kernelId N) B = B := by
  funext i j
  simp [kernelComp, kernelId]

theorem kernelComp_id {N : ℕ} (B : FiniteKernel N) : kernelComp B (kernelId N) = B := by
  funext i j
  simp [kernelComp, kernelId]

/-- The causal matrix `C_ij = 1` if `X_i ≺ X_j`, and `0` otherwise. -/
def causalMatrix {N : ℕ} (C : FiniteCausalSet N) [∀ i j, Decidable (C.precedes i j)] :
    FiniteKernel N :=
  fun i j => if C.precedes i j then 1 else 0

/-- Section 5: the massless causal-set retarded Green function is `G_0 = C/2`. -/
def causalSetMasslessRetardedGreen {N : ℕ} (C : FiniteCausalSet N)
    [∀ i j, Decidable (C.precedes i j)] : FiniteKernel N :=
  fun i j => causalMatrix C i j / 2

theorem causalSetMasslessRetardedGreen_eq_half_causalMatrix {N : ℕ}
    (C : FiniteCausalSet N) [∀ i j, Decidable (C.precedes i j)] :
    causalSetMasslessRetardedGreen C = fun i j => causalMatrix C i j / 2 := rfl

/-- The finite resolvent factor `I + (m^2/rho) G_0` in Eq. (132). -/
def massiveGreenResolventFactor {N : ℕ} (rho m : ℝ) (G0 : FiniteKernel N) : FiniteKernel N :=
  fun i j => kernelId N i j + (((m ^ 2 / rho : ℝ) : ℂ)) * G0 i j

theorem massiveGreenResolventFactor_zero_mass {N : ℕ} (rho : ℝ) (G0 : FiniteKernel N) :
    massiveGreenResolventFactor rho 0 G0 = kernelId N := by
  funext i j
  simp [massiveGreenResolventFactor]

/-- Eq. (132), once the inverse of the resolvent factor has been supplied. -/
def causalSetMassiveGreen {N : ℕ} (resolventInverse G0 : FiniteKernel N) : FiniteKernel N :=
  kernelComp resolventInverse G0

theorem causalSetMassiveGreen_eq_resolvent_inverse_mul {N : ℕ}
    (resolventInverse G0 : FiniteKernel N) :
    causalSetMassiveGreen resolventInverse G0 = kernelComp resolventInverse G0 := rfl

theorem causalSetMassiveGreen_zero_mass {N : ℕ} (G0 : FiniteKernel N) :
    causalSetMassiveGreen (kernelId N) G0 = G0 :=
  kernelId_comp G0

/-! ## H. Weighted inner product and the Rindler appendix -/

/-- Ordinary finite kernel action. -/
def ordinaryKernelAction {X : Type*} [Fintype X] (K : X → X → ℂ) (f : X → ℂ) : X → ℂ :=
  fun x => ∑ y, K x y * f y

/-- Weighted finite kernel action, the finite analogue of Eq. (177). -/
def weightedKernelAction {X : Type*} [Fintype X] (K : X → X → ℂ) (w : X → ℝ)
    (f : X → ℂ) : X → ℂ :=
  fun x => ∑ y, K x y * f y * ((w y : ℝ) : ℂ)

/-- Eq. (179): weighted action is ordinary action on the weighted test function. -/
theorem weightedKernelAction_eq_ordinary_weightedFunction {X : Type*} [Fintype X]
    (K : X → X → ℂ) (w : X → ℝ) (f : X → ℂ) :
    weightedKernelAction K w f = ordinaryKernelAction K (fun y => ((w y : ℝ) : ℂ) * f y) := by
  funext x
  simp [weightedKernelAction, ordinaryKernelAction, mul_comm, mul_left_comm]

theorem weightedKernelAction_eq_ordinary_of_weight_one {X : Type*} [Fintype X]
    (K : X → X → ℂ) (w : X → ℝ) (f : X → ℂ) (hw : ∀ x, w x = 1) :
    weightedKernelAction K w f = ordinaryKernelAction K f := by
  funext x
  simp [weightedKernelAction, ordinaryKernelAction, hw]

/-- Rindler metric volume factor `e^{2a xi}` from Eq. (180). -/
def rindlerVolumeFactor (a xi : ℝ) : ℝ := Real.exp (2 * a * xi)

/-- The appendix choice `w = e^{-2a xi}`. -/
def rindlerSJWeight (a xi : ℝ) : ℝ := Real.exp (-(2 * a * xi))

/-- The appendix trick: `w e^{2a xi} = 1`, so the weighted eigenproblem reduces to
the unweighted massless SJ eigenproblem in the Rindler light-cone coordinates. -/
theorem rindler_weight_cancels_volume (a xi : ℝ) :
    rindlerSJWeight a xi * rindlerVolumeFactor a xi = 1 := by
  unfold rindlerSJWeight rindlerVolumeFactor
  rw [← Real.exp_add]
  ring_nf
  simp

/-! ## I. Repository-facing capability package -/

/-- The formal Sorkin-Johnston causal-diamond structure available to the rest of the repository. -/
def HasSorkinJohnstonCausalDiamondCarrier : Prop :=
  (∀ (A Delta : DiamondPoint → DiamondPoint → ℝ),
      IsSymmetricKernel A → IsPauliJordan Delta → ∀ x y,
        diamondWightmanTwoPoint A Delta x y - diamondWightmanTwoPoint A Delta y x =
          Complex.I * ((Delta x y : ℝ) : ℂ))
    ∧ (∀ lam : ℝ, sjSpectrum lam - sjSpectrum (-lam) = lam)
    ∧ (∀ (J0 : ℝ → ℝ), J0 0 = 1 →
      massiveIPauliJordan2D J0 0 =
        fun x y : DiamondPoint => -(Complex.I / 2) * ((diamondCausalFactor x y : ℝ) : ℂ))
    ∧ (∀ (T : (DiamondPoint → ℂ) → DiamondPoint → ℂ) (lam : ℝ) (f : DiamondPoint → ℂ),
      KernelLinear T → CommutesWithUVSwap T → KernelEigenfunction T lam f →
        KernelEigenfunction T lam (symmetricMode f) ∧
          KernelEigenfunction T lam (antisymmetricMode f))
    ∧ (∀ m k : ℝ, antisymmetricQuantizationResidual m k = 0 ↔
      Real.sin k = antisymmetricQuantizationRHS m k)
    ∧ (∀ m k : ℝ, symmetricQuantizationResidual m k = 0 ↔
      Real.sin k = symmetricQuantizationRHS m k)
    ∧ (∀ (W0mink : DiamondPoint → DiamondPoint → ℂ) (Lambda eulerGamma epsCenter : ℝ),
      DiffersByConstantOnRegion (fun _ : DiamondPoint => True)
        (centerSJApprox W0mink Lambda eulerGamma epsCenter) W0mink
        (centerSJDifferenceConstant Lambda eulerGamma epsCenter))
    ∧ (∀ (Wmirror : DiamondPoint → DiamondPoint → ℂ) (zeta3 m epsCorner : ℝ),
      DiffersByConstantOnRegion (fun _ : DiamondPoint => True)
        (cornerSJApprox Wmirror zeta3 m epsCorner) Wmirror
        (cornerSJDifferenceConstant zeta3 m epsCorner))
    ∧ (∀ {N : ℕ} (G0 : FiniteKernel N), causalSetMassiveGreen (kernelId N) G0 = G0)
    ∧ (∀ (a xi : ℝ), rindlerSJWeight a xi * rindlerVolumeFactor a xi = 1)
    ∧ sjCriticalMass 0.462 = 0.924

/-- The Sorkin-Johnston causal-diamond structure is checked from the existing SJ region-state
formalization plus the Mathur-Surya Eq. (22) diamond kernel. -/
theorem sorkinJohnstonCausalDiamondCarrier_checked : HasSorkinJohnstonCausalDiamondCarrier := by
  refine ⟨?_, diamond_sjSpectrum_sub, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sjCriticalMass_numeric⟩
  · intro A Delta hA hDelta x y
    exact diamondWightman_commutator A Delta hA hDelta x y
  · intro J0 hJ0
    exact massiveIPauliJordan2D_zero_mass J0 hJ0
  · intro T lam f hlin hswap hf
    exact ⟨symmetricMode_eigenfunction lam f hlin hswap hf,
      antisymmetricMode_eigenfunction lam f hlin hswap hf⟩
  · intro m k
    exact antisymmetricQuantization_residual_zero_iff m k
  · intro m k
    exact symmetricQuantization_residual_zero_iff m k
  · intro W0mink Lambda eulerGamma epsCenter
    exact centerSJApprox_differsByConstant W0mink Lambda eulerGamma epsCenter (fun _ => True)
  · intro Wmirror zeta3 m epsCorner
    exact cornerSJApprox_differsByConstant Wmirror zeta3 m epsCorner (fun _ => True)
  · intro N G0
    exact causalSetMassiveGreen_zero_mass G0
  · intro a xi
    exact rindler_weight_cancels_volume a xi

end Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SorkinJohnstonCausalDiamond

end

end
