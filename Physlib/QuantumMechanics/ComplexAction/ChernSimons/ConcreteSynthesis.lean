/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TorusHilbert
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.Explicit
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
public import Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling

/-!
# Concrete Chern-Simons-Witten synthesis

This module records what is already formalized enough to stop treating the Hayashi
CSW file as a purely abstract interface.

The module does **not** claim the full analytic CSW functional integral.  It
builds the concrete finite/trivial-bundle spine currently available in the repo:

* a local matrix-valued CSW density and its holomorphic/anti-holomorphic split;
* the existing explicit Hayashi couplings and `SL(2,ℂ)` quadratic gravity split;
* the explicit torus Hilbert factorization and diagonal genus-one invariant;
* the existing WDW/constraint replacement interface;
* the existing Maxwell-Faraday gauge/Bianchi carrier;
* the existing Kálnay Bose/Fermi and Dirac/Bogoliubov field-operator links.

So this is the checked assembly layer: assuming the finite local CSW model below,
Lean verifies that the explicit components prove the abstract Hayashi bridge
obligations already used by the rest of the repository.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna
open Physlib.QuantumMechanics.ComplexAction.BoseFermiOperatorAlgebra.Basic
open Physlib.QuantumMechanics.ComplexAction.YangMillsGaugeDynamics
open Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling


/-- A finite local/trivial-bundle shadow of a `𝔤_C`-valued connection on a 3-manifold:
three matrix components of a connection one-form. -/
abbrev LocalCSConnection (n : ℕ) : Type :=
  Fin 3 → Matrix (Fin n) (Fin n) ℂ

/-! ### Yang-Mills realization of the finite local connection -/

/-- The zero coordinate derivative for the finite/trivial-bundle local model.
With this derivative, Yang-Mills curvature reduces to the non-Abelian
commutator part `A ∧ A`. -/
def localCSZeroPartial {n : ℕ} :
    GaugePartial Unit (Fin 3) (Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ _ => 0

/-- Regard a finite local CSW connection as a Yang-Mills gauge potential on one
point with three form components. -/
def localCSAsGaugePotential {n : ℕ} (A : LocalCSConnection n) :
    GaugePotential Unit (Fin 3) (Matrix (Fin n) (Fin n) ℂ) :=
  fun _ i => A i

/-- Constant gauge functions in the finite local model. -/
def localCSConstantGauge {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) :
    Unit → Matrix (Fin n) (Fin n) ℂ :=
  fun _ => G

/-- The cubic local Chern-Simons density shadow
`Tr(A₀(A₁A₂ - A₂A₁))`, i.e. the matrix component of `Tr(A ∧ A ∧ A)`.
This is the noncommutative part of the CS functional in a finite trivialization. -/
noncomputable def localChernSimonsCubic {n : ℕ} (A : LocalCSConnection n) : ℂ :=
  Matrix.trace (A 0 * A 1 * A 2 - A 0 * A 2 * A 1)

/-- The holomorphic finite local CSW sector weighted by Hayashi's coupling `t = k + is`. -/
noncomputable def localHolomorphicAction {n : ℕ} (c : HayashiCouplings)
    (A : LocalCSConnection n) : ℂ :=
  holomorphicCoupling c / (8 * (Real.pi : ℂ)) * localChernSimonsCubic A

/-- The anti-holomorphic finite local CSW sector weighted by Hayashi's coupling `t̄ = k - is`. -/
noncomputable def localAntiholomorphicAction {n : ℕ} (c : HayashiCouplings)
    (Abar : LocalCSConnection n) : ℂ :=
  antiholomorphicCoupling c / (8 * (Real.pi : ℂ)) * localChernSimonsCubic Abar

/-- The finite local complex CSW action is the sum of its two chiral sectors. -/
noncomputable def localComplexCSWAction {n : ℕ} (c : HayashiCouplings)
    (P : LocalCSConnection n × LocalCSConnection n) : ℂ :=
  localHolomorphicAction c P.1 + localAntiholomorphicAction c P.2

/-- **[Concrete local CSW split]** The finite local/trivial-bundle CSW action splits into
holomorphic and anti-holomorphic Chern-Simons sectors. -/
lemma localComplexCSWAction_split {n : ℕ} (c : HayashiCouplings)
    (P : LocalCSConnection n × LocalCSConnection n) :
    localComplexCSWAction c P =
      localHolomorphicAction c P.1 + localAntiholomorphicAction c P.2 := rfl

/-- The finite local CSW model as a concrete `ComplexCSWAction` carrier. -/
noncomputable def localComplexCSWCarrier {n : ℕ} (c : HayashiCouplings) :
    ComplexCSWAction (LocalCSConnection n × LocalCSConnection n) where
  holomorphicAction P := localHolomorphicAction c P.1
  antiholomorphicAction P := localAntiholomorphicAction c P.2
  totalAction P := localComplexCSWAction c P
  total_eq_sector_sum := fun _ => rfl


/-- The derivative-free finite/trivial-bundle curvature shadow `Fᵢⱼ = [Aᵢ,Aⱼ]`.
This is the algebraic non-abelian part of `dA + A ∧ A`. -/
noncomputable def localCSCurvature {n : ℕ} (A : LocalCSConnection n) (i j : Fin 3) :
    Matrix (Fin n) (Fin n) ℂ :=
  ⁅A i, A j⁆

/-- The finite local CSW curvature is exactly the Yang-Mills curvature in the
zero-derivative local/trivial-bundle specialization. -/
lemma localCSCurvature_eq_yangMillsCurvature_zeroPartial {n : ℕ}
    (A : LocalCSConnection n) (i j : Fin 3) :
    localCSCurvature A i j =
      yangMillsCurvature localCSZeroPartial (localCSAsGaugePotential A) () i j := by
  simp [localCSCurvature, yangMillsCurvature, localCSZeroPartial,
    localCSAsGaugePotential]

/-- The local curvature is antisymmetric in its two form indices. -/
lemma localCSCurvature_swap {n : ℕ} (A : LocalCSConnection n) (i j : Fin 3) :
    localCSCurvature A j i = -localCSCurvature A i j := by
  simp only [localCSCurvature, Ring.lie_def]; abel

/-- The diagonal curvature component vanishes. -/
@[simp] lemma localCSCurvature_self {n : ℕ} (A : LocalCSConnection n) (i : Fin 3) :
    localCSCurvature A i i = 0 := by
  simp only [localCSCurvature, Ring.lie_def, sub_self]

/-- Finite local flatness: all curvature commutators vanish. -/
def LocalCSFlat {n : ℕ} (A : LocalCSConnection n) : Prop :=
  ∀ i j, localCSCurvature A i j = 0

/-- Local finite flatness is the vanishing of the zero-derivative Yang-Mills
curvature. -/
lemma localCSFlat_iff_yangMillsCurvature_zeroPartial_vanishes {n : ℕ}
    (A : LocalCSConnection n) :
    LocalCSFlat A ↔
      ∀ i j,
        yangMillsCurvature localCSZeroPartial (localCSAsGaugePotential A) () i j = 0 := by
  constructor
  · intro h i j
    rw [← localCSCurvature_eq_yangMillsCurvature_zeroPartial A i j]
    exact h i j
  · intro h i j
    rw [localCSCurvature_eq_yangMillsCurvature_zeroPartial A i j]
    exact h i j

/-- In the finite/trivial-bundle model, flatness is exactly pairwise commutation of the connection
components. -/
lemma localCSFlat_iff_pairwise_commute {n : ℕ} (A : LocalCSConnection n) :
    LocalCSFlat A ↔ ∀ i j, A i * A j = A j * A i := by
  constructor
  · intro h i j
    exact sub_eq_zero.mp (by simpa [localCSCurvature, Ring.lie_def] using h i j)
  · intro h i j
    simp [localCSCurvature, Ring.lie_def, h i j]

/-- A convenient constructor for finite flat local CSW connections. -/
lemma localCSFlat_of_pairwise_commute {n : ℕ} (A : LocalCSConnection n)
    (h : ∀ i j, A i * A j = A j * A i) :
    LocalCSFlat A :=
  (localCSFlat_iff_pairwise_commute A).mpr h

/-- The cubic CS density is the trace of `A₀ F₁₂`. -/
lemma localChernSimonsCubic_eq_trace_A0_curvature12 {n : ℕ} (A : LocalCSConnection n) :
    localChernSimonsCubic A = Matrix.trace (A 0 * localCSCurvature A 1 2) := by
  apply congrArg Matrix.trace
  simp [localCSCurvature, Ring.lie_def]
  noncomm_ring

/-- If the `12` curvature component vanishes, the local cubic CS density vanishes. -/
lemma localChernSimonsCubic_eq_zero_of_curvature12_zero {n : ℕ} (A : LocalCSConnection n)
    (hF : localCSCurvature A 1 2 = 0) :
    localChernSimonsCubic A = 0 := by
  rw [localChernSimonsCubic_eq_trace_A0_curvature12, hF]
  simp

/-- Flat finite connections have zero local cubic CS density. -/
lemma localChernSimonsCubic_eq_zero_of_flat {n : ℕ} (A : LocalCSConnection n)
    (hA : LocalCSFlat A) :
    localChernSimonsCubic A = 0 :=
  localChernSimonsCubic_eq_zero_of_curvature12_zero A (hA 1 2)

/-- The holomorphic local action vanishes on a flat finite connection. -/
lemma localHolomorphicAction_eq_zero_of_flat {n : ℕ} (c : HayashiCouplings)
    (A : LocalCSConnection n) (hA : LocalCSFlat A) :
    localHolomorphicAction c A = 0 := by
  rw [localHolomorphicAction, localChernSimonsCubic_eq_zero_of_flat A hA, mul_zero]

/-- The anti-holomorphic local action vanishes on a flat finite connection. -/
lemma localAntiholomorphicAction_eq_zero_of_flat {n : ℕ} (c : HayashiCouplings)
    (Abar : LocalCSConnection n) (hAbar : LocalCSFlat Abar) :
    localAntiholomorphicAction c Abar = 0 := by
  rw [localAntiholomorphicAction, localChernSimonsCubic_eq_zero_of_flat Abar hAbar, mul_zero]

/-- The finite local complex CSW action vanishes on flat holomorphic and anti-holomorphic sectors. -/
lemma localComplexCSWAction_eq_zero_of_flat {n : ℕ} (c : HayashiCouplings)
    (P : LocalCSConnection n × LocalCSConnection n)
    (hA : LocalCSFlat P.1) (hAbar : LocalCSFlat P.2) :
    localComplexCSWAction c P = 0 := by
  rw [localComplexCSWAction, localHolomorphicAction_eq_zero_of_flat c P.1 hA,
    localAntiholomorphicAction_eq_zero_of_flat c P.2 hAbar, zero_add]

/-- Constant finite gauge conjugation `Aᵢ ↦ G Aᵢ H`, with `H` the inverse of `G` when the
hypothesis `H * G = 1` is supplied. -/
noncomputable def localGaugeConjugate {n : ℕ} (G H : Matrix (Fin n) (Fin n) ℂ)
    (A : LocalCSConnection n) : LocalCSConnection n :=
  fun i => G * A i * H

/-- Constant finite gauge conjugation is the zero-derivative Yang-Mills gauge
transformation of the one-point gauge potential. -/
lemma localGaugeConjugate_eq_gaugeTransformPotential_zeroPartial {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℂ) (A : LocalCSConnection n) :
    localCSAsGaugePotential (localGaugeConjugate G H A) =
      gaugeTransformPotential localCSZeroPartial
        (localCSConstantGauge G) (localCSConstantGauge H) (localCSAsGaugePotential A) := by
  funext x i
  cases x
  simp [localCSAsGaugePotential, localGaugeConjugate, gaugeTransformPotential,
    localCSZeroPartial, localCSConstantGauge]

/-- The existing local CSW curvature covariance is the constant-sector
Yang-Mills curvature covariance identity. -/
lemma localGaugeConjugate_yangMillsCurvatureCovariant {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℂ) (A : LocalCSConnection n) (hHG : H * G = 1) :
    GaugeCurvatureCovariant localCSZeroPartial
      (localCSConstantGauge G) (localCSConstantGauge H) (localCSAsGaugePotential A) := by
  intro i j x
  cases x
  simp [yangMillsCurvature, gaugeTransformPotential,
    gaugeTransformCurvature, gaugeAdjoint, localCSZeroPartial, localCSAsGaugePotential,
    localCSConstantGauge, Ring.lie_def]
  calc
    (G * A i * H) * (G * A j * H) - (G * A j * H) * (G * A i * H)
        = G * A i * (H * G) * A j * H - G * A j * (H * G) * A i * H := by
      noncomm_ring
    _ = G * A i * 1 * A j * H - G * A j * 1 * A i * H := by
      rw [hHG]
    _ = G * (A i * A j - A j * A i) * H := by
      noncomm_ring

/-- Curvature is covariant under constant finite gauge conjugation. -/
lemma localCSCurvature_gauge_conjugate {n : ℕ} (G H : Matrix (Fin n) (Fin n) ℂ)
    (A : LocalCSConnection n) (i j : Fin 3) (hHG : H * G = 1) :
    localCSCurvature (localGaugeConjugate G H A) i j =
      G * localCSCurvature A i j * H := by
  rw [localCSCurvature_eq_yangMillsCurvature_zeroPartial]
  rw [localGaugeConjugate_eq_gaugeTransformPotential_zeroPartial G H A]
  rw [localGaugeConjugate_yangMillsCurvatureCovariant G H A hHG i j ()]
  simp [gaugeTransformCurvature, gaugeAdjoint, localCSConstantGauge]
  rw [← localCSCurvature_eq_yangMillsCurvature_zeroPartial A i j]

/-- Flatness is preserved by constant finite gauge conjugation. -/
lemma localCSFlat_gauge_conjugate {n : ℕ} (G H : Matrix (Fin n) (Fin n) ℂ)
    (A : LocalCSConnection n) (hHG : H * G = 1) (hA : LocalCSFlat A) :
    LocalCSFlat (localGaugeConjugate G H A) := by
  intro i j
  rw [localCSCurvature_gauge_conjugate G H A i j hHG, hA i j]
  simp

/-- The finite local cubic CS density is invariant under constant finite gauge conjugation. -/
lemma localChernSimonsCubic_gauge_conjugate {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) ℂ) (A : LocalCSConnection n) (hHG : H * G = 1) :
    localChernSimonsCubic (localGaugeConjugate G H A) = localChernSimonsCubic A := by
  set X : Matrix (Fin n) (Fin n) ℂ := A 0 * A 1 * A 2 - A 0 * A 2 * A 1
  have hmat :
      (localGaugeConjugate G H A 0 * localGaugeConjugate G H A 1 * localGaugeConjugate G H A 2
          - localGaugeConjugate G H A 0 * localGaugeConjugate G H A 2
            * localGaugeConjugate G H A 1)
        = G * X * H := by
    subst X
    unfold localGaugeConjugate
    calc
      (G * A 0 * H) * (G * A 1 * H) * (G * A 2 * H)
          - (G * A 0 * H) * (G * A 2 * H) * (G * A 1 * H)
          = G * A 0 * (H * G) * A 1 * (H * G) * A 2 * H
              - G * A 0 * (H * G) * A 2 * (H * G) * A 1 * H := by
        noncomm_ring
      _ = G * A 0 * 1 * A 1 * 1 * A 2 * H - G * A 0 * 1 * A 2 * 1 * A 1 * H := by
        rw [hHG]
      _ = G * (A 0 * A 1 * A 2 - A 0 * A 2 * A 1) * H := by
        noncomm_ring
  unfold localChernSimonsCubic
  rw [hmat]
  calc
    Matrix.trace (G * X * H) = Matrix.trace (G * (X * H)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace ((X * H) * G) := Matrix.trace_mul_comm G (X * H)
    _ = Matrix.trace (X * (H * G)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (X * 1) := by rw [hHG]
    _ = Matrix.trace X := by simp

/-- The holomorphic local CSW action is invariant under constant finite gauge conjugation. -/
lemma localHolomorphicAction_gauge_conjugate {n : ℕ} (c : HayashiCouplings)
    (G H : Matrix (Fin n) (Fin n) ℂ) (A : LocalCSConnection n) (hHG : H * G = 1) :
    localHolomorphicAction c (localGaugeConjugate G H A) = localHolomorphicAction c A := by
  rw [localHolomorphicAction, localHolomorphicAction, localChernSimonsCubic_gauge_conjugate G H A hHG]

/-- The anti-holomorphic local CSW action is invariant under constant finite gauge conjugation. -/
lemma localAntiholomorphicAction_gauge_conjugate {n : ℕ} (c : HayashiCouplings)
    (G H : Matrix (Fin n) (Fin n) ℂ) (Abar : LocalCSConnection n) (hHG : H * G = 1) :
    localAntiholomorphicAction c (localGaugeConjugate G H Abar) =
      localAntiholomorphicAction c Abar := by
  rw [localAntiholomorphicAction, localAntiholomorphicAction,
    localChernSimonsCubic_gauge_conjugate G H Abar hHG]

/-- The finite local complex CSW action is invariant under simultaneous constant finite gauge
conjugation of both chiral sectors. -/
lemma localComplexCSWAction_gauge_conjugate {n : ℕ} (c : HayashiCouplings)
    (G H : Matrix (Fin n) (Fin n) ℂ) (P : LocalCSConnection n × LocalCSConnection n)
    (hHG : H * G = 1) :
    localComplexCSWAction c
        (localGaugeConjugate G H P.1, localGaugeConjugate G H P.2)
      = localComplexCSWAction c P := by
  rw [localComplexCSWAction, localComplexCSWAction,
    localHolomorphicAction_gauge_conjugate c G H P.1 hHG,
    localAntiholomorphicAction_gauge_conjugate c G H P.2 hHG]


/-- **[Gauge/Bianchi carrier already available]** The Maxwell-Faraday finite momentum-space gauge
layer provides the two basic identities that the CSW gauge sector must eventually lift to
non-abelian connections: gauge invariance of `F = dA` and the homogeneous Bianchi identity. -/
lemma faraday_gauge_invariant_and_bianchi (q A : Fin 4 → ℝ) (χ : ℝ) :
    faraday q (fun ρ => A ρ + χ * q ρ) = faraday q A
      ∧ ∀ lam μ ν,
        q lam * faraday q A μ ν + q μ * faraday q A ν lam + q ν * faraday q A lam μ = 0 :=
  ⟨faraday_gauge_invariant q A χ, fun lam μ ν => faraday_bianchi q A lam μ ν⟩


/-- A concrete Hayashi replacement in which CSW parallel transport is instantiated by the existing
Wheeler-DeWitt predicate itself.  This is intentionally modest: it is the checked bridge from the
existing WDW formalization into Hayashi's replacement slot. -/
def wheelerDeWittParallelReplacement (HR HI : ℝ) : HayashiParallelTransportReplacement ℂ where
  wheelerDeWittPhysical Ψ := WheelerDeWitt HR HI Ψ
  parallelTransportPhysical Ψ := WheelerDeWitt HR HI Ψ
  replacement := fun _ => Iff.rfl

/-- Orthogonality for the explicitly factorized torus character pairs.  The charge is the pair of
left/right labels, and different pairs have zero Kronecker inner product. -/
def torusPairCharacterCarrier (k : ℕ) :
    HayashiOrthogonalityCarrier (Fin k × Fin k) (Fin k × Fin k) where
  inner ψ φ := if ψ = φ then 1 else 0
  charge ψ := ψ
  orthogonal_of_charge_ne ψ φ h := by simp [h]


/-- The concrete finite/trivial-bundle CSW bridge assembled from repo components:

* `localComplexCSWCarrier` gives the action split;
* `hayashiSL2CGravity` gives the explicit `SL(2,ℂ)` quadratic gravity split;
* `wheelerDeWittParallelReplacement` fills the WDW/parallel-transport slot;
* `torusHilbertFactorization` gives the explicit torus left/right split;
* `torusDiagonalInvariant` gives the genus-one invariant factorization;
* `torusPairCharacterCarrier` gives orthogonality of distinct character pairs. -/
noncomputable def concreteCSWBridge {n k : ℕ} (c : HayashiCouplings)
    (lam ω e : ℂ) (Λ : ℝ) (hΛ : Λ < 0) (HR HI : ℝ) (χ : Fin k → ℂ) :
    HayashiCSWGravityBridge
      (LocalCSConnection n × LocalCSConnection n)
      ℂ
      (Fin k × Fin k)
      (Fin k)
      (Fin k)
      (Fin k)
      ℂ
      (Fin k × Fin k) where
  actionSplit := localComplexCSWCarrier c
  gravity := hayashiSL2CGravity lam ω e Λ hΛ
  parallelReplacement := wheelerDeWittParallelReplacement HR HI
  torusFactorization := torusHilbertFactorization k
  invariantFactorization := torusDiagonalInvariant k χ
  orthogonality := torusPairCharacterCarrier k

/-- **[Concrete CSW obligations proved]** The explicit finite CSW action, explicit `SL(2,ℂ)`
gravity split, WDW replacement, torus factorization, diagonal invariant factorization, and
orthogonality carrier satisfy the Hayashi bridge obligations.  The final conjunct also exposes the
repo's Kálnay Bose-bilinear fermion-field operator statement at the same time. -/
lemma concreteCSWBridge_satisfies_hayashi_and_field_obligations
    {n k : ℕ} (c : HayashiCouplings) (lam ω e : ℂ) (Λ : ℝ) (hΛ : Λ < 0)
    (HR HI : ℝ) (χ : Fin k → ℂ)
    (P : LocalCSConnection n × LocalCSConnection n) (ψ : ℂ)
    (Ψ φ : Fin k × Fin k) (O : Fin k) (p : Momentum 3) (hcharge : Ψ ≠ φ) :
    (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).actionSplit.totalAction P =
        (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).actionSplit.holomorphicAction P
          + (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).actionSplit.antiholomorphicAction P
      ∧ (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).gravity.complexAction =
          (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).gravity.exoticTerm
            + (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).gravity.einsteinHilbertTerm
      ∧ ((@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).parallelReplacement.wheelerDeWittPhysical ψ
          ↔ (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).parallelReplacement.parallelTransportPhysical ψ)
      ∧ (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).torusFactorization.assemble
          ((@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).torusFactorization.leftState Ψ)
          ((@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).torusFactorization.rightState Ψ) = Ψ
      ∧ (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).invariantFactorization.complexInvariant O =
          (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).invariantFactorization.rightInvariant O
            * (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).invariantFactorization.leftInvariant O
      ∧ (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).orthogonality.inner Ψ φ = 0
      ∧ KalnayBoseFermiFieldStatement p :=
  hayashi_CSW_gravity_bose_fermi_operator_synthesis
    (B := @concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ) P ψ Ψ O φ p hcharge


/-- Concrete CSW synthesis plus the completed half-filled FQHE sector. This
packages the existing finite CSW/Hayashi/Bose-Fermi bridge together with the
FQHE topological-order bundle, without restating either side's equations. -/
def HasConcreteCSWFQHEBridge
    {n k : ℕ} (c : HayashiCouplings) (lam ω e : ℂ) (Λ : ℝ) (hΛ : Λ < 0)
    (HR HI : ℝ) (χ : Fin k → ℂ)
    (P : LocalCSConnection n × LocalCSConnection n) (ψ : ℂ)
    (Ψ φ : Fin k × Fin k) (O : Fin k) (p : Momentum 3) : Prop :=
  ((@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).actionSplit.totalAction P =
        (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).actionSplit.holomorphicAction P
          + (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).actionSplit.antiholomorphicAction P
      ∧ (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).gravity.complexAction =
          (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).gravity.exoticTerm
            + (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).gravity.einsteinHilbertTerm
      ∧ ((@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).parallelReplacement.wheelerDeWittPhysical ψ
          ↔ (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).parallelReplacement.parallelTransportPhysical ψ)
      ∧ (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).torusFactorization.assemble
          ((@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).torusFactorization.leftState Ψ)
          ((@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).torusFactorization.rightState Ψ) = Ψ
      ∧ (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).invariantFactorization.complexInvariant O =
          (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).invariantFactorization.rightInvariant O
            * (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).invariantFactorization.leftInvariant O
      ∧ (@concreteCSWBridge n k c lam ω e Λ hΛ HR HI χ).orthogonality.inner Ψ φ = 0
      ∧ KalnayBoseFermiFieldStatement p)
    ∧ HasHalfFillingCompleteTopologicalOrder

/-- The concrete CSW synthesis now exports the half-filled FQHE complete
topological-order capability under the same explicit CSW item-9 package used by
the FQHE theorem. -/
lemma concreteCSWBridge_satisfies_hayashi_field_and_fqhe_obligations
    {n k : ℕ} (c : HayashiCouplings) (lam ω e : ℂ) (Λ : ℝ) (hΛ : Λ < 0)
    (HR HI : ℝ) (χ : Fin k → ℂ)
    (P : LocalCSConnection n × LocalCSConnection n) (ψ : ℂ)
    (Ψ φ : Fin k × Fin k) (O : Fin k) (p : Momentum 3) (hcharge : Ψ ≠ φ)
    (G : CSWGeometricQuantizationPackage 2 (by norm_num)) :
    HasConcreteCSWFQHEBridge c lam ω e Λ hΛ HR HI χ P ψ Ψ φ O p :=
  ⟨concreteCSWBridge_satisfies_hayashi_and_field_obligations
      c lam ω e Λ hΛ HR HI χ P ψ Ψ φ O p hcharge,
    halfFilling_completeTopologicalOrder_checked G⟩

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity

end
