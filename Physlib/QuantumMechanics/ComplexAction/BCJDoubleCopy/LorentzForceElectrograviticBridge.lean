/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay
public import Physlib.QuantumMechanics.ComplexAction.SpacetimePositiveMass
meta import Zil

/-!
# Lorentz force, BCJ double copy, and the electrogravitic equations

This module closes the typed route from the repository's Lorentz-force numerator to its coupled
Einstein--Maxwell sector.  It composes existing carriers; it does not define a second field strength,
Maxwell stress tensor, Einstein equation, or BCJ amplitude.

* `derive_electrogravitic_field_equation_with_lorentz_bcj` starts from the existing variational
  stationarity data.  It derives the electrogravitic field equation with `T = T[F]`, source-free and
  homogeneous Maxwell equations, the nonnegative diagonal BCJ dual of `F U`, the antisymmetric
  no-work identity, and the electrogravitic complex-action weight represented by the repository's
  genuine denominated BCJ amplitude.
* `lorentzForce_bcj_electrogravitic_bianchi_closure` joins the force channel to both Maxwell Bianchi
  identities and to stress-energy conservation derived from the gravitational second Bianchi.
* `lorentzForce_bcj_electrogravitic_bit_closure` reads the same coupled system at the holographic
  area-per-bit Einstein coupling.
* `potential_lorentzForce_bcj_electrogravitic` supplies the explicit boundary between the smooth
  position-space potential and the momentum-space electrogravitic field.  Its Fourier-identification
  premise is visible in the type rather than silently treating the two representations as definitional.
* `gibbonsWells_lorentz_bcj_electrogravitic` instantiates the force channel with the independently
  derived Kaluza--Klein charge-to-mass ratio and relates its squared numerators to the existing
  operator-level `F²` generator without calling that generator intrinsic Riemann curvature.
* `gibbonsWells_lorentz_bcj_zeno_interval` connects the nonnegative projected-force BCJ channel to the
  existing Mandelstam--Tamm/Zeno bound under an explicit Hamiltonian-variance calibration.

The BCJ force square and the entropic three-channel amplitude are distinct BCJ observables.  This
module proves that the derived electrogravitic solution carries both; it does not identify their
numerators.  Likewise, `faraday k A` is the established momentum-space field-strength carrier.  A
position-space potential may be connected to it only after supplying the appropriate Fourier
identification, while `Lorentz.ForceBCJDual` separately proves the smooth position-space `dA` chain.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.LorentzForceElectrograviticBridge

open Matrix
open Physlib.Thermodynamics
open Physlib.Thermodynamics.GravitationalCouplingSystem
open Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual
open Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.PTTensorDynamics
open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay
open Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator
open Physlib.QuantumMechanics.ComplexAction.SpacetimePositiveMass
open Physlib.QFT.Wick.Consistency

/-! ## A. Variational electrogravitics carries both BCJ faces -/

/-- **Variational Einstein--Maxwell + Lorentz BCJ + entropic BCJ.**  The repository's independent
metric, electromagnetic, and entropic stationarity conditions derive one electrogravitic solution.
For that same `F = faraday k A`, the Lorentz numerator has a nonnegative diagonal double copy and does
no four-velocity work, while the complex-action damping is the existing Jacobi-compliant denominated
BCJ amplitude.  The theorem keeps these two BCJ constructions distinct rather than equating their
model-specific numerators. -/
@[zil_level physical_theorem]
theorem derive_electrogravitic_field_equation_with_lorentz_bcj
    (Ric : FourTensor) (scalarR : ℝ) (g gInv Λ S : FourTensor)
    (κ mR mI c S1 S2 : ℝ) (k A U : Fin 4 → ℝ) (μ : Fin 4)
    (D S_R ℏ : ℝ)
    (hκ : κ ≠ 0) (hInv : AreInverseMetrics g gInv)
    (hmetric : IsElectrograviticMetricStationary Ric scalarR g gInv Λ S κ k A)
    (hbcj : IsBCJEntropicStationary mI c S1 S2)
    (hmaxwell : IsElectromagneticStationary k A) (hD : 0 < D) :
    ElectroGravitationalFieldEquation Ric scalarR g Λ
        (maxwellStressEnergy g gInv (faraday k A)) S
        κ mR mI c S1 S2 k A
      ∧ AreInverseMetrics g gInv
      ∧ (∀ ν, maxwellOp (faraday k A) k ν = 0)
      ∧ (∀ lam μ ν,
          k lam * faraday k A μ ν + k μ * faraday k A ν lam
            + k ν * faraday k A lam μ = 0)
      ∧ 0 ≤ lorentzForceDual (faraday k A) U μ D
      ∧ U ⬝ᵥ ((faraday k A) *ᵥ U) = 0
      ∧ ‖complexActionWeight S_R (complexEinsteinEnergy mR mI c).im ℏ‖ =
          bcjDoubleCopyAmplitude
            (entropicJacobiBCJChannels S1 ℏ)
            (entropicJacobiBCJChannels S2 ℏ) := by
  obtain ⟨H, hInv', hsourceFree, hhomogeneous⟩ :=
    derive_electrogravitic_field_equation Ric scalarR g gInv Λ S
      κ mR mI c S1 S2 k A hκ hInv hmetric hbcj hmaxwell
  exact ⟨H, hInv', hsourceFree, hhomogeneous,
    maxwellLorentzForceDual_nonneg k A U μ D hD,
    faraday_no_work k A U,
    H.pathWeight_eq_jacobiBCJAmplitude S_R ℏ⟩

/-! ## B. Bianchi and conservation closure -/

variable {I : Type*}
variable {Ric : Matrix I I ℝ} {scalarR : ℝ} {g Λ T S : Matrix I I ℝ}
variable {κ mR mI c S1 S2 : ℝ} {k A : Fin 4 → ℝ}

/-- **One field strength, force, gauge conservation, and gravity conservation.**  For an
electrogravitic solution, the same `F = faraday k A` supplies the Lorentz BCJ numerator, the no-work
identity, the Maxwell cyclic identity, and conserved current.  The gravitational second Bianchi plus
the Einstein contraction then derives conservation of the electromagnetic stress tensor. -/
@[zil_level physical_theorem]
theorem lorentzForce_bcj_electrogravitic_bianchi_closure
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (U : Fin 4 → ℝ) (μ : Fin 4) (D : ℝ) (hD : 0 < D)
    (lam α ν : Fin 4) (divG divT : Fin 4 → ℝ)
    (hEinstein : divG = κ • divT) (hSecondBianchi : divG = 0) :
    0 ≤ lorentzForceDual (faraday k A) U μ D
      ∧ U ⬝ᵥ ((faraday k A) *ᵥ U) = 0
      ∧ (k lam * faraday k A α ν + k α * faraday k A ν lam
          + k ν * faraday k A lam α = 0)
      ∧ (∑ i, k i * fourCurrent k A i = 0)
      ∧ divT = 0 := by
  obtain ⟨hclosed, hcurrent, hstress⟩ :=
    electrogravitational_bianchi_double_copy H lam α ν divG divT
      hEinstein hSecondBianchi
  exact ⟨maxwellLorentzForceDual_nonneg k A U μ D hD,
    faraday_no_work k A U, hclosed, hcurrent, hstress⟩

/-! ## C. Holographic area-per-bit coupling -/

/-- **Lorentz/BCJ electrogravitics at the bit-count coupling.**  An electrogravitic solution at
`κ = 8πG/c⁴` simultaneously carries the Lorentz-force double-copy channel, the covariant no-work
identity, Einstein--Maxwell plus the entropic source, the homogeneous Maxwell identity, the entropic
BCJ factorization, and the area-per-bit formula for `κ`.  The bit count is an explicit premise; this
does not promote the screen identity into an independent numerical prediction of `G`. -/
@[zil_level physical_theorem]
theorem lorentzForce_bcj_electrogravitic_bit_closure
    (Ric : Matrix I I ℝ) (scalarR : ℝ) (g Λ T S : Matrix I I ℝ)
    (mR mI c S1 S2 : ℝ) (k A U : Fin 4 → ℝ) (G ℏ N R : ℝ)
    (μ : Fin 4) (D : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S
      (8 * Real.pi * G / c ^ 4) mR mI c S1 S2 k A)
    (hD : 0 < D) :
    0 ≤ lorentzForceDual (faraday k A) U μ D
      ∧ U ⬝ᵥ ((faraday k A) *ᵥ U) = 0
      ∧ (einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4)
          ∧ Λ = (8 * Real.pi * G / c ^ 4) • S)
      ∧ (∀ lam α ν : Fin 4,
          k lam * faraday k A α ν + k α * faraday k A ν lam
            + k ν * faraday k A lam α = 0)
      ∧ Real.exp (-(complexEinsteinEnergy mR mI c).im) =
          Real.exp (-S1) * Real.exp (-S2)
      ∧ 8 * Real.pi * G / c ^ 4 =
          8 * Real.pi * (sphereArea R / N) / (ℏ * c) := by
  obtain ⟨hfield, hclosed, hdoubleCopy, hcoupling⟩ :=
    electrogravitic_equations_bitForm Ric scalarR g Λ T S
      mR mI c S1 S2 k A G ℏ N R hℏ hc hG hR hbits H
  exact ⟨maxwellLorentzForceDual_nonneg k A U μ D hD,
    faraday_no_work k A U, hfield, hclosed, hdoubleCopy, hcoupling⟩

/-! ## D. Explicit position/momentum representation boundary -/

open Electromagnetism
open Electromagnetism.ElectromagneticPotential
open SpaceTime
open minkowskiMatrix

/-- Reindex the smooth position-space field strength from the electromagnetic spacetime carrier
`Fin 1 ⊕ Fin 3` to the electrogravitic momentum carrier `Fin 4`.  This changes only the component
labels; it is not a Fourier transform. -/
noncomputable def potentialFieldStrengthFin4 (V : ElectromagneticPotential 3)
    (x : SpaceTime 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν => V.fieldStrengthMatrix x (finSumFinEquiv.symm μ, finSumFinEquiv.symm ν)

/-- Reindex a covariant four-vector from `Fin 1 ⊕ Fin 3` to `Fin 4`. -/
def covectorFin4 (Ucov : (Fin 1 ⊕ Fin 3) → ℝ) : Fin 4 → ℝ :=
  fun μ => Ucov (finSumFinEquiv.symm μ)

/-- Analytic certificate that a smooth position-space potential has momentum symbol `(k, A)` at
`x`: its raised coordinate derivative in direction `μ` is `k_μ A_ν`.  This is the precise primitive
needed to pass from the real pointwise `dA` representation to the real momentum-symbol convention used
by `faraday k A`; unlike a matrix equality, it exposes the derivative-eigenmode content. -/
def IsRaisedDerivativeMomentumModeAt (V : ElectromagneticPotential 3)
    (x : SpaceTime 3) (k A : Fin 4 → ℝ) : Prop :=
  ∀ μ ν : Fin 1 ⊕ Fin 3,
    η μ μ * SpaceTime.deriv μ V x ν =
      k (finSumFinEquiv μ) * A (finSumFinEquiv ν)

/-- A raised-derivative momentum-mode certificate derives the representation equality previously
supplied as `hFourier`: antisymmetrizing the two certified derivatives gives exactly
`k_μ A_ν - k_ν A_μ`. -/
theorem potentialFieldStrengthFin4_eq_faraday_of_momentumMode
    (V : ElectromagneticPotential 3) (x : SpaceTime 3) (k A : Fin 4 → ℝ)
    (hMode : IsRaisedDerivativeMomentumModeAt V x k A) :
    potentialFieldStrengthFin4 V x = faraday k A := by
  ext μ ν
  unfold potentialFieldStrengthFin4
  rw [toFieldStrength_basis_repr_apply_eq_single]
  simp only [faraday, Matrix.of_apply]
  rw [hMode (finSumFinEquiv.symm μ) (finSumFinEquiv.symm ν),
    hMode (finSumFinEquiv.symm ν) (finSumFinEquiv.symm μ)]
  simp

/-- Reindexing the smooth field strength to `Fin 4` preserves the repository's established gauge
invariance theorem. -/
theorem potentialFieldStrengthFin4_gauge_invariant
    (V : ElectromagneticPotential 3) (χ : SpaceTime 3 → ℝ)
    (hV : Differentiable ℝ V) (hχ : ContDiff ℝ 2 χ) (x : SpaceTime 3) :
    potentialFieldStrengthFin4 (gaugeTransform χ V) x =
      potentialFieldStrengthFin4 V x := by
  ext μ ν
  unfold potentialFieldStrengthFin4
  rw [fieldStrengthMatrix_gaugeTransform V χ hV hχ x]

/-- The Lorentz numerator is invariant under the canonical component reindexing.  Thus the smooth
potential result in `ForceBCJDual` and the `Fin 4` BCJ carrier have the same contraction once their
indices are transported by `finSumFinEquiv`. -/
theorem potentialLorentzForceNumerator_reindex
    (V : ElectromagneticPotential 3) (x : SpaceTime 3)
    (Ucov : (Fin 1 ⊕ Fin 3) → ℝ) (μ : Fin 1 ⊕ Fin 3) :
    lorentzForceNum (potentialFieldStrengthFin4 V x) (covectorFin4 Ucov)
        (finSumFinEquiv μ) =
      potentialLorentzForceNumerator V x Ucov μ := by
  unfold potentialLorentzForceNumerator lorentzForceNum potentialFieldStrengthFin4 covectorFin4
    Matrix.mulVec dotProduct
  rw [← (@finSumFinEquiv 1 3).sum_comp]
  simp

/-- **Smooth potential to BCJ/electrogravitics, with the representation premise exposed.**  If the
reindexed smooth field strength at `x` is the momentum-space `faraday k A` used by an electrogravitic
solution, then its potential-derived Lorentz force is exactly that solution's BCJ force numerator.
Consequently its diagonal gravity-side square is nonnegative, while the same solution satisfies the
Einstein equation sourced by its electromagnetic stress tensor and the entropic curvature equation.

`hFourier` is intentionally explicit: equality between a pointwise field and a Fourier mode is analytic
input, not a consequence of finite component reindexing. -/
@[zil_level physical_theorem]
theorem potential_lorentzForce_bcj_electrogravitic
    (V : ElectromagneticPotential 3) (x : SpaceTime 3)
    (Ucov : (Fin 1 ⊕ Fin 3) → ℝ) (μ : Fin 1 ⊕ Fin 3)
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (hFourier : potentialFieldStrengthFin4 V x = faraday k A)
    (D : ℝ) (hD : 0 < D) :
    potentialLorentzForceNumerator V x Ucov μ ^ 2 / D =
        lorentzForceDual (faraday k A) (covectorFin4 Ucov) (finSumFinEquiv μ) D
      ∧ 0 ≤ lorentzForceDual (faraday k A) (covectorFin4 Ucov) (finSumFinEquiv μ) D
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S := by
  have hnum := potentialLorentzForceNumerator_reindex V x Ucov μ
  rw [hFourier] at hnum
  refine ⟨?_, maxwellLorentzForceDual_nonneg k A (covectorFin4 Ucov)
    (finSumFinEquiv μ) D hD, H.einsteinMaxwell⟩
  unfold lorentzForceDual
  rw [hnum]

/-- **The potential/BCJ/electrogravitic closure from derivative data.**  This is the premise-reduced
form of `potential_lorentzForce_bcj_electrogravitic`: the caller supplies the derivative eigenmode,
and `potentialFieldStrengthFin4_eq_faraday_of_momentumMode` derives the required field-strength
identification. -/
@[zil_level physical_theorem]
theorem potential_lorentzForce_bcj_electrogravitic_of_momentumMode
    (V : ElectromagneticPotential 3) (x : SpaceTime 3)
    (Ucov : (Fin 1 ⊕ Fin 3) → ℝ) (μ : Fin 1 ⊕ Fin 3)
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (hMode : IsRaisedDerivativeMomentumModeAt V x k A)
    (D : ℝ) (hD : 0 < D) :
    potentialLorentzForceNumerator V x Ucov μ ^ 2 / D =
        lorentzForceDual (faraday k A) (covectorFin4 Ucov) (finSumFinEquiv μ) D
      ∧ 0 ≤ lorentzForceDual (faraday k A) (covectorFin4 Ucov) (finSumFinEquiv μ) D
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S :=
  potential_lorentzForce_bcj_electrogravitic V x Ucov μ H
    (potentialFieldStrengthFin4_eq_faraday_of_momentumMode V x k A hMode) D hD

/-- **Gauge-stable potential/BCJ/electrogravitic closure.**  A `C²` gauge shift of the smooth
potential gives the same BCJ force square and the same electrogravitic Einstein--Maxwell endpoint.
The proof consumes the actual smooth gauge-invariance theorem before applying the momentum-mode
bridge; it does not merely assume equality of the two force numerators. -/
@[zil_level physical_theorem]
theorem gaugeTransformed_potential_lorentzForce_bcj_electrogravitic
    (V : ElectromagneticPotential 3) (χ : SpaceTime 3 → ℝ)
    (hV : Differentiable ℝ V) (hχ : ContDiff ℝ 2 χ) (x : SpaceTime 3)
    (Ucov : (Fin 1 ⊕ Fin 3) → ℝ) (μ : Fin 1 ⊕ Fin 3)
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (hMode : IsRaisedDerivativeMomentumModeAt V x k A)
    (D : ℝ) (hD : 0 < D) :
    potentialLorentzForceNumerator (gaugeTransform χ V) x Ucov μ ^ 2 / D =
        lorentzForceDual (faraday k A) (covectorFin4 Ucov) (finSumFinEquiv μ) D
      ∧ 0 ≤ lorentzForceDual (faraday k A) (covectorFin4 Ucov) (finSumFinEquiv μ) D
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S := by
  refine potential_lorentzForce_bcj_electrogravitic
    (gaugeTransform χ V) x Ucov μ H ?_ D hD
  rw [potentialFieldStrengthFin4_gauge_invariant V χ hV hχ x]
  exact potentialFieldStrengthFin4_eq_faraday_of_momentumMode V x k A hMode

/-! ## E. A concrete smooth momentum-symbol potential -/

/-- The continuous linear Minkowski-raised momentum phase
`x ↦ Σ_μ η_μμ k^μ x^μ`.  Its coordinate derivative in direction `μ` is
`η_μμ k^μ`, so raising that derivative once more returns `k^μ`. -/
noncomputable def raisedMomentumPhaseCLM (k : Fin 4 → ℝ) : SpaceTime 3 →L[ℝ] ℝ :=
  ∑ μ : Fin 1 ⊕ Fin 3,
    (η μ μ * k (finSumFinEquiv μ)) • SpaceTime.coordCLM μ

/-- The `Fin 4` momentum amplitude represented in the electromagnetic spacetime carrier. -/
def momentumAmplitudeVector (A : Fin 4 → ℝ) : Lorentz.Vector 3 :=
  fun ν => A (finSumFinEquiv ν)

/-- The rank-one continuous linear map whose value is the raised momentum phase times the fixed
four-potential amplitude. -/
noncomputable def affineMomentumPotentialCLM (k A : Fin 4 → ℝ) :
    SpaceTime 3 →L[ℝ] Lorentz.Vector 3 :=
  (raisedMomentumPhaseCLM k).smulRight (momentumAmplitudeVector A)

/-- Scalar component of `affineMomentumPotentialCLM`, retained as a bundled continuous linear map so
its Fréchet derivative is consumed directly. -/
noncomputable def affineMomentumPotentialComponentCLM (k A : Fin 4 → ℝ)
    (ν : Fin 1 ⊕ Fin 3) : SpaceTime 3 →L[ℝ] ℝ :=
  (Lorentz.Vector.coordCLM ν).comp (affineMomentumPotentialCLM k A)

/-- A concrete smooth real potential realizing the momentum symbol `(k, A)`.  It is affine-linear in
the spacetime coordinates and therefore produces the constant field strength `k ∧ A`. -/
noncomputable def affineMomentumPotential (k A : Fin 4 → ℝ) :
    ElectromagneticPotential 3 :=
  ⟨affineMomentumPotentialCLM k A⟩

/-- Evaluation of the raised momentum phase on the coordinate basis. -/
theorem raisedMomentumPhaseCLM_basis (k : Fin 4 → ℝ) (μ : Fin 1 ⊕ Fin 3) :
    raisedMomentumPhaseCLM k (Lorentz.Vector.basis μ) =
      η μ μ * k (finSumFinEquiv μ) := by
  rcases μ with μ | μ
  · fin_cases μ
    simp [raisedMomentumPhaseCLM, SpaceTime.coordCLM, Lorentz.Vector.basis_apply]
  · fin_cases μ <;>
      simp [raisedMomentumPhaseCLM, SpaceTime.coordCLM, Lorentz.Vector.basis_apply]

/-- The concrete potential has the required coordinate derivative exactly. -/
theorem affineMomentumPotential_deriv (k A : Fin 4 → ℝ)
    (x : SpaceTime 3) (μ ν : Fin 1 ⊕ Fin 3) :
    SpaceTime.deriv μ (affineMomentumPotential k A) x ν =
      (η μ μ * k (finSumFinEquiv μ)) * A (finSumFinEquiv ν) := by
  unfold SpaceTime.deriv
  rw [Lorentz.Vector.fderiv_apply]
  change (fderiv ℝ (affineMomentumPotentialComponentCLM k A ν) x)
      (Lorentz.Vector.basis μ) = _
  rw [ContinuousLinearMap.fderiv]
  change raisedMomentumPhaseCLM k (Lorentz.Vector.basis μ) *
      A (finSumFinEquiv ν) = _
  rw [raisedMomentumPhaseCLM_basis]
  exact (affineMomentumPotentialCLM k A).differentiable

/-- The concrete potential satisfies the raised-derivative momentum-mode certificate at every point.
The proof is the signature identity `η_μμ² = 1`. -/
theorem affineMomentumPotential_isMode (k A : Fin 4 → ℝ) (x : SpaceTime 3) :
    IsRaisedDerivativeMomentumModeAt (affineMomentumPotential k A) x k A := by
  intro μ ν
  rw [affineMomentumPotential_deriv]
  rcases μ with μ | μ
  · fin_cases μ
    simp [minkowskiMatrix.inl_0_inl_0]
  · simp [minkowskiMatrix.inr_i_inr_i]

/-- The concrete momentum-symbol potential is smooth to every finite or infinite order. -/
theorem affineMomentumPotential_contDiff (k A : Fin 4 → ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (affineMomentumPotential k A) :=
  (affineMomentumPotentialCLM k A).contDiff

/-- The smooth concrete potential produces exactly the electrogravitic momentum-space Faraday tensor. -/
theorem affineMomentumPotential_fieldStrength (k A : Fin 4 → ℝ) (x : SpaceTime 3) :
    potentialFieldStrengthFin4 (affineMomentumPotential k A) x = faraday k A :=
  potentialFieldStrengthFin4_eq_faraday_of_momentumMode
    (affineMomentumPotential k A) x k A (affineMomentumPotential_isMode k A x)

/-- **Concrete smooth potential → Lorentz force → BCJ → electrogravitics.**  For the explicit
smooth potential above, no representation-identification or momentum-mode premise remains: its
derivative theorem constructs `faraday k A`, its Lorentz numerator feeds the nonnegative BCJ square,
and the supplied electrogravitic solution supplies the Einstein--Maxwell and entropic endpoints. -/
@[zil_level physical_theorem]
theorem affineMomentumPotential_bcj_electrogravitic
    (x : SpaceTime 3) (Ucov : (Fin 1 ⊕ Fin 3) → ℝ) (μ : Fin 1 ⊕ Fin 3)
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (D : ℝ) (hD : 0 < D) :
    potentialLorentzForceNumerator (affineMomentumPotential k A) x Ucov μ ^ 2 / D =
        lorentzForceDual (faraday k A) (covectorFin4 Ucov) (finSumFinEquiv μ) D
      ∧ 0 ≤ lorentzForceDual (faraday k A) (covectorFin4 Ucov) (finSumFinEquiv μ) D
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S :=
  potential_lorentzForce_bcj_electrogravitic_of_momentumMode
    (affineMomentumPotential k A) x Ucov μ H
    (affineMomentumPotential_isMode k A x) D hD

/-! ## F. Kaluza--Klein and operator-level analogues -/

/-- **Gibbons--Wells projected Lorentz force → BCJ → Einstein--Maxwell.**  On the same Faraday tensor
carried by an electrogravitic solution, the five-to-four-dimensional projection derives the force
coefficient `q/m = s κ₅`; its diagonal BCJ dual is `(s κ₅)²` times the bare Lorentz dual, remains
nonnegative, and its summed squared numerators equal the quadratic form of the existing operator `F²`.

The final two conjuncts are the real and entropic sectors of the supplied electrogravitic solution.
The `F²` operator is an algebraic double-copy generator; this theorem does not identify it with the
intrinsic Riemann tensor of `g`. -/
@[zil_level physical_theorem]
theorem gibbonsWells_lorentz_bcj_electrogravitic
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (V : Fin 4 → ℝ) (mu : Fin 4) (s e κ5 D : ℝ)
    (he : e ≠ 0) (hκ5 : κ5 ≠ 0) (hD : 0 < D) :
    gibbonsWellsProbeLorentzForce (faraday k A) V s e κ5 =
        (s * κ5) • ((faraday k A) *ᵥ V)
      ∧ gibbonsWellsProbeLorentzForceDual (faraday k A) V mu s e κ5 D =
        (s * κ5) ^ 2 * lorentzForceDual (faraday k A) V mu D
      ∧ 0 ≤ gibbonsWellsProbeLorentzForceDual (faraday k A) V mu s e κ5 D
      ∧ (∑ rho, gibbonsWellsProbeLorentzForceNum (faraday k A) V rho s e κ5 ^ 2) =
        -(s * κ5) ^ 2 * (V ⬝ᵥ gravCurvatureGen (faraday k A) V)
      ∧ V ⬝ᵥ gibbonsWellsProbeLorentzForce (faraday k A) V s e κ5 = 0
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S := by
  exact ⟨gibbonsWellsProbeLorentzForce_eq (faraday k A) V s e κ5 he hκ5,
    gibbonsWellsProbeLorentzForceDual_eq (faraday k A) V mu s e κ5 D he hκ5,
    gibbonsWellsProbeLorentzForceDual_nonneg (faraday k A) V mu s e κ5 D he hκ5 hD,
    gibbonsWellsProbeLorentzForceNum_sq_sum_eq_curvature
      (faraday k A) (faraday_antisymm k A) V s e κ5 he hκ5,
    gibbonsWellsProbeLorentzForce_no_work
      (faraday k A) (faraday_antisymm k A) V s e κ5 he hκ5,
    H.einsteinMaxwell.1, H.einsteinMaxwell.2⟩

/-- **Projected-force Bianchi closure.**  The Gibbons--Wells force on the electrogravitic Faraday
tensor has a nonnegative BCJ dual and performs no work, while the same field obeys the Maxwell cyclic
identity and current conservation and the gravitational second Bianchi discharges stress conservation.
The last conclusion still requires the displayed Einstein-contraction and second-Bianchi premises. -/
@[zil_level physical_theorem]
theorem gibbonsWells_lorentz_bcj_electrogravitic_bianchi_closure
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (V : Fin 4 → ℝ) (mu : Fin 4) (s e κ5 D : ℝ)
    (he : e ≠ 0) (hκ5 : κ5 ≠ 0) (hD : 0 < D)
    (lam α ν : Fin 4) (divG divT : Fin 4 → ℝ)
    (hEinstein : divG = κ • divT) (hSecondBianchi : divG = 0) :
    0 ≤ gibbonsWellsProbeLorentzForceDual (faraday k A) V mu s e κ5 D
      ∧ V ⬝ᵥ gibbonsWellsProbeLorentzForce (faraday k A) V s e κ5 = 0
      ∧ (k lam * faraday k A α ν + k α * faraday k A ν lam
          + k ν * faraday k A lam α = 0)
      ∧ (∑ i, k i * fourCurrent k A i = 0)
      ∧ divT = 0 := by
  obtain ⟨hclosed, hcurrent, hstress⟩ :=
    electrogravitational_bianchi_double_copy H lam α ν divG divT
      hEinstein hSecondBianchi
  exact ⟨gibbonsWellsProbeLorentzForceDual_nonneg
      (faraday k A) V mu s e κ5 D he hκ5 hD,
    gibbonsWellsProbeLorentzForce_no_work
      (faraday k A) (faraday_antisymm k A) V s e κ5 he hκ5,
    hclosed, hcurrent, hstress⟩

/-- **Operator double copy on an Einstein--Maxwell field.**  The gauge generator `V ↦ F V`
composes with itself to the algebraic `F²` generator, whose quadratic form is minus the sum of squared
Lorentz-force numerators.  The same supplied electrogravitic carrier satisfies Einstein--Maxwell.

This is the precise operator-level statement available in the repository: it deliberately does not
equate `F²` with the chartwise or intrinsic Riemann curvature tensor. -/
@[zil_level bridge_theorem]
theorem lorentzForce_operatorDoubleCopy_electrogravitic
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (V : Fin 4 → ℝ) :
    gravCurvatureGen (faraday k A) =
        (lorentzGen (faraday k A)).comp (lorentzGen (faraday k A))
      ∧ V ⬝ᵥ gravCurvatureGen (faraday k A) V =
        -(∑ mu, lorentzForceNum (faraday k A) V mu ^ 2)
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S :=
  ⟨gravCurvatureGen_eq_comp (faraday k A),
    gravCurvatureGen_quadratic_lorentz (faraday k A) (faraday_antisymm k A) V,
    H.einsteinMaxwell.1, H.einsteinMaxwell.2⟩

/-! ## G. Calibrated quantum-Zeno read -/

/-- **Projected-force BCJ channel → quantum-Zeno interval bound.**  If the Hamiltonian energy variance
of the monitored mode is calibrated by
`ΔE² = gibbonsWellsProbeLorentzForceDual`, then the existing Mandelstam--Tamm short-time theorem gives

`1 - gibbonsWellsProbeLorentzForceDual · (t/(Nℏ))² ≤ Q(t/N)`.

The projected dual is independently nonnegative for positive propagator denominator, and the same
carrier satisfies Einstein--Maxwell.  The calibration premise is load-bearing: BCJ kinematics alone does
not determine the energy variance of a laboratory measurement Hamiltonian. -/
@[zil_level physical_theorem]
theorem gibbonsWells_lorentz_bcj_zeno_interval
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (V : Fin 4 → ℝ) (mu : Fin 4) (s e κ5 D ΔE ℏ t N : ℝ)
    (he : e ≠ 0) (hκ5 : κ5 ≠ 0) (hD : 0 < D)
    (hspread : ΔE ^ 2 =
      gibbonsWellsProbeLorentzForceDual (faraday k A) V mu s e κ5 D) :
    0 ≤ gibbonsWellsProbeLorentzForceDual (faraday k A) V mu s e κ5 D
      ∧ 1 - gibbonsWellsProbeLorentzForceDual (faraday k A) V mu s e κ5 D *
          (t / (N * ℏ)) ^ 2 ≤ mandelstamTammSurvival ΔE ℏ (t / N)
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S := by
  have hscale : (ΔE * t / (N * ℏ)) ^ 2 =
      gibbonsWellsProbeLorentzForceDual (faraday k A) V mu s e κ5 D *
        (t / (N * ℏ)) ^ 2 := by
    rw [div_pow, mul_pow, hspread, div_pow]
    ring
  have hzeno := zeno_interval_survival ΔE ℏ t N
  rw [hscale] at hzeno
  exact ⟨gibbonsWellsProbeLorentzForceDual_nonneg
      (faraday k A) V mu s e κ5 D he hκ5 hD,
    hzeno, H.einsteinMaxwell.1, H.einsteinMaxwell.2⟩

/-- **Operator-double-copy form of the Zeno bound.**  When the energy variance is calibrated by the
summed squared Lorentz numerators, the exact operator identity
`-V · F²V = Σμ (FV)μ²` turns the repeated-measurement bound into

`1 - (-V · F²V) · (t/(Nℏ))² ≤ Q(t/N)`.

This is an equality-guided specialization of the established Zeno theorem, not a claim that the
algebraic `F²` generator is an intrinsic curvature tensor or that Einstein--Maxwell fixes `ΔE`. -/
@[zil_level bridge_theorem]
theorem lorentzForce_operatorDoubleCopy_zeno_interval
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (V : Fin 4 → ℝ) (ΔE ℏ t N : ℝ)
    (hspread : ΔE ^ 2 = ∑ mu, lorentzForceNum (faraday k A) V mu ^ 2) :
    0 ≤ -(V ⬝ᵥ gravCurvatureGen (faraday k A) V)
      ∧ 1 - (-(V ⬝ᵥ gravCurvatureGen (faraday k A) V)) *
          (t / (N * ℏ)) ^ 2 ≤ mandelstamTammSurvival ΔE ℏ (t / N)
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S := by
  have hquad := gravCurvatureGen_quadratic_lorentz
    (faraday k A) (faraday_antisymm k A) V
  have hcurv : ΔE ^ 2 = -(V ⬝ᵥ gravCurvatureGen (faraday k A) V) := by
    rw [hquad]
    simpa using hspread
  have hscale : (ΔE * t / (N * ℏ)) ^ 2 =
      (-(V ⬝ᵥ gravCurvatureGen (faraday k A) V)) * (t / (N * ℏ)) ^ 2 := by
    rw [div_pow, mul_pow, hcurv, div_pow]
    ring
  have hzeno := zeno_interval_survival ΔE ℏ t N
  rw [hscale] at hzeno
  refine ⟨?_, hzeno, H.einsteinMaxwell.1, H.einsteinMaxwell.2⟩
  rw [hquad, neg_neg]
  exact Finset.sum_nonneg fun mu _ =>
    sq_nonneg (lorentzForceNum (faraday k A) V mu)

/-- **Gibbons--Wells/BCJ calibrated quantum-Zeno freeze.**  Under the same explicit energy-variance
calibration as `gibbonsWells_lorentz_bcj_zeno_interval`, the *full ideal repeated survival*

`(Q(t/n))ⁿ → 1`

follows from `mandelstamTamm_repeated_survival_tendsto_one`.  Nonnegativity of the calibrated BCJ
channel and the Einstein--Maxwell endpoint are carried alongside the limit. -/
@[zil_level physical_theorem]
theorem gibbonsWells_lorentz_bcj_zeno_freeze
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (V : Fin 4 → ℝ) (mu : Fin 4) (s e κ5 D ΔE ℏ t : ℝ)
    (he : e ≠ 0) (hκ5 : κ5 ≠ 0) (hD : 0 < D)
    (hspread : ΔE ^ 2 =
      gibbonsWellsProbeLorentzForceDual (faraday k A) V mu s e κ5 D) :
    0 ≤ gibbonsWellsProbeLorentzForceDual (faraday k A) V mu s e κ5 D
      ∧ ΔE ^ 2 = gibbonsWellsProbeLorentzForceDual (faraday k A) V mu s e κ5 D
      ∧ Filter.Tendsto
          (fun n : ℕ => mandelstamTammSurvival ΔE ℏ (t / n) ^ n)
          Filter.atTop (nhds 1)
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S :=
  ⟨gibbonsWellsProbeLorentzForceDual_nonneg
      (faraday k A) V mu s e κ5 D he hκ5 hD,
    hspread, mandelstamTamm_repeated_survival_tendsto_one ΔE ℏ t,
    H.einsteinMaxwell.1, H.einsteinMaxwell.2⟩

/-- **Operator-double-copy quantum-Zeno freeze.**  If `ΔE²` is the summed Lorentz-force numerator
square, then it is exactly the nonnegative quadratic coefficient `-V · F²V`; the corresponding ideal
repeated Mandelstam--Tamm survival tends to one.  The result remains a calibrated monitored-mode
statement, not a derivation of `ΔE` from Einstein--Maxwell. -/
@[zil_level bridge_theorem]
theorem lorentzForce_operatorDoubleCopy_zeno_freeze
    (H : ElectroGravitationalFieldEquation Ric scalarR g Λ T S κ mR mI c S1 S2 k A)
    (V : Fin 4 → ℝ) (ΔE ℏ t : ℝ)
    (hspread : ΔE ^ 2 = ∑ mu, lorentzForceNum (faraday k A) V mu ^ 2) :
    0 ≤ -(V ⬝ᵥ gravCurvatureGen (faraday k A) V)
      ∧ ΔE ^ 2 = -(V ⬝ᵥ gravCurvatureGen (faraday k A) V)
      ∧ Filter.Tendsto
          (fun n : ℕ => mandelstamTammSurvival ΔE ℏ (t / n) ^ n)
          Filter.atTop (nhds 1)
      ∧ einsteinFieldEquation Ric scalarR g T κ
      ∧ Λ = κ • S := by
  have hquad := gravCurvatureGen_quadratic_lorentz
    (faraday k A) (faraday_antisymm k A) V
  have hcurv : ΔE ^ 2 = -(V ⬝ᵥ gravCurvatureGen (faraday k A) V) := by
    rw [hquad]
    simpa using hspread
  refine ⟨?_, hcurv, mandelstamTamm_repeated_survival_tendsto_one ΔE ℏ t,
    H.einsteinMaxwell.1, H.einsteinMaxwell.2⟩
  rw [hquad, neg_neg]
  exact Finset.sum_nonneg fun mu _ =>
    sq_nonneg (lorentzForceNum (faraday k A) V mu)

/- ZIL-BEGIN -/

zil attach derive_electrogravitic_field_equation_with_lorentz_bcj where
  formalizes @ "claim:variational-electrogravitics-carries-the-lorentz-force-bcj-square-and-the-entropic-jacobi-bcj-amplitude",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_electrogravitic_field_equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual.maxwellLorentzForceDual_nonneg",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation.pathWeight_eq_jacobiBCJAmplitude",
  requires @ "claim:metric-electromagnetic-and-entropic-stationarity-plus-positive-force-channel-propagator",
  caveat @ "claim:the-lorentz-diagonal-square-and-entropic-three-channel-amplitude-are-both-carried-but-their-numerators-are-not-identified"

zil attach lorentzForce_bcj_electrogravitic_bianchi_closure where
  formalizes @ "claim:one-maxwell-field-strength-carries-the-lorentz-bcj-channel-current-conservation-and-stress-energy-conservation-from-gravity-second-bianchi",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Vlasov.MaxwellEM.faraday_no_work",
  requires @ "claim:einstein-contracted-stress-divergence-and-gravitational-second-bianchi",
  caveat @ "claim:conservation-closure-for-a-supplied-electrogravitic-solution-not-an-existence-theorem"

zil attach lorentzForce_bcj_electrogravitic_bit_closure where
  formalizes @ "claim:the-lorentz-bcj-and-electrogravitic-equations-share-the-holographic-area-per-bit-einstein-coupling",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_equations_bitForm",
  requires @ "claim:the-explicit-holographic-bit-count-identification-and-nonzero-physical-scales",
  caveat @ "claim:conditional-screen-coupling-identity-not-an-independent-numerical-prediction-of-newton-g"

zil attach potential_lorentzForce_bcj_electrogravitic where
  formalizes @ "claim:the-smooth-potential-derived-lorentz-force-is-the-bcj-force-numerator-of-the-electrogravitic-solution-after-an-explicit-position-momentum-identification",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual.potentialLorentzForceNumerator_apply_eq_derivatives",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.ElectroGravitationalFieldEquation.einsteinMaxwell",
  requires @ "claim:the-reindexed-pointwise-field-strength-equals-the-selected-momentum-space-faraday-mode-and-the-bcj-denominator-is-positive",
  caveat @ "claim:the-fourier-identification-is-an-explicit-analytic-premise-not-derived-by-component-reindexing"

zil attach potentialFieldStrengthFin4_eq_faraday_of_momentumMode where
  formalizes @ "claim:a-raised-derivative-momentum-eigenmode-derives-the-momentum-space-faraday-tensor-from-the-smooth-potential",
  supported_by @ "lean:Electromagnetism.ElectromagneticPotential.toFieldStrength_basis_repr_apply_eq_single",
  requires @ "claim:the-pointwise-raised-derivative-mode-equations",
  caveat @ "claim:local-mode-symbol-identity-not-a-global-fourier-inversion-or-plancherel-theorem"

zil attach potential_lorentzForce_bcj_electrogravitic_of_momentumMode where
  formalizes @ "claim:the-raised-derivative-momentum-mode-connects-the-smooth-lorentz-force-to-the-bcj-and-electrogravitic-einstein-maxwell-endpoint",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.LorentzForceElectrograviticBridge.potentialFieldStrengthFin4_eq_faraday_of_momentumMode",
  requires @ "claim:an-electrogravitic-solution-and-positive-bcj-denominator",
  caveat @ "claim:pointwise-symbol-bridge-not-a-global-wave-packet-existence-theorem"

zil attach gaugeTransformed_potential_lorentzForce_bcj_electrogravitic where
  formalizes @ "claim:the-smooth-potential-to-bcj-to-electrogravitic-closure-is-invariant-under-c2-gauge-transformations",
  supported_by @ "lean:Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix_gaugeTransform",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.LorentzForceElectrograviticBridge.potential_lorentzForce_bcj_electrogravitic_of_momentumMode",
  caveat @ "claim:gauge-stability-of-the-equation-level-bridge-not-gauge-fixed-global-pde-well-posedness"

zil attach affineMomentumPotential_deriv where
  formalizes @ "claim:an-explicit-smooth-real-four-potential-has-the-raised-momentum-symbol-derivative",
  supported_by @ "lean:SpaceTime.coordCLM",
  supported_by @ "lean:Lorentz.Vector.fderiv_apply",
  caveat @ "claim:affine-constant-field-witness-not-a-normalizable-radiative-wave-packet"

zil attach affineMomentumPotential_fieldStrength where
  formalizes @ "claim:the-explicit-smooth-affine-potential-derives-the-electrogravitic-momentum-space-faraday-tensor",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.LorentzForceElectrograviticBridge.affineMomentumPotential_isMode",
  caveat @ "claim:constant-field-strength-realization-not-a-global-fourier-inversion-theorem"

zil attach affineMomentumPotential_bcj_electrogravitic where
  formalizes @ "claim:an-explicit-smooth-potential-derives-the-lorentz-bcj-force-channel-and-connects-it-to-the-electrogravitic-einstein-maxwell-equation",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.LorentzForceElectrograviticBridge.affineMomentumPotential_fieldStrength",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.LorentzForceElectrograviticBridge.potential_lorentzForce_bcj_electrogravitic_of_momentumMode",
  requires @ "claim:a-supplied-electrogravitic-solution-and-positive-bcj-propagator-denominator",
  caveat @ "claim:explicit-equation-level-smooth-witness-not-a-finite-energy-global-coupled-pde-solution"

zil attach gibbonsWells_lorentz_bcj_electrogravitic where
  formalizes @ "claim:the-kaluza-klein-projected-lorentz-force-has-a-coupling-scaled-bcj-double-copy-on-the-electrogravitic-einstein-maxwell-field",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SpacetimePositiveMass.gibbonsWellsProbeLorentzForceDual_eq",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SpacetimePositiveMass.gibbonsWellsProbeLorentzForceNum_sq_sum_eq_curvature",
  requires @ "claim:a-supplied-electrogravitic-solution-nonzero-probe-scales-and-positive-bcj-denominator",
  caveat @ "claim:the-f-squared-operator-is-an-algebraic-double-copy-generator-not-the-intrinsic-riemann-tensor"

zil attach gibbonsWells_lorentz_bcj_electrogravitic_bianchi_closure where
  formalizes @ "claim:the-kaluza-klein-projected-lorentz-force-shares-the-electrogravitic-maxwell-and-gravity-bianchi-conservation-closure",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy",
  requires @ "claim:einstein-contracted-stress-divergence-and-gravitational-second-bianchi",
  caveat @ "claim:conservation-for-a-supplied-electrogravitic-solution-not-a-five-dimensional-global-existence-theorem"

zil attach lorentzForce_operatorDoubleCopy_electrogravitic where
  formalizes @ "claim:on-an-einstein-maxwell-field-the-f-squared-operator-is-the-composite-of-two-lorentz-generators-and-its-quadratic-form-is-minus-the-summed-force-numerator-squares",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator.gravCurvatureGen_eq_comp",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator.gravCurvatureGen_quadratic_lorentz",
  caveat @ "claim:operator-double-copy-identity-not-an-identification-with-intrinsic-spacetime-curvature"

zil attach gibbonsWells_lorentz_bcj_zeno_interval where
  formalizes @ "claim:a-kaluza-klein-projected-lorentz-bcj-mode-obeys-the-mandelstam-tamm-quantum-zeno-interval-bound-when-its-energy-variance-is-explicitly-calibrated-by-the-bcj-dual",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.zeno_interval_survival",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.SpacetimePositiveMass.gibbonsWellsProbeLorentzForceDual_nonneg",
  requires @ "claim:delta-e-squared-equals-the-projected-force-bcj-dual-for-the-selected-measurement-hamiltonian",
  caveat @ "claim:bcj-kinematics-does-not-by-itself-derive-the-physical-hamiltonian-energy-variance"

zil attach lorentzForce_operatorDoubleCopy_zeno_interval where
  formalizes @ "claim:the-quantum-zeno-short-time-bound-can-be-written-with-minus-v-dot-f-squared-v-using-the-summed-lorentz-force-numerator-square",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator.gravCurvatureGen_quadratic_lorentz",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.zeno_interval_survival",
  requires @ "claim:delta-e-squared-equals-the-sum-of-squared-lorentz-force-numerators-for-the-monitored-mode",
  caveat @ "claim:calibrated-zeno-bound-not-an-identification-of-f-squared-with-riemann-curvature-or-a-derivation-of-delta-e-from-einstein-maxwell"

zil attach gibbonsWells_lorentz_bcj_zeno_freeze where
  formalizes @ "claim:a-calibrated-kaluza-klein-lorentz-bcj-mode-has-n-fold-ideal-mandelstam-tamm-survival-tending-to-one-the-full-quantum-zeno-freeze",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.mandelstamTamm_repeated_survival_tendsto_one",
  requires @ "claim:delta-e-squared-equals-the-projected-force-bcj-dual-for-the-selected-measurement-hamiltonian",
  caveat @ "claim:ideal-factorized-projection-limit-not-a-detector-backreaction-or-unbounded-operator-product-formula"

zil attach lorentzForce_operatorDoubleCopy_zeno_freeze where
  formalizes @ "claim:after-energy-variance-calibration-the-operator-double-copy-coefficient-minus-v-dot-f-squared-v-governs-an-ideal-repeated-survival-that-tends-to-one",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator.gravCurvatureGen_quadratic_lorentz",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.mandelstamTamm_repeated_survival_tendsto_one",
  requires @ "claim:delta-e-squared-equals-the-summed-lorentz-force-numerator-square-for-the-monitored-mode",
  caveat @ "claim:does-not-identify-f-squared-with-intrinsic-curvature-or-derive-the-energy-variance-from-einstein-maxwell"

zil_file_contract physlib.lorentzForceElectrograviticBridge where
  promises "The repository's variational Einstein-Maxwell solution carries the Lorentz-force BCJ numerator of its momentum-space field strength, the nonnegative diagonal gravity-side square, both Maxwell Bianchi conservation statements, gravity-side stress-energy conservation, the entropic denominated BCJ amplitude, and the holographic area-per-bit coupling. An explicit position-momentum identification connects this carrier to the smooth potential-derived force."
  at_level physical_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual.maxwellLorentzForceDual_nonneg",
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.ForceBCJDual.potentialLorentzForceNumerator_apply_eq_derivatives",
    "lean:Electromagnetism.ElectromagneticPotential.fieldStrengthMatrix_gaugeTransform",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ElectroGravitationalFieldEquations.derive_electrogravitic_field_equation",
    "lean:Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ElectroGravitationalBianchiDoubleCopy.electrogravitational_bianchi_double_copy",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.ElectroGravitationalBitForm.electrogravitic_equations_bitForm",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropyProductionDecay.zeno_interval_survival",
    "lean:Physlib.QuantumMechanics.ComplexAction.SpacetimePositiveMass.gibbonsWellsProbeLorentzForceDual_eq",
    "lean:Physlib.QuantumMechanics.ComplexAction.Lorentz.GravityDoubleCopySuperoperator.gravCurvatureGen_quadratic_lorentz"
  ]
  forbids_substitutes [
    "introducing a second Maxwell field-strength or stress-energy definition",
    "identifying the Lorentz-force numerator with the entropic Jacobi numerator without a calibration theorem",
    "identifying position-space and momentum-space potentials without an explicit Fourier bridge",
    "calling the area-per-bit identity an independent measurement-free prediction of G",
    "identifying the algebraic F-squared generator with intrinsic Riemann curvature"
  ]
  witnessed_by [
    derive_electrogravitic_field_equation_with_lorentz_bcj,
    lorentzForce_bcj_electrogravitic_bianchi_closure,
    lorentzForce_bcj_electrogravitic_bit_closure,
    potentialLorentzForceNumerator_reindex,
    potential_lorentzForce_bcj_electrogravitic,
    potentialFieldStrengthFin4_eq_faraday_of_momentumMode,
    potentialFieldStrengthFin4_gauge_invariant,
    potential_lorentzForce_bcj_electrogravitic_of_momentumMode,
    gaugeTransformed_potential_lorentzForce_bcj_electrogravitic,
    raisedMomentumPhaseCLM_basis,
    affineMomentumPotential_deriv,
    affineMomentumPotential_isMode,
    affineMomentumPotential_contDiff,
    affineMomentumPotential_fieldStrength,
    affineMomentumPotential_bcj_electrogravitic,
    gibbonsWells_lorentz_bcj_electrogravitic,
    gibbonsWells_lorentz_bcj_electrogravitic_bianchi_closure,
    lorentzForce_operatorDoubleCopy_electrogravitic,
    gibbonsWells_lorentz_bcj_zeno_interval,
    lorentzForce_operatorDoubleCopy_zeno_interval,
    gibbonsWells_lorentz_bcj_zeno_freeze,
    lorentzForce_operatorDoubleCopy_zeno_freeze
  ]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.LorentzForceElectrograviticBridge

end
